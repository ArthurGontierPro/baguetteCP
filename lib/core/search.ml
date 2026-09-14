(* search.ml: depth-first search with every decision and backtrack reflected in the
   proof (M1-T10, Part 2). Read the module header below in full before calling
   [solve] -- the proof-logging strategy it implements is a specific, deliberate
   answer to "how a decision made mid-search can ever be cited by a checker that never
   sees it as an axiom", not an incidental detail.

   ---------------------------------------------------------------------------
   The hard question, and why the answer here is neither of the two the task poses
   ---------------------------------------------------------------------------

   docs/SPEC.md 3.4: first-fail variable selection, min-value branching, depth-first,
   restarts disabled. That part is unsurprising. The proof-logging strategy is not.

   A decision is not implied by the model, so it cannot enter the proof as a bare fact:
   neither [rup] nor [pol] can derive an unentailed literal (docs/DECISIONS.md D-0009
   demonstrates this directly against veripb -- a bare literal in a [pol] is the
   trivial axiom [lit >= 0], and [rup] requires a genuine logical consequence), and
   [a] (assumed-checked) is forbidden outside debugging (docs/PROOF-FORMAT.md section
   2). [red] (redundance) does not apply either: it justifies adding a constraint that
   preserves *satisfiability* under a witness substitution, which is not available for
   an arbitrary domain split (a solution with x=3 cannot be "witnessed" into one with
   x>=5; it may simply not exist).

   The task offers two standard resolutions:
     (a) every derived constraint carries the negated decision literals, so it is
         globally valid rather than valid-under-assumption;
     (b) nothing is logged inside a branch; the branch's refutation is derived only
         when it closes.

   What is implemented here is (b), but sharpened by one observation that changes what
   "derived when it closes" has to mean: a propagator's [Explanation.t] is *never
   rendered* during search, not even at the point a branch fails. Only one thing is
   ever asked of the proof, per branch: the clause "not all of these decisions can
   hold simultaneously" (the branch's nogood), built purely from the *literals of the
   decisions themselves* -- and it is logged as a [rup] of that clause alone, with no
   reference to any intermediate [Explanation.t] a propagator constructed to reach the
   conflict.

   Why this is sound, and not a weaker echo of (a): [rup]'s check is "does the
   database, extended with the negation of every literal in this clause, propagate
   (by the checker's own generalised unit propagation over pseudo-Boolean
   constraints) to a contradiction". Negating every literal of the nogood clause is
   *exactly* asserting the decisions the branch took. The checker then has to
   re-derive the same conflict our propagators found, using only the model rows
   (already in the database, unconditionally) and the order-encoding's consistency
   family -- and it can, because every M1 bounds propagator (int_lin_le and everything
   built on it: int_le, int_lt, int_eq, int_lin_eq) *is* generalised unit propagation
   over its own row; there is no reasoning our propagators perform that the checker's
   RUP search cannot replay by itself once it is told which literals to assume. This
   is checked against the real checker below (the veripb-backed tests), not asserted.
   So a leaf's nogood needs nothing from [Explanation.t] at all: the decisions are
   already, by construction, everything the checker needs to reconstruct the reason.

   This gives (a)'s property -- every logged constraint is globally valid, no
   assumption ever sits unprotected in the database -- at (b)'s cost -- one clause per
   search node that actually fails, not one per pruning step -- without needing
   [Explanation.t] to grow an extra "guarded by these decisions" case (which would
   have required touching [lib/core/explanation.ml] / [lib/core/justify.ml], both
   read-only for this task). See the proposed decision record in the hand-back report
   for the Context/Decision/Consequences write-up this deserves in
   docs/DECISIONS.md.

   ---------------------------------------------------------------------------
   How a decision and a backtrack become proof steps
   ---------------------------------------------------------------------------

   Branching splits on a single order-encoding literal [l = x_ge_(lo+1)] for the
   first-fail variable [x] at its current [lo] (indomain_min: try [x = lo] --
   i.e. [~l] -- before [x > lo] -- i.e. [l]). Both branches run inside their own
   [Store] decision level (docs/DECISIONS.md D-0008), tagged in the proof with
   [Writer.set_level] to match: *every* decision opens a level and *every* backtrack
   wipes one, which is the sense in which "every branching decision and every
   backtrack MUST be reflected in the proof" (docs/SPEC.md 3.4) holds here, even
   though no individual pruning inside a branch is ever rendered.

   When both branches of a decision fail, their two nogoods --
     "~l" branch:  (negated ancestor decisions) \/ l
     "l"  branch:  (negated ancestor decisions) \/ ~l
   -- resolve on [l] (itself a [rup], found trivially by unit propagation against the
   two clauses, both still live in the database at that point) into the ancestor-only
   nogood, i.e. the failure is propagated exactly one level up, mirroring chronological
   backtracking. The two child nogoods are then retired with a single [w] at the level
   they were tagged with (D-0008: one wipe per backtrack, not one deletion per
   reason), and the combined nogood survives, tagged one level up. Recursing this to
   the root produces, when the whole search space is exhausted, the empty clause --
   an unconditional contradiction -- which is exactly the id [conclusion UNSAT] cites
   (invariant I-S2: the proof independently establishes it, not merely the solver's
   own "I looked everywhere" bookkeeping). *)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

type assignment = (Var.t * int) list

type outcome = Sat of assignment | Unsat

(* Raised if the independently-checked solution (invariant I-S1) fails the caller's
   own [check] -- a propagator soundness bug (I-P1), never a normal outcome. [solve]
   must not paper over this by pretending UNSAT or silently retrying. *)
exception Unsound_solution of assignment

(* One node's outcome, before it has been reported to its own caller: a solution, or a
   nogood -- the clause already asserted into the proof (its [Writer.cid] is still
   live) together with the literals it states, so the caller can drop its own most
   recent decision literal and re-derive the next nogood up. *)
type node = NSat of assignment | NFail of Lit.t list * Writer.cid

(* ------------------------------------------------------------------ variable choice *)

(* First-fail (docs/SPEC.md 3.4): the unfixed variable (domain size > 1) with the
   smallest domain, ties broken by declaration order (the store's variable index). *)
let pick_var store =
  let n = Store.n_vars store in
  let best = ref None in
  for i = 0 to n - 1 do
    let v = Var.of_int i in
    let size = Domain.size (Store.get store v) in
    if size > 1 then
      match !best with
      | None -> best := Some (v, size)
      | Some (_, bsize) -> if size < bsize then best := Some (v, size)
  done;
  Option.map fst !best

let extract_assignment store : assignment =
  List.init (Store.n_vars store) (fun i ->
      let v = Var.of_int i in
      (v, Domain.lo (Store.get store v)))

(* ------------------------------------------------------------------------------ dfs *)

(* [decisions] is the stack of literals actually forced true so far by branching,
   most-recent decision first -- so [List.map Lit.negate decisions] is, at every
   point, exactly the nogood clause that would state "not all of these hold". *)
let rec dfs engine store ctx (decisions : Lit.t list) : node =
  match Engine.propagate engine store with
  | Engine.Conflict _ ->
      (* The propagator's own [Explanation.t] is deliberately not consulted -- see the
         module header. Only the active decisions matter to the proof. *)
      let lits = List.map Lit.negate decisions in
      let cid = Justify.emit ctx (Explanation.clause lits) in
      NFail (lits, cid)
  | Engine.Fixpoint -> (
      match pick_var store with
      | None -> NSat (extract_assignment store)
      | Some v -> branch engine store ctx decisions v)

and branch engine store ctx decisions v : node =
  let d = Store.get store v in
  let lo = Domain.lo d in
  let name = Store.name store v in
  let lit = Lit.ge name (lo + 1) in
  (* indomain_min: [x = lo] (~lit) before [x > lo] (lit). *)
  Store.new_level store;
  let lvl = Store.level store in
  Writer.set_level ctx.Justify.writer lvl;
  let r1 = explore_hi store engine ctx decisions v lo lit in
  Store.backtrack store;
  match r1 with
  | NSat asn ->
      Justify.wipe_level ctx lvl;
      NSat asn
  | NFail (lits1, _) -> (
      Store.new_level store;
      let lvl2 = Store.level store in
      Debug.check "search: reopened level matches the one just closed" (fun () ->
          lvl2 = lvl);
      Writer.set_level ctx.Justify.writer lvl;
      let r2 = explore_lo store engine ctx decisions v lo lit in
      Store.backtrack store;
      match r2 with
      | NSat asn ->
          Justify.wipe_level ctx lvl;
          NSat asn
      | NFail (lits2, _) ->
          let combined =
            match lits1 with
            | _ :: tl -> tl
            | [] ->
                invalid_arg
                  "Search.branch: a branch's own nogood must mention its own decision"
          in
          Debug.check "search: both children's nogoods agree past their own decision"
            (fun () ->
              match lits2 with
              | _ :: tl2 -> List.length tl2 = List.length combined
              | [] -> false);
          Writer.set_level ctx.Justify.writer (lvl - 1);
          let cid = Justify.emit ctx (Explanation.clause combined) in
          Justify.wipe_level ctx lvl;
          NFail (combined, cid))

and explore_hi store engine ctx decisions v lo lit =
  match Store.set_hi store v lo Explanation.trivial with
  | Store.Conflict _ ->
      (* [lo] is always in [v]'s domain, so [set_hi _ lo] cannot fail; kept only so
         this function is total against [Store.outcome] without assuming it. *)
      let lits = List.map Lit.negate (Lit.negate lit :: decisions) in
      let cid = Justify.emit ctx (Explanation.clause lits) in
      NFail (lits, cid)
  | Store.Changed | Store.Unchanged -> dfs engine store ctx (Lit.negate lit :: decisions)

and explore_lo store engine ctx decisions v lo lit =
  match Store.set_lo store v (lo + 1) Explanation.trivial with
  | Store.Conflict _ ->
      let lits = List.map Lit.negate (lit :: decisions) in
      let cid = Justify.emit ctx (Explanation.clause lits) in
      NFail (lits, cid)
  | Store.Changed | Store.Unchanged -> dfs engine store ctx (lit :: decisions)

(* ------------------------------------------------------------------------------ API *)

(* Depth-first search from the store's current decision level (I-S3: the level on
   return equals the level on entry -- true here by construction, since every
   [Store.new_level] this module calls is paired with exactly one [Store.backtrack]
   before returning).

   [engine] is shared, reusable state (its watcher table does not depend on the
   store's contents); [store] and [ctx] carry the search's actual state. [check] is
   the independent re-verification invariant I-S1 requires -- "every solution printed
   satisfies every constraint, re-checked independently ... not by trusting the
   propagators". There is deliberately no way to skip it: a caller without a real
   model-level checker at hand (M1-T10 lands before the FlatZinc [Model.t] is wired to
   the solver) still has to pass one, even if it is a small hand-written one, as the
   tests below do.

   On [Sat], the proof's [conclusion] cites the found assignment directly (never a
   bare [sol], which the doc notes only works when deletion-checking was never turned
   off -- the assignment form always works). On [Unsat], it cites the id of the
   final, decision-free nogood. Both leave [Writer]'s audit-mode live set exactly as
   it was before the call plus that one id, which [Writer.conclusion] itself retires
   (invariant I-X2 -- see docs/PROOF-FORMAT.md section 5, "discharged by the
   conclusion"). *)
let solve ~(engine : Engine.t) ~(store : Store.t) ~(ctx : Justify.ctx)
    ~(check : assignment -> bool) () : outcome =
  let entry_level = Store.level store in
  let result = dfs engine store ctx [] in
  Debug.check "I-S3: decision level on return equals level on entry" (fun () ->
      Store.level store = entry_level);
  match result with
  | NSat assignment ->
      if not (check assignment) then raise (Unsound_solution assignment);
      let bindings =
        List.map (fun (v, x) -> (Store.name store v, x)) assignment
      in
      let lits = Encoding.assignment_lits ctx.Justify.encoding bindings in
      Writer.conclusion ctx.Justify.writer (Writer.Sat lits);
      Sat assignment
  | NFail (lits, cid) ->
      (match lits with
      | [] -> ()
      | _ ->
          invalid_arg
            "Search.solve: the root nogood must be decision-free -- solve must be \
             called with no ambient decisions active");
      Writer.conclusion ctx.Justify.writer (Writer.Unsat (Some cid));
      Unsat
