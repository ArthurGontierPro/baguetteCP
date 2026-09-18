(* pb: a pseudo-Boolean inequality over ORDER LITERALS, propagated by slack,

     a_1 l_1 + ... + a_n l_n  >=  b,     every a_i >= 1

   where each l_i is an order-encoding atom [x >= k] at a polarity (D-0028,
   docs/PROOF-FORMAT.md section 3), so `~[x >= k]` is `x <= k - 1`.

   Consistency level: BOUNDS (docs/SPEC.md 3.2). See "Consistency level" below --
   the declaration is honest and the section says exactly what is left on the table.

   ---------------------------------------------------------------------------
   Why this module exists: D-0054, a SOLVING-side object
   ---------------------------------------------------------------------------

   D-0054 is the precondition and it is one sentence: **a PB line for proof logging and
   a PB explanation for solving are different objects.** The first must be sound,
   complete and CITABLE; the second must be USEFUL TO PROPAGATION. Until M2-L13 this
   tree had only ever built the first.

   [Propagator.pb_row] is explicitly the proof object and its own comment says so: it
   requires [r_cid] because "a row nobody can cite is a row no [pol] can be built from",
   and it is "emphatically not a function of the store because it reads live domains" --
   it is frozen at DECLARED bounds, because "a row that moved with the search would be
   the wrong side of I-X6". Both properties are correct for proof logging and
   disqualifying for propagation, because propagation strength lives in the LIVE domain
   at the moment of the pruning.

   **This module reads live domains, and that is the entire point.** [status] below asks
   [Store.get] on every call. Nothing here is frozen except the DECLARED bounds each
   atom carries, which are the .opb's ladder width and not a search state -- exactly the
   freeze lib/core/learned.ml's "Why the [Linear.t] is built here" argues for, for the
   same reason. The proof row stays static and citable; this object moves.

   [Learned.to_linear_row] used to stand between a learned row and propagation, deciding
   by an ALGEBRAIC IDENTITY OVER THE DECLARED BOX whether the row could be read back as
   an integer linear row that [Linear] would take. D-0050 called that "the right
   predicate used as the wrong gate"; D-0054 named why -- a proof-side test doing a
   solving-side job. M2-L13 removed it from the propagation path: [Learned.to_linear]
   and [Learned.instance] are gone, this module instantiates from [Learned.t] terms
   directly, and [to_linear_row] survives only as the MEASURED counter
   [Search.n_pb_converts] that bin/main.ml already labels "MEASURED ONLY".

   ---------------------------------------------------------------------------
   [Clause] is the degree-1 case, and it is the SAME CODE
   ---------------------------------------------------------------------------

   D-0044 fixed the learned object as a PB inequality with the clause as its degree-1,
   unit-coefficient case. lib/core/prop/clause.ml's header already refused "a second
   implementation to keep in step" for [Array_bool_or]; that refusal applies here with
   more force, so [Clause] does not have a propagator of its own any more. Its [t] IS
   this [t], its [make] and [of_lits] build one with every coefficient 1 and degree 1,
   and its [propagate] is this [propagate]. The type relationship D-0044 asserted is now
   structural instead of asserted.

   The degree-1 arithmetic falls out rather than being special-cased, which is the check
   that the generalisation is the right one. With every a_i = 1 and b = 1:

     - some literal satisfied: slack = |sat| + |open| - 1 >= 0 and a forcing needs
       1 > slack, i.e. slack = 0 with an open literal, which cannot happen while a
       literal is satisfied. Nothing fires -- [Clause]'s old [Satisfied] arm.
     - two or more open, none satisfied: slack = |open| - 1 >= 1, and 1 > 1 is false.
       Nothing fires -- the old [Two_open] arm.
     - exactly one open: slack = 0 and 1 > 0, so that literal is forced -- unit
       propagation, the old [Units [l]] arm.
     - none open, none satisfied: slack = -1 < 0, conflict -- the old [Units []] arm,
       including the opposite-direction HOLE case its header describes (`x >= 3 \/
       x <= 1` with x at [2,2]).

   The explanations coincide too, and byte-identically: see [reason_clause] below.

   ---------------------------------------------------------------------------
   The rule, and why each pruning is RUP against the row on the page
   ---------------------------------------------------------------------------

   Let F be the literals FALSIFIED by the live domains and

     slack  =  ( sum of a_i over i not in F )  -  b.

     - slack < 0: the constraint is violated. Conflict.
     - any OPEN l_i with a_i > slack is forced true.

   Both are the textbook counter/slack rule (Elffers & Nordstrom, IJCAI 2018, and
   RoundingSat as Koops et al. (CP 2025) describe it -- docs/DECISIONS.md:2649, :2677).
   lib/core/reduce.ml's header already states its solving-side half -- "reduce the reason
   so the resolvent stays CONFLICTING" -- and confines it to the analysis; this is the
   same criterion at the other end of the pipeline.

   The PROOF OBLIGATION IS UNCHANGED and was already discharged before this module
   existed: the learned row is on the page as a stated line with its [pol] derivation
   behind it (lib/core/learned.ml's [introduce], lib/core/pb_analysis.ml's). Nothing
   here writes a new proof shape. What it writes is the [rup] every pruning in this
   solver writes, and the one-step RUP argument is:

     a forcing of l_i emits the clause  l_i \/ ( \/_{j in F} l_j ).  Negate it: l_i and
     every l_j in F are false, so the largest the left-hand side can reach is
     (slack + b) - a_i, which is < b because a_i > slack. The row is violated outright,
     so the checker finds the contradiction with no search at all.

     a conflict emits  \/_{j in F} l_j.  Negate it: the left-hand side is at most
     slack + b < b. Violated outright, again in one step.

   That is the same shape lib/core/prop/clause.ml already relies on, which is what
   D-0044's "the clause is the degree-1 case" has to mean on the proof side as well.

   **F is a SNAPSHOT taken at the top of the pass**, and the explanation of every
   forcing in that pass names that same F. It stays valid even if an earlier forcing in
   the same pass falsifies a further literal, because the argument above only needs the
   negated clause to violate the row, and a smaller F makes the bound on the left-hand
   side larger, not smaller. I-X6's snapshot discipline, met by construction.

   ---------------------------------------------------------------------------
   Consistency level: BOUNDS
   ---------------------------------------------------------------------------

   Forcing `x >= v` true moves [lo]; forcing it false moves [hi]. Those are the only two
   mutators this module calls, so it can only ever move bounds. It cannot punch an
   interior hole -- that would need [Store.remove_with_facts], of which I-X10 records
   [Ne] is the sole caller in lib/, and D-0052 told the clause row not to reach for it.

   BOUNDS is also the honest level for a second reason that is about PB and not about
   holes: **the slack rule is not domain consistent even over the literals it does
   mention.** A single row knows nothing about the LADDER constraints that tie
   `[x >= 4]` to `[x >= 3]` (they are separate rows of the .opb, D-0028), which is
   precisely the observation lib/core/pb_analysis.ml's [Postcondition_failed] section
   makes about the same arithmetic on the analysis side. So a row can fail to force a
   literal that the row PLUS the ladder would force. That is a weaker propagator, not an
   unsound one, and BOUNDS claims no more than it delivers.

   [Clause.Bool_clause] still declares DOMAIN, still correctly, on the same [0, 1]
   precondition its [make] checks -- see clause.ml. An instance built here gets BOUNDS.

   ---------------------------------------------------------------------------
   No mutable state, and no watched literals
   ---------------------------------------------------------------------------

   [t] has no [mutable] field and [propagate] keeps nothing between calls. D-0052
   refused watched literals for the clause row because they would be the first
   search-dependent mutable propagator state outside [Store]'s undo trail, and a
   counter-based PB propagator has the same temptation (a cached slack updated on the
   trail). It is refused here for the same reason and for a second one: a cached counter
   that the trail does not undo is the classic way a backtracking PB solver becomes
   unsound in a way no proof check catches, because the wrong slack yields a pruning
   whose [rup] is still valid for the F it names.

   Every pass recomputes from [Store.get]. *)

module Lit = Baguette_proof.Lit

(* One order-encoding atom at a polarity:

     [positive = true ] : the literal is  x >= k
     [positive = false] : the literal is  x <= k - 1

   [name] is frozen at construction -- nothing renames a variable and an explanation
   should not have to hold the store to spell itself out. [decl_lo] / [decl_hi] are the
   DECLARED bounds, which is what [Reason] needs to decide whether a fact materialises
   to a literal at all (M2-T8 / D-0026); they come from the ENCODING and not from the
   store, because an instance built mid-search would otherwise freeze a narrowed box as
   the declared one. lib/core/learned.ml says this at length for the same hazard. *)
type atom = {
  x : Var.t;
  name : string;
  positive : bool;
  k : int;
  decl_lo : int;
  decl_hi : int;
}

(* A strictly positive coefficient on an atom. [of_terms] establishes the sign; a
   [Learned.t] has already normalised to positive coefficients ([Learned.make] absorbs a
   negative one by negating its literal), so the invariant arrives rather than being
   imposed here. *)
type term = { coeff : int; a : atom }

(* [pb] is the whole constraint's literals in term order, and [expl_all] is the clause
   over all of them -- both built once at construction. [expl_all] is not "the
   explanation": for a general row the explanation of a pruning is the SUBSET clause
   [reason_clause] builds. It is kept because in the degree-1 case that subset is always
   the whole thing, and lib/core/justify.ml memoises on PHYSICAL identity, so handing
   back the same value lets one clause emit one [rup] per decision level instead of one
   per pruning. That is the property lib/core/prop/clause.ml's header claims and this
   module has to keep. *)
type t = {
  terms : term list;
  degree : int;
  pb : Lit.t list;
  expl_all : Explanation.t;
  n_terms : int;
}

let name = "pb"

(* BOUNDS. The header's "Consistency level" section is the argument. *)
let consistency = Propagator.Bounds
let pb_lit a = if a.positive then Lit.ge a.name a.k else Lit.le a.name (a.k - 1)

let finish terms degree =
  let pb = List.map (fun tm -> pb_lit tm.a) terms in
  { terms; degree; pb; expl_all = Explanation.clause pb; n_terms = List.length terms }

(* ------------------------------------------------------------------ construction *)

(* An order literal as an atom of this store, or [None].

   [None] for a [Lit.Eq] literal: the direct encoding is a set of 0-1 variables with no
   order to read a bound off (D-0019, D-0040), so a positive [Eq] would have to FIX a
   variable and a negative one would have to punch an interior hole. Both are outside
   what BOUNDS may claim and the second needs [Store.remove_with_facts] (I-X10). [None]
   too for a name this store or this encoding does not know: the honest answer is to
   decline the whole instance rather than to guess a box. A 1UIP cut and a PB row can
   both contain such a literal, so this is a case that really arises and is counted by
   the caller, not a defensive arm. *)
let atom_of store ~(decl : string -> (int * int) option) (l : Lit.t) : atom option =
  match l.Lit.v with
  | Lit.Eq _ -> None
  | Lit.Ge (nm, k) -> (
      match (Store.var_named store nm, decl nm) with
      | Some x, Some (lo, hi) ->
          Some { x; name = nm; positive = l.Lit.positive; k; decl_lo = lo; decl_hi = hi }
      | _ -> None)

(* The general entry: a PB row over proof literals, as [Learned.terms] hands it over.

   Coefficients must be strictly positive, which [Learned.make] guarantees; a
   non-positive one is dropped rather than accepted, because a zero term contributes
   nothing and a negative one would mean the caller skipped the normalisation and the
   row this instance propagates would not be the row on the page.

   [None] if any literal declines. Partial instantiation is not available: dropping a
   literal from a PB row makes it a DIFFERENT, stronger constraint, which is the one
   thing a learned instance must not be. (Dropping a literal from a CLAUSE is also
   strengthening -- same argument, which is why [Clause.of_lits] declined wholesale
   too.) *)
let of_terms store ~decl ~degree (raw : (int * Lit.t) list) : t option =
  let rec go acc = function
    | [] -> Some (finish (List.rev acc) degree)
    | (c, l) :: rest -> (
        if c <= 0 then go acc rest
        else
          match atom_of store ~decl l with
          | None -> None
          | Some a -> go ({ coeff = c; a } :: acc) rest)
  in
  go [] raw

(* The degree-1 entry, for [Clause]: atoms already resolved, every coefficient 1. Not a
   second constructor -- it is [finish] with D-0044's degenerate numbers, written out so
   that the one place the clause case is spelled is here. *)
let of_atoms (atoms : atom list) : t =
  finish (List.map (fun a -> { coeff = 1; a }) atoms) 1

let vars t = List.map (fun tm -> tm.a.x) t.terms
let literals t = t.pb
let width t = t.n_terms
let degree t = t.degree
let coeffs t = List.map (fun tm -> tm.coeff) t.terms

(* ------------------------------------------------------------------- bound facts *)

(* docs/DECISIONS.md D-0018's other projection: the facts lib/core/trace.ml negates into
   the tail of a trace line. A literal that is FALSE is a bound fact -- `x <= k - 1` for
   a positive occurrence, `x >= k` for a negative one -- which is exactly [Lit.negate]
   of the literal, so the line [Trace] builds, [claim :: List.map Lit.negate facts],
   comes out as the clause [reason_clause] built.

   M2-T8 / D-0026: the declared bound is IN the fact, so whether it materialises to a
   literal at all is [Reason.lit_of_fact]'s test and not this module's. *)
let falsity_fact a =
  if a.positive then Reason.at_most ~name:a.name ~decl:a.decl_hi (a.k - 1)
  else Reason.at_least ~name:a.name ~decl:a.decl_lo a.k

(* ------------------------------------------------------------------- propagation *)

type status = Sat_lit | Unsat_lit | Open

(* LIVE domains, every call. See the header: this is the whole difference between this
   object and [Propagator.pb_row]. *)
let status store a =
  let d = Store.get store a.x in
  if a.positive then
    if Domain.lo d >= a.k then Sat_lit
    else if Domain.hi d <= a.k - 1 then Unsat_lit
    else Open
  else if Domain.hi d <= a.k - 1 then Sat_lit
  else if Domain.lo d >= a.k then Unsat_lit
  else Open

(* One full walk: every term's status, in term order. No early exit, unlike the clause
   survey this replaces -- the slack needs every falsified coefficient, so there is
   nothing to stop at. *)
let survey store t = List.map (fun tm -> (tm, status store tm.a)) t.terms

let slack_of degree surveyed =
  List.fold_left
    (fun s (tm, st) -> if st = Unsat_lit then s else Checked.add s tm.coeff)
    (-degree) surveyed

(* The explanation of one step, and the reason facts that go with it.

   [keep] selects the terms the step names: for a forcing, the forced literal plus every
   falsified one; for a conflict, every falsified one. Both are walked IN TERM ORDER,
   which is what makes the degree-1 case byte-identical to the clause propagator this
   replaces -- there the selected set is always the whole constraint, in the same order
   [pb] has, so the value handed to [Explanation.clause] is the same list.

   When the set IS the whole constraint the shared [expl_all] is returned instead of an
   equal fresh one, so lib/core/justify.ml's memoisation on physical identity still
   fires. That is not an optimisation of this module's making: it is the property
   clause.ml's header claims for a clause, preserved. *)
let reason_clause t surveyed ~(keep : term -> status -> bool) =
  let picked = List.filter (fun (tm, st) -> keep tm st) surveyed in
  (* The FALSIFIED members of [picked] are the facts. The forced literal, if [keep] took
     one, is not a fact -- [assign] passes it as [concludes] instead, which is D-0043's
     shape and what lets [Store.apply] check the claim against the bound. *)
  let facts =
    List.filter_map
      (fun (tm, st) -> if st = Unsat_lit then Some (falsity_fact tm.a) else None)
      picked
  in
  let expl =
    if List.length picked = t.n_terms then t.expl_all
    else Explanation.clause (List.map (fun (tm, _) -> pb_lit tm.a) picked)
  in
  (expl, facts)

(* Force one open literal true. A positive atom moves [lo] to [k], a negative one moves
   [hi] to [k - 1]; either way exactly ONE bound moves, so lib/core/trace.ml writes
   exactly one line for it. The reason is not optional and there is no factless mutator
   to reach for (I-P5): without it the line would claim the new bound unconditionally,
   which is false.

   D-0043: [concludes] is the [Reason.fact] mirror of the bound handed to the mutator on
   the next line, against the same declared bounds [falsity_fact] uses, so [Store.apply]
   can check the two against each other. *)
let assign t store surveyed (tm : term) =
  let a = tm.a in
  let expl, facts =
    reason_clause t surveyed ~keep:(fun u st -> u == tm || st = Unsat_lit)
  in
  let concludes =
    Some
      (if a.positive then Reason.at_least ~name:a.name ~decl:a.decl_lo a.k
       else Reason.at_most ~name:a.name ~decl:a.decl_hi (a.k - 1))
  in
  let j = Reason.because ~concludes facts expl in
  if a.positive then Store.set_lo store a.x a.k j else Store.set_hi store a.x (a.k - 1) j

let conflict_of t store surveyed =
  let expl, facts = reason_clause t surveyed ~keep:(fun _ st -> st = Unsat_lit) in
  Propagator.Conflict (Store.conflict store (Reason.because ~concludes:None facts expl))

(* One pass, then repeat while the store moved.

   The loop is what a general PB row needs and a clause does not: forcing one literal
   can falsify a different literal on the SAME variable (`x >= 5` forced true falsifies
   `~[x >= 3]`), which shrinks the slack and can make a further term forceable. Each
   pass recomputes from live domains, so the fixpoint is reached without any cached
   counter -- see the header on why there is none.

   Termination: a pass only repeats when a [Store] mutator reported [Changed], and a
   change strictly narrows a domain over a finite box.

   I-P3: on return there is nothing more to say about this constraint, because the last
   pass found no forceable term and a non-negative slack. *)
let rec propagate t store =
  let surveyed = survey store t in
  let slack = slack_of t.degree surveyed in
  if slack < 0 then conflict_of t store surveyed
  else
    let forced = List.filter (fun (tm, st) -> st = Open && tm.coeff > slack) surveyed in
    if forced = [] then Propagator.Fixpoint
    else
      let rec apply moved = function
        | [] -> if moved then propagate t store else Propagator.Fixpoint
        | (tm, _) :: rest -> (
            match assign t store surveyed tm with
            | Store.Changed -> apply true rest
            | Store.Unchanged -> apply moved rest
            | Store.Conflict e ->
                (* Reachable, unlike the clause case: two forced literals on one
                   variable can be jointly unsatisfiable, and then the row plus the
                   snapshot F really is a contradiction. Forwarded exactly as
                   [Store.apply] returns it, the way every other propagator does. *)
                Propagator.Conflict e)
      in
      apply false forced

(* --------------------------------------------------------------------------------
   The learned face: a PB row this search derived, registered mid-search by
   lib/core/search.ml. Named apart from [name] above so that a trace, a fallback reason
   or an attribution failure says WHICH row -- a model row's or one this search derived
   -- which is the distinction lib/core/retention.ml's citation guard is about.

   A learned instance is on the page only while [Retention] holds it, so a [rup] citing
   it is RUP only while that constraint is live: whoever registers one must
   [Retention.cite] its id. [Search.register_learned_pb] does. That is the same coupling
   M2-L12 created for the learned clause and D-0051's "what would reverse this" section
   is the other half of it. *)
module Learned_pb = struct
  type nonrec t = t

  let name = "learned_pb"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end
