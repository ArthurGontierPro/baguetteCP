(* int_lin_le: sum_i a_i * x_i <= c, over integer variables with possibly negative
   coefficients.

   Consistency level: BOUNDS (docs/SPEC.md 3.2). This propagator only ever reads and
   writes lo/hi; it never punches a hole. It is the reference propagator (docs/ROADMAP.md
   M1-T7a) - every later propagator in prop/ copies this shape, so the structure below
   (compute once, explain lazily, one pass to fixpoint) is deliberate.

   Algorithm (textbook bounds propagation for a linear inequality):

     slack = c - sum_i min(a_i * x_i)
       where min(a_i * x_i) = a_i * lo(x_i)  if a_i >= 0
                             = a_i * hi(x_i)  if a_i <  0

     - slack < 0            : no assignment in the current box satisfies the
                               constraint -> Conflict.
     - otherwise, for each i with a_i <> 0:
         max_i = min(a_i * x_i) + slack        (* largest value a_i*x_i may take *)
         a_i > 0 :  x_i <= floor(max_i / a_i)  -> tighten hi(x_i)
         a_i < 0 :  x_i >= ceil (max_i / a_i)  -> tighten lo(x_i)

   [slack] is computed once from the pre-propagation bounds, and every push above reads
   only the *other* variables' minima, which do not change as a result of tightening
   [x_i] itself (tightening hi(x_i) never moves lo(x_i), and vice versa for a_i < 0). So a
   single pass over all terms already reaches the bounds-consistent fixpoint; there is no
   need to loop back over the terms already visited. That is what makes [propagate]
   idempotent at the interface (I-P3) after just one pass: calling it again recomputes the
   same slack (now possibly larger, since a variable may have been tightened) and finds
   nothing left to push.

   Declared bounds (docs/DECISIONS.md D-0010): a bound fact has to be stated in the order
   encoding's own currency, x = lo_decl + sum_{v=lo_decl+1}^{hi_decl} [x >= v], which needs
   the variable's *declared* domain, not just its current one. [make] therefore reads each
   variable's domain out of the store at construction time and freezes it into [term] -
   this has to happen before anything (including this propagator, on a later call) has
   narrowed it.

   [make] also takes [~row_id], the id (a Baguette_proof.Writer.cid, i.e. plain [int] --
   this module has no reason to depend on [Baguette_proof.Writer] just for its type) the
   .opb already gave this instance's own row. D-0011: one instance justifies against
   exactly one row, and that row is posted to the encoding before any propagator ever
   runs, so the id is available at construction time; passing it in beats resolving it
   later through an ambient [Justify.ctx], which is exactly the trap D-0013 hit (see
   [Explanation.Model_row]'s header in lib/core/explanation.ml).

   It is **required**, as of M1-T31. It was optional while nothing wired a model to the
   engine (D-0010's note), and the fallback was [Explanation.Trivial] -- "whatever row
   [ctx.model_id] currently points at". That fallback is what made the ambient row
   reachable at all, so removing it and deleting [Trivial] are one change: with no
   caller able to omit the id and no constructor able to mean "the current row", a
   [Justify.ctx] has nowhere left to keep an ambient row and does not have the field.
   A test that has no real row and does not care which one it names should pass a
   made-up id and say so, rather than leave the question open.

   ---------------------------------------------------------------------------
   Proof step this justifies -- docs/DECISIONS.md D-0013, "weaken, divide, add"
   ---------------------------------------------------------------------------

   For a pruning that tightens variable [j] (all other terms i <> j untouched), the
   explanation is

     Combine (Term (1, Model_row row_id) :: [ other_i's summand | i <> j, a_i <> 0 ],
              abs a_j)

   where, for each other term i:
     - if [x_i]'s current bound *relevant to this row* (lo if a_i >= 0, hi if a_i < 0)
       is still its *declared* one, [i]'s summand is [Weaken chain] -- the full
       declared-width axiom chain [Order_reason.weaken_declared] builds, scaled by
       [a_i]. An axiom cannot assert a bound (D-0009), but weakening one away needs no
       assertion: it is sound regardless of what [x_i] turns out to be.
     - otherwise [x_i]'s current bound was itself established by an earlier trail
       entry (bounds only ever tighten, so if it is not declared, something set it):
       [i]'s summand is [Term (abs a_i, that entry's explanation)] -- cite it, do not
       re-derive it. [find_lo_reason]/[find_hi_reason] below locate it.

   The second bullet hides a premise, and M1-T44 is what happens when it is false:
   *the cited entry's explanation establishes the entry's recorded bound*. It does not
   when [Domain.settle] walked that bound past a hole (see [settled_over_lo] below),
   because the hole is a disequality's doing and the row's own derivation says nothing
   about it. Those entries therefore cite the hole's reason as well, which is what makes
   the dependency list honest -- and, since a [Clause] is what a hole's reason is,
   what makes [Search.rests_on_a_clause] route the conflict the D-0022 way instead of
   citing a chain that cannot close.

   Dividing the sum by [abs a_j] is D-0013 step 4 (and the "one division"
   docs/PROOF-FORMAT.md section 4 promises): [j]'s own terms are the only ones left
   with a nonzero coefficient after every other term cancels (each [Weaken] cancels
   its row contribution to a constant, D-0009; each cited [Term] is, by this same
   construction applied recursively, already a unit-coefficient statement purely
   about its own variable's full declared-range literals, and the [abs a_i] scaling
   here makes it cancel [row_id]'s own coefficient for that variable exactly the same
   way a [Weaken] does), so dividing by [abs a_j] reduces [j]'s own coefficient to a
   unit one directly -- see [Order_reason.weaken_declared]'s header for why the
   *polarity* half of this ("which literal cancels") depends only on the sign of the
   row's own coefficient, and D-0013 (docs/DECISIONS.md) for the worked example this
   whole shape is checked against.

   A [Conflict] from this row's own slack (slack < 0, no term excluded) is the same
   shape, over every term, with divisor 1 -- there is no variable left to solve for,
   just a direct numeric contradiction (D-0013 step 5's "0 >= positive", generalised
   past two terms).

   A [Conflict] from [Store.set_hi]/[set_lo] (the new bound this row computed
   contradicts a bound some *other* propagator instance already established -- the
   cross-row case D-0013's own worked example exercises, its final two steps) combines
   this row's own new-bound derivation with whatever explanation currently holds the
   *opposite* bound on the same variable, added, divisor 1 -- D-0013 step 5, "two
   opposite bounds on the same variable, added".

   ---------------------------------------------------------------------------
   Arithmetic (roadmap M1-T23)
   ---------------------------------------------------------------------------

   Every product, sum, difference and division below goes through [Checked]
   (lib/core/checked.ml), which raises [Checked.Overflow] rather than wrapping. Read
   that module's header before changing any of it: this is not defensive decoration,
   it is the fix for the one soundness gap M1 found. A wrapped [a_i * lo_i] here does
   not merely prune wrongly -- [Encoding.linear_terms_int_lin_le] folds the *same*
   product into the .opb row's constant, so the corrupted row and the corrupted slack
   agree and veripb accepts a refutation of a model nobody wrote.

   Nothing on this path can raise for a model the CLI accepted:
   lib/flatzinc/compile.ml caps every declared bound and every row's magnitude
   |c| + sum_i |a_i| * max(|lo_i|, |hi_i|) at [Checked.limit], which leaves a factor
   of 16/9 over the largest intermediate anything computes from the row. The raise is
   for callers that build a [Linear.t] directly, which is what every unit test does. *)

module Lit = Baguette_proof.Lit

(* One term of the sum: coefficient (may be negative or zero; zero terms are inert and
   never generate a bound or appear in an explanation), the variable it multiplies, and
   the variable's *declared* domain, frozen at [make] time (D-0010: the offset an
   explanation needs is the declared bound, which the store no longer holds once this or
   any other propagator has narrowed the domain). *)
type term = { coeff : int; x : Var.t; decl_lo : int; decl_hi : int }
type t = { terms : term list; rhs : int; row_id : int }

let name = "int_lin_le"
let consistency = Propagator.Bounds

(* [row_id] is required (M1-T31; see the module header). Every [Combine] this instance
   builds is based on [Model_row row_id], so an instance without one could not name its
   own base -- and the old answer to that, [Explanation.trivial], named whichever row
   happened to be ambient in the [Justify.ctx] doing the rendering. *)
let make ~row_id store raw_terms rhs =
  let terms =
    List.map
      (fun (coeff, x) ->
        let d = Store.get store x in
        { coeff; x; decl_lo = Domain.lo d; decl_hi = Domain.hi d })
      raw_terms
  in
  { terms; rhs; row_id }

let base_explanation t = Explanation.model_row t.row_id
let vars t = List.map (fun tm -> tm.x) t.terms

(* -------------------------------------------------------------- integer division *)

(* [Stdlib.(/)] truncates toward zero, which is the wrong rounding for a negative
   dividend or divisor: bounds propagation needs floor/ceil of the exact rational
   quotient regardless of sign. [b] is never zero here (callers only apply these to
   nonzero coefficients).

   Both are now [Checked]'s, re-exported under their old names because test_prop.ml
   asserts a pushed bound against [Linear.floordiv]/[Linear.ceildiv] by name. The
   rounding is character for character the rounding this module used to do inline;
   what [Checked] adds is the guard on min_int / -1, the one division whose quotient
   does not fit. [Checked.ceildiv] also stops routing through [-(floordiv (-a) b)],
   which was a second place a native int could wrap -- [-a] has no answer for
   a = min_int -- and answers the case split directly instead. *)
let floordiv = Checked.floordiv
let ceildiv = Checked.ceildiv

(* ------------------------------------------------------------------- min/max terms *)

(* The smallest value [a * x] can currently take, given [x]'s domain. The product is
   checked: wrapping it is the M1-T23 gap, and it wraps into the .opb row as well as
   into the slack (see the module header). *)
let term_min store (tm : term) =
  let d = Store.get store tm.x in
  if tm.coeff >= 0 then Checked.mul tm.coeff (Domain.lo d)
  else Checked.mul tm.coeff (Domain.hi d)

(* -------------------------------------------------------- locating an earlier reason *)

(* The most recent trail entry for [v] that tightened its *lower* bound to (at least)
   its current value, or [None] if [v]'s current lo is still its declared one.

   Domain lo only ever increases (I-D3/I-D2), so the newest entry for [v] whose [old]
   domain had a strictly smaller lo than the current one is exactly the entry that
   pushed lo to where it now sits: every entry for [v] *more recent* than it (already
   skipped, scanning newest-first) left lo unchanged, or it would have been the one
   found instead.

   M1-T28: this walks the trail *by index, downwards*, and both halves of that matter.

   By index, because [Store.trail_entries] materialises the whole trail as a fresh
   list before the scan looks at a single entry, and the scan then stops at the first
   match -- usually within a few entries of the newest. It runs once per term per
   pruning, not once per propagator call, so it was the most expensive O(|trail|)
   allocation left in [lib/] after M1-T24 fixed the identical defect in
   [Engine.propagate]. [Store.trail_entry] is O(1) and says so in its own comment.

   Downwards, because [Store.trail_entries] returns the trail *most recent first*
   (its own header says so, and its loop prepends ascending positions, so the head is
   position [trail_length - 1]). Scanning that list head-first is therefore scanning
   positions downwards. This is M1-T24's lesson restated: the obvious rewrite,
   [for i = 0 to trail_length - 1], is not a slower version of the same function, it
   is a *different* function -- it returns the OLDEST entry that moved the bound
   rather than the newest, so the pruning would cite a superseded reason. The two
   differ only on a variable whose bound moved twice in one branch, which is why no
   type and no model in the suite can tell them apart (see the commit message). *)
(* ---------------------------------------------------------------------------
   M1-T44: a bound can be stronger than the entry that carries it

   [Domain.set_lo] does not stop where the propagator asked. It re-establishes I-D2 by
   *settling* -- walking the new bound up past any hole it lands on -- so a trail
   entry's recorded [lo] can be strictly greater than the bound its own explanation
   derives, by exactly the run of holes immediately below it. Citing that entry as the
   reason for its recorded bound is then short by that run, and a [Combine] built on it
   lands on [0 >= 0] instead of [0 >= k]. That is the whole of M1-T44: the arithmetic
   was never wrong, the *dependency list* was, because the hole's own reason -- a
   disequality's [Clause], punched by [Store.remove_with_facts] -- is on the trail and
   was silently dropped. See test/models/root_hole_unsat.fzn for the worked instance.

   Holes only ever enter a domain through a removal, so each one has a trail entry
   carrying its reason and the two functions below find it. The exception is a hole the
   variable was *declared* with ([Domain.of_list]): no entry ever removed it, and it is
   skipped here. That is not this task papering over the same bug in another guise --
   lib/proof/encoding.ml has no representation for a declared hole at all, so such a
   variable's declared domain is not in the .opb in the first place; nothing this module
   can cite would make a proof about it sound. It is unreachable from the CLI today
   (lib/flatzinc/ never calls [Domain.of_list]) and reported as a finding rather than
   guarded here, because a guard would fail loudly in unit tests that build such a
   domain for reasons that have nothing to do with the proof.

   Both directions are reached, and each is load-bearing on its own -- measured, not
   assumed, because a mirrored pair is where this project keeps shipping a half that
   nothing runs. Probed over one fuzzer seed (test/unit/test_random.ml, seed 133, 200
   cases x 9 branching orders): the lower-bound settle fires 62 times and the UPPER-bound
   settle 71. Each half was then broken on its own, and they fail in different places --
   dropping [settled_over_lo]'s holes turns test/models/root_hole_unsat.fzn red and
   leaves that seed green; dropping [settled_over_hi]'s holes leaves the model green and
   turns 9 of that seed's cases red. Neither test covers the other's half. *)

(* The values [Domain.settle] walked the lower bound over on its way to [cur], newest
   domain state [old] being the one the entry started from: the maximal run of holes
   immediately below [cur]. It stops at the first value [old] still held, which is at or
   above whatever bound was actually pushed -- so this never claims more than the settle
   did. Empty when the entry's bound is exactly the bound its explanation derives, which
   is every entry in a model with no disequality. *)
let settled_over_lo old ~cur =
  let rec go v acc =
    if v < Domain.lo old || Domain.mem old v then acc else go (v - 1) (v :: acc)
  in
  go (cur - 1) []

let settled_over_hi old ~cur =
  let rec go v acc =
    if v > Domain.hi old || Domain.mem old v then acc else go (v + 1) (v :: acc)
  in
  go (cur + 1) []

(* The reason of the entry that took [value] out of [v]'s domain, searched from trail
   position [before] downwards. A value leaves a domain once and never comes back
   within a level, so there is at most one; [None] means it was a declared hole (see
   above). *)
let find_removal store v ~before ~value =
  let rec scan i =
    if i < 0 then None
    else
      let e : Store.entry = Store.trail_entry store i in
      if Var.equal e.var v && Domain.mem e.old value && not (Domain.mem e.now value) then
        Some (Store.explanation store e)
      else scan (i - 1)
  in
  scan before

(* Every reason the current lower bound of [v] rests on: the entry that moved it, then
   one per hole that entry's settle walked over. [[]] exactly when the bound is still
   the declared one (the old [None]). *)
let find_lo_reason store v ~decl_lo =
  let cur = Domain.lo (Store.get store v) in
  if cur <= decl_lo then []
  else
    let rec scan i =
      if i < 0 then []
      else
        let e : Store.entry = Store.trail_entry store i in
        if Var.equal e.var v && Domain.lo e.old < cur then
          Store.explanation store e
          :: List.filter_map
               (fun h -> find_removal store v ~before:(i - 1) ~value:h)
               (settled_over_lo e.old ~cur)
        else scan (i - 1)
    in
    scan (Store.trail_length store - 1)

(* Symmetric for the upper bound: the entry that pushed hi down to its current value.
   Newest first, so the same downward index walk -- see [find_lo_reason]. *)
let find_hi_reason store v ~decl_hi =
  let cur = Domain.hi (Store.get store v) in
  if cur >= decl_hi then []
  else
    let rec scan i =
      if i < 0 then []
      else
        let e : Store.entry = Store.trail_entry store i in
        if Var.equal e.var v && Domain.hi e.old > cur then
          Store.explanation store e
          :: List.filter_map
               (fun h -> find_removal store v ~before:(i - 1) ~value:h)
               (settled_over_hi e.old ~cur)
        else scan (i - 1)
    in
    scan (Store.trail_length store - 1)

(* ------------------------------------------------------ per-term summand, snapshotted *)

(* What a term contributes to a [Combine], decided *now* (D-0013: declared vs. derived)
   but with the expensive parts -- the [Lit.t] chain, or forcing the cited explanation
   -- left for [summand_of_snap] to build only when the whole explanation is actually
   forced (docs/ARCHITECTURE.md, "Deferred explanations"). Snapshotting the *decision*
   eagerly, not just cheap ints, matters here specifically because which trail entry
   currently witnesses a bound can change (or vanish on backtrack) between now and
   whenever this explanation is finally forced -- the snapshot pins down *this* row's
   own reason to cite, not whatever happens to be current later.

   [Snap_cite]'s [holes] is M1-T44's addition: [expl] is still the entry that moved the
   bound, and [holes] the reason of every hole that entry's settle walked past on the
   way to it. [holes] is empty for every bound that was not settled over one, which is
   every bound in a model with no disequality, and the rendering is then unchanged.

   ---------------------------------------------------------------------------
   [Snap_assume] -- M1-T50: a bound a *decision* established cannot be cited
   ---------------------------------------------------------------------------

   The [Snap_cite] branch's whole premise is that the bound was established by
   something with an id in the proof. A search decision is not: nothing derives it
   (D-0009, and search.ml's header argues it at length), so there is no constraint for
   a [pol] to name. Until M1-T50 that case still took the [Snap_cite] branch, because
   the reason a decision pushed was [Explanation.Trivial] and so indistinguishable from
   a model row; [Justify.emit] then answered [ctx.model_id ()] and the step came out as
   `pol <own row> <own row> +` -- the row added to itself, where the fact belonged. It
   verified, because a [pol] makes no claim for a checker to refuse, and it said
   something the explanation did not.

   [Explanation.Decision] now names the case, and the honest rendering is the one that
   was always available: *weaken the term away*, exactly as for a bound still at its
   declared value. An axiom cannot assert a bound but it can weaken one away (D-0009),
   and it is valid whatever the variable turns out to be, so the resulting [Combine] is
   sound. It is also *weaker* than the bound the propagator pushed -- it has to be,
   because the decision the pruning really rested on is not in the checker's database
   at all. That is not a loss: a pruning made under a decision is justified by D-0018's
   trace line, never by this [pol] (a [Combine] is emitted only at a root conflict,
   where by construction no decision is in force), and the trace line is where the
   decision's literal belongs.

   Which is why [Snap_assume] keeps [fact] and [Snap_weaken] does not. The two render
   identically into the [Combine] and differently into [facts_of_snaps]: the decision
   moved the bound, so the pruning does depend on it, and dropping it from the trace
   line would make that line an unconditional claim -- false on a satisfiable model,
   the exact I-P5 failure [int_ne] shipped between M1-T9 and M1-T17. The emitted facts
   are therefore byte-for-byte what they were before this change. *)
type source_snap =
  | Snap_weaken of { coeff : int; name : string; decl_lo : int; decl_hi : int }
  | Snap_cite of {
      coeff : int;
      expl : Explanation.t;
      holes : Explanation.t list;
      fact : Lit.t;
    }
  | Snap_assume of {
      coeff : int;
      name : string;
      decl_lo : int;
      decl_hi : int;
      fact : Lit.t;
    }

(* Is any reason this bound rests on a search decision?

   Matched WITHOUT forcing, deliberately. [Explanation.force] on a [Deferred] runs a
   propagator's thunk, and this predicate is consulted once per term per pruning at
   *snapshot* time -- forcing here would make every explanation eager and undo
   docs/ARCHITECTURE.md's "Deferred explanations" wholesale. It costs nothing to skip:
   [Explanation.decision] is the only producer of a [Decision] and search.ml pushes it
   directly, so a decision never arrives wrapped in a thunk. A [Deferred] that forced
   to one would be a propagator claiming to have derived an assumption, which is a
   different bug from this one.

   The whole list, not just the head: a hole's reason (M1-T44) is cited at the same
   scale as the bound itself, so if any of them is uncitable the term cannot be cited
   at all and the honest move is to weaken the lot away. Holes come from
   [Store.remove_with_facts] and a decision never removes a value, so this is a guard
   on the invariant rather than a case anything reaches today. *)
let rests_on_a_decision reasons =
  List.exists (function Explanation.Decision _ -> true | _ -> false) reasons

(* [None] only for a zero coefficient (an absent term, contributing nothing). Otherwise
   picks the bound relevant to this term's sign (D-0013's own case split, matching
   [term_min]'s), and within it: declared (weaken), assumed (weaken, but keep the fact
   -- M1-T50), or derived (cite). See the module header for all three.

   The defensive branches below (falling back to weakening when the bound is tighter
   than declared but no trail entry can be found) should be unreachable -- I-D2/I-D3
   guarantee a bound only tightens via a recorded entry -- but weakening is still
   *sound* even if this bookkeeping is ever wrong, just weaker than it should be, so a
   defensive fallback here fails soft rather than emitting something unsound. *)
let snapshot_source store (tm : term) : source_snap option =
  if tm.coeff = 0 then None
  else
    let name = Store.name store tm.x in
    let weakened =
      Snap_weaken { coeff = tm.coeff; name; decl_lo = tm.decl_lo; decl_hi = tm.decl_hi }
    in
    let assumed fact =
      Snap_assume
        { coeff = tm.coeff; name; decl_lo = tm.decl_lo; decl_hi = tm.decl_hi; fact }
    in
    let derived reasons fact =
      match reasons with
      | _ when rests_on_a_decision reasons -> assumed fact
      | expl :: holes -> Snap_cite { coeff = tm.coeff; expl; holes; fact }
      | [] -> weakened
    in
    if tm.coeff >= 0 then
      let cur = Domain.lo (Store.get store tm.x) in
      if cur <= tm.decl_lo then Some weakened
      else
        Some (derived (find_lo_reason store tm.x ~decl_lo:tm.decl_lo) (Lit.ge name cur))
    else
      let cur = Domain.hi (Store.get store tm.x) in
      if cur >= tm.decl_hi then Some weakened
      else
        Some (derived (find_hi_reason store tm.x ~decl_hi:tm.decl_hi) (Lit.le name cur))

(* One snapshot, one *or more* summands. A [Snap_cite] with holes behind it contributes
   one [Term] per reason, all at [abs coeff] -- the scale at which the bound itself
   enters, since each hole is a fact about the same variable's same chain. The extra
   terms do not cancel the row's coefficient the way the bound's own chain-sum does, so
   the [Combine] is no longer the self-contained numeric chain D-0013 describes; it is
   still a sound [pol] (a [pol] derives whatever it derives), and the reason it may stop
   closing on its own is precisely D-0022's, which is why [Search.rests_on_a_clause] --
   reading exactly these summands -- then routes the conflict to its empty-clause close
   instead of citing the chain. D-0022 settled the same trade the other way round for a
   clause folded in as a bound, and for the same reason: weakening it away would erase
   the signal and still not close. *)
let summands_of_snap = function
  | Snap_weaken { coeff; name; decl_lo; decl_hi }
  (* M1-T50: identical arithmetic to [Snap_weaken]. The two differ only in
     [facts_of_snaps] -- see the [source_snap] header. *)
  | Snap_assume { coeff; name; decl_lo; decl_hi; _ } ->
      let lits, _ = Order_reason.weaken_declared ~coeff ~name ~decl_lo ~decl_hi in
      [ Explanation.weaken lits ]
  | Snap_cite { coeff; expl; holes; _ } ->
      List.map (fun e -> Explanation.term (Checked.abs coeff) e) (expl :: holes)

(* docs/DECISIONS.md D-0018's *other* projection of the same snapshot: the bound facts
   this row actually read, one order literal per other term, for the trace line
   lib/core/trace.ml writes. Deliberately not [Explanation.lits] of the [Combine] --
   that yields the declared-width [Weaken] chains the [pol] needs, which state nothing
   about where a bound currently sits.

   A [Snap_weaken] term contributes no literal at all: its bound is still the declared
   one, so the fact is the encoding's own constant true (docs/PROOF-FORMAT.md section 3,
   [Encoding.ge]'s [Holds]) and its negation is false. Putting it in the clause would be
   wrong twice over -- there is no such literal, and a false disjunct is not a weakening.

   A [Snap_cite] term contributes the literal for the bound as it stood *at the moment
   of the pruning* ([snapshot_source] pins this down, which is what lets the whole trace
   be written later, when the branch fails, and still be a faithful record of what was
   derived when). Sign follows the same case split as the [Combine]: a_i >= 0 reads
   lo(x_i) and states [x_i >= lo], a_i < 0 reads hi(x_i) and states [x_i <= hi]. *)
let facts_of_snaps snaps =
  List.filter_map
    (function
      | Snap_cite { fact; _ } | Snap_assume { fact; _ } -> Some fact
      | Snap_weaken _ -> None)
    snaps

(* All terms except the one at [idx] (by position, not value - a variable could in
   principle appear twice, and each occurrence is excluded independently). *)
let others_except terms idx = List.filteri (fun i _ -> i <> idx) terms

(* The [Combine] that justifies tightening the term at [idx] (or, for a row-level
   conflict, justifies the row's own contradiction, when [idx] is [None] and every
   term is "other"). Cheap eagerly (the snapshot decision above); the [Lit.t] chain
   and any recursive [emit] happen only once [Justify.emit] actually forces this. *)
let row_snaps store terms ~exclude =
  let others = match exclude with None -> terms | Some idx -> others_except terms idx in
  List.filter_map (snapshot_source store) others

let explain_of_snaps base snaps divisor =
  Explanation.deferred (fun () ->
      let summands = Explanation.term 1 base :: List.concat_map summands_of_snap snaps in
      Explanation.combine summands divisor)

let explain_row store base terms ~exclude divisor =
  explain_of_snaps base (row_snaps store terms ~exclude) divisor

(* D-0013 step 5: a conflict where this row's own new bound for [tm] contradicts a
   bound some *other* propagator instance already holds on the same variable -- add
   this row's own (already fully divided, unit-coefficient) derivation to whatever
   explanation currently holds the *opposite* bound, divisor 1. [new_bound_expl] is
   exactly what [Store.set_hi]/[set_lo] was just handed (the row's own derivation of
   the value that turned out to conflict); the store returns it back unchanged on
   [Conflict], so a caller could equally well reuse the value it already has instead
   of trusting the returned one, and this module does. *)
(* The literal for the *opposite* bound involved in a cross-row conflict, or [None]
   when that bound is still the declared one (the constant true -- and the case
   [explain_cross_conflict] below refuses outright). Same shape as [facts_of_snaps]'s
   per-term literal, for the one variable the two rows disagree about. *)
let opposite_bound_fact store (tm : term) =
  let name = Store.name store tm.x in
  let d = Store.get store tm.x in
  if tm.coeff > 0 then
    if Domain.lo d <= tm.decl_lo then None else Some (Lit.ge name (Domain.lo d))
  else if Domain.hi d >= tm.decl_hi then None
  else Some (Lit.le name (Domain.hi d))

(* docs/DECISIONS.md D-0018 is explicit that a [Deferred] thunk must close over a
   *snapshot* and never read live store state: the whole reason the trace can be written
   later, when a branch fails, rather than eagerly at every pruning, is that a reason
   forced late still renders the derivation as of the moment it was made. This function
   used to call [find_lo_reason]/[find_hi_reason] from inside the thunk, i.e. it looked
   at whatever trail entry happened to witness the opposite bound at *force* time. It
   was harmless in practice only because search forces a conflict's explanation
   immediately; under conflict analysis (M2-T3), or under any change that defers the
   rendering past a backtrack, it would have cited a reason that no longer holds -- and
   the symptom would have been a rejected line somewhere else entirely, which is exactly
   the trap D-0018 quotes from GCS. The lookup is therefore done here, eagerly, on the
   same pattern as [snapshot_source]; only building the [Combine] stays deferred. A
   trail scan per cross-row conflict is not a hot path -- conflicts are the rare case,
   and the scan already happened, just a moment later. *)
let explain_cross_conflict store (tm : term) new_bound_expl =
  let opposite =
    if tm.coeff > 0 then find_lo_reason store tm.x ~decl_lo:tm.decl_lo
    else find_hi_reason store tm.x ~decl_hi:tm.decl_hi
  in
  Explanation.deferred (fun () ->
      match opposite with
      | _ :: _ ->
          (* One [Term] per reason the opposing bound rests on -- the entry that moved
             it, plus any hole its settle walked over (M1-T44, [find_lo_reason]). *)
          Explanation.combine
            (Explanation.term 1 new_bound_expl
            :: List.map (fun e -> Explanation.term 1 e) opposite)
            1
      | [] ->
          (* The opposite bound is still declared, yet contradicts a fresh derivation
             from this row alone -- that would already have been this row's own
             slack < 0 conflict before any per-term push was attempted. Believed
             unreachable at bounds consistency (I-D2/I-D3); fail loudly rather than
             emit an explanation that does not actually derive a contradiction. *)
          invalid_arg
            "Linear.explain_cross_conflict: opposite bound is declared, not derived -- \
             this should have been caught as this row's own slack < 0 conflict")

(* ------------------------------------------------------------------------ propagate *)

(* Every push below hands [Store] both halves of docs/DECISIONS.md D-0018: the
   [Explanation.t] (the [pol] the checker is shown when a derivation is demanded) and
   [~facts] (the bound literals the trace line's clause negates). They come from one
   [row_snaps] call, so the two cannot drift apart -- reading the same snapshot twice,
   at two different moments, is the D-0013 trap [snapshot_source]'s header describes.

   Both conflict paths call [Store.record_conflict_facts] immediately before handing the
   conflict back, for D-0018 point 3: a conflict has no trail entry, so its own reason
   line needs the facts routed separately. *)
let propagate t store =
  let mins = List.map (fun tm -> term_min store tm) t.terms in
  let total_min = Checked.sum mins in
  let slack = Checked.sub t.rhs total_min in
  if slack < 0 then (
    let snaps = row_snaps store t.terms ~exclude:None in
    Store.record_conflict_facts store (fun () -> facts_of_snaps snaps);
    Propagator.Conflict (explain_of_snaps (base_explanation t) snaps 1))
  else
    let result = ref Propagator.Fixpoint in
    let conflict = ref None in
    let cross_conflict tm snaps expl =
      (* The row's own reasons, plus the opposing bound this new one ran into. Both
         halves are snapshotted here, not inside the thunk, for the reason
         [explain_cross_conflict] below spells out. *)
      let opposite = opposite_bound_fact store tm in
      Store.record_conflict_facts store (fun () ->
          facts_of_snaps snaps @ match opposite with Some l -> [ l ] | None -> []);
      conflict := Some (explain_cross_conflict store tm expl)
    in
    List.iteri
      (fun idx (tm, m) ->
        if !conflict = None && tm.coeff <> 0 then
          let max_term = Checked.add m slack in
          let d = Store.get store tm.x in
          if tm.coeff > 0 then (
            let new_hi = floordiv max_term tm.coeff in
            if new_hi < Domain.hi d then
              let snaps = row_snaps store t.terms ~exclude:(Some idx) in
              let expl = explain_of_snaps (base_explanation t) snaps tm.coeff in
              let facts () = facts_of_snaps snaps in
              match Store.set_hi_with_facts store tm.x new_hi ~facts expl with
              | Store.Conflict _ -> cross_conflict tm snaps expl
              | Store.Changed | Store.Unchanged -> ())
          else
            let new_lo = ceildiv max_term tm.coeff in
            if new_lo > Domain.lo d then
              let snaps = row_snaps store t.terms ~exclude:(Some idx) in
              let expl =
                explain_of_snaps (base_explanation t) snaps (Checked.neg tm.coeff)
              in
              let facts () = facts_of_snaps snaps in
              match Store.set_lo_with_facts store tm.x new_lo ~facts expl with
              | Store.Conflict _ -> cross_conflict tm snaps expl
              | Store.Changed | Store.Unchanged -> ())
      (List.combine t.terms mins);
    (match !conflict with Some e -> result := Propagator.Conflict e | None -> ());
    !result
