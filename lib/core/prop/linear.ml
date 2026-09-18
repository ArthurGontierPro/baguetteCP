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
       re-derive it. [lo_rests_on]/[hi_rests_on] below locate it, in O(1), out of
       [Store.lo_support] (M2-T8).

   The second bullet hides a premise, and M1-T44 is what happens when it is false:
   *the cited entry's explanation establishes the entry's recorded bound*. It does not
   when [Domain.settle] walked that bound past a hole (see [Store.settled_over_lo]),
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

(* ------------------------------------------------------- M2-L6: this row, as the .opb

   The row [sum a_i x_i <= rhs] rewritten over order literals, in the ">=" form
   [Propagator.pb_row] wants. The identity is the order encoding's own
   (docs/PROOF-FORMAT.md section 3):

     x_i  =  lo_i + sum_{v = lo_i+1}^{hi_i} [x_i >= v]

   so, substituting and moving the constant across,

     sum_i a_i x_i <= rhs
     sum_i a_i lo_i  +  sum_i sum_v a_i [x_i >= v]  <=  rhs
     sum_i sum_v (-a_i) [x_i >= v]  >=  (sum_i a_i lo_i) - rhs

   which is what is returned. Negative coefficients are left as they are: normalising
   them is [Learned.make]'s job and doing it in two places is how the two forms drift
   apart.

   [decl_lo]/[decl_hi] and NOT the live domain -- that is the whole of this function's
   correctness. The .opb contains the ladder of the DECLARED domain; a row built from
   narrowed bounds would be a different constraint from the one [row_id] names, and every
   [pol] citing it would derive something the checker never agreed to. The store is read
   for [Store.name] only, which does not move. See [Propagator.pb_row].

   A term with [a_i = 0] contributes nothing at all, and a singleton declared domain has
   no rungs and contributes only its constant -- both exactly as
   [Encoding.linear_terms_int_lin_le] does it, because these two must agree literally or
   [row_id] names a row this function cannot reproduce. test_learn.ml pins that agreement
   on every model row the suite compiles. *)
let pb_row store (t : t) : Propagator.pb_row =
  let terms, const =
    List.fold_left
      (fun (acc, const) tm ->
        if tm.coeff = 0 then (acc, const)
        else
          let name = Store.name store tm.x in
          let rungs =
            List.init
              (max 0 (tm.decl_hi - tm.decl_lo))
              (fun i -> (-tm.coeff, Lit.ge name (tm.decl_lo + 1 + i)))
          in
          (acc @ rungs, Checked.add const (Checked.mul tm.coeff tm.decl_lo)))
      ([], 0) t.terms
  in
  { Propagator.r_terms = terms; r_degree = Checked.sub const t.rhs; r_cid = t.row_id }

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

(* ------------------------------------------- what holds an earlier bound up *)

(* "What established [x]'s current lower bound?", asked of the store, guarded by *this
   instance's own frozen declared bound*.

   [[]] means "still the declared bound, so weaken the term away" (D-0009: an axiom
   cannot assert a bound but it can weaken one away). Anything else is the derivation to
   cite, plus one per hole its settle walked over (M1-T44, I-X9).

   M2-T8 / D-0026: these two lines are what is left of [find_lo_reason] and
   [find_hi_reason], which scanned the trail downwards from the newest entry, once per
   term per pruning -- O(n * |trail|) per pruning and the most expensive thing left in
   [lib/]. [Store.lo_support] answers the same question in O(1) from an array [Store.apply]
   maintains, and [Store.check_invariants] asserts that array against the trail rather
   than leaving the equivalence argued; [Store.lo_support]'s own header carries the
   argument, including why the direction of the old scan was load-bearing (M1-T28).

   The guard stays HERE and not in [Store], because it is about the propagator and not
   about the store: [decl_lo] is what this instance froze at [make] time, which is not the
   bound the store was created with when a unit test narrows a variable before building
   the propagator. Dropping the guard would make such a test cite an entry where the old
   code weakened, so it is behaviour and not decoration.

   M1-T63: the declared-hole hedge this module used to carry is NOT here any more. A hole
   the variable was declared with ([Domain.of_list]) has no trail entry to cite, and the
   one surviving statement of what happens then is [Store.remover]'s header, which also
   names the gate that makes it unreachable (lib/flatzinc/compile.ml's
   [reject_set_domain], refusing [Model.Dset] outright). M2-T8 deleted this module's copy
   along with [find_lo_reason]/[find_hi_reason]; do not reinstate it here. *)
let lo_rests_on store v ~decl_lo =
  if Domain.lo (Store.get store v) <= decl_lo then [] else Store.lo_reasons store v

let hi_rests_on store v ~decl_hi =
  if Domain.hi (Store.get store v) >= decl_hi then [] else Store.hi_reasons store v

(* ------------------------------------------------------ per-term snapshot *)

(* What one term of the row contributes to the pruning, decided *now* (D-0013: declared
   vs. derived) but with the expensive parts -- the [Lit.t] chain, the [Lit.t] of the
   fact, forcing a cited explanation -- left until someone actually asks
   (docs/ARCHITECTURE.md, "Deferred explanations"). Snapshotting the *decision* eagerly,
   not just cheap ints, matters here specifically because which trail entry witnesses a
   bound can change, or vanish on a backtrack, between now and whenever this is finally
   rendered: the snapshot pins down *this* row's own reason to cite, not whatever happens
   to be current later (I-X6).

   One record, where M1-T50 left three constructors:

     - [value] is the bound relevant to this term's sign -- lo for [coeff >= 0], hi for
       [coeff < 0], D-0013's own case split, the same one [term_min] makes -- as it stood
       at the moment of the pruning. For a term still at its declared bound it *is* the
       declared bound, and [Reason.lits] then materialises no literal for it, because at
       the declared bound the order encoding's statement is the constant true
       (docs/PROOF-FORMAT.md section 3). That is the whole of what the old [Snap_weaken]
       constructor said.
     - [cited] is the derivations to cite, or [[]] for "weaken this term away instead".
       It is empty in three cases that used to be two constructors and a fallback: the
       bound is declared; the bound rests on a search *decision*, which has no constraint
       id and never will (M1-T50, D-0009, D-0037) so the honest rendering is to weaken it
       away and let the D-0018 trace line carry the decision's literal; or the bookkeeping
       found nothing, which should be unreachable and weakens rather than guesses.

   The old [Snap_weaken] and [Snap_assume] had, by their own comment, "identical
   arithmetic" and "differ only in [facts_of_snaps]" -- i.e. they differed only in whether
   the fact has a literal, which is exactly what [value] vs the declared bound already
   says. Collapsing them is not a tidy-up: two constructors that must render identically
   into one place and differently into another are two chances to get the pairing wrong,
   and the pairing is what D-0026 exists to make structural. *)
type source_snap = {
  coeff : int;
  name : string;
  decl_lo : int;
  decl_hi : int;
  value : int;
  cited : Explanation.t list;
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
   [Store.remove] and a decision never removes a value, so this is a guard on the
   invariant rather than a case anything reaches today. *)
let rests_on_a_decision reasons =
  List.exists (function Explanation.Decision _ -> true | _ -> false) reasons

(* [None] only for a zero coefficient (an absent term, contributing nothing). *)
let snapshot_source store (tm : term) : source_snap option =
  if tm.coeff = 0 then None
  else
    let d = Store.get store tm.x in
    let snap value cited =
      Some
        {
          coeff = tm.coeff;
          name = Store.name store tm.x;
          decl_lo = tm.decl_lo;
          decl_hi = tm.decl_hi;
          value;
          cited;
        }
    in
    (* A bound that rests on a decision keeps its [value] and drops its [cited] -- the
       pruning does depend on the decision, so dropping the fact would make the trace
       line an unconditional claim, which is the exact I-P5 failure [int_ne] shipped
       between M1-T9 and M1-T17. M1-T50's [Snap_assume] is this line. *)
    let citable rests = if rests_on_a_decision rests then [] else rests in
    if tm.coeff >= 0 then
      let cur = Domain.lo d in
      if cur <= tm.decl_lo then snap tm.decl_lo []
      else snap cur (citable (lo_rests_on store tm.x ~decl_lo:tm.decl_lo))
    else
      let cur = Domain.hi d in
      if cur >= tm.decl_hi then snap tm.decl_hi []
      else snap cur (citable (hi_rests_on store tm.x ~decl_hi:tm.decl_hi))

(* --------------------------------------- the two halves, from one snapshot *)

(* D-0026's reason half: the bound this term contributes to "these facts imply that
   bound". Declarative data -- no literal is built here, and none can be, because
   [Reason.bound_for_coeff] takes ints and a name. [Reason.lits] is where it becomes a
   literal, and where a term still at its declared bound drops out. *)
let fact_of_snap s =
  Reason.bound_for_coeff ~coeff:s.coeff ~name:s.name ~decl_lo:s.decl_lo ~decl_hi:s.decl_hi
    s.value

(* D-0026's justification half: what this term contributes to the [Combine].

   [cited = []] weakens the term out of the row with the full declared-width axiom chain
   [Order_reason.weaken_declared] builds, scaled by [coeff]. Otherwise one [Term] per
   cited reason, all at [abs coeff] -- the scale at which the bound itself enters, since
   each hole is a fact about the same variable's same chain. Those extra terms do not
   cancel the row's coefficient the way the bound's own chain-sum does, so the [Combine]
   is no longer the self-contained numeric chain D-0013 describes; it is still a sound
   [pol] (a [pol] derives whatever it derives), and the reason it may stop closing on its
   own is precisely D-0022's, which is why [Search.rests_on_a_clause] -- reading exactly
   these summands -- then routes the conflict to its empty-clause close instead of citing
   the chain. D-0022 settled the same trade the other way round for a clause folded in as
   a bound, and for the same reason: weakening it away would erase the signal and still
   not close. *)
let summands_of_snap s =
  match s.cited with
  | [] ->
      let lits, _ =
        Order_reason.weaken_declared ~coeff:s.coeff ~name:s.name ~decl_lo:s.decl_lo
          ~decl_hi:s.decl_hi
      in
      [ Explanation.weaken lits ]
  | cited -> List.map (fun e -> Explanation.term (Checked.abs s.coeff) e) cited

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

(* Which of the three cases M1-T50 named a term is in. The constructors collapsed into
   one record (see [source_snap]), but the distinction is still a real one and
   test/unit/test_matrix.ml asserts that its scenes exercise all three, so it is a
   function rather than a shape a test has to re-derive by hand. [`Cited] implies the
   fact materialises: [cited] is non-empty only where the bound has passed its declared
   value. *)
let classify s =
  match s.cited with
  | _ :: _ -> `Cited
  | [] ->
      if Option.is_some (Reason.lit_of_fact (fact_of_snap s)) then `Assumed else `Weakened

(* -------------------------------------------- the one pairing (D-0026) *)

(* THE function that turns a snapshot list into a pruning: its reason and its
   justification, together, from one argument.

   This is D-0026's "our code already builds both -- as [facts ()] and as [expl], from one
   [row_snaps] call -- and keeps them in agreement with a comment rather than a type. The
   layering makes the split the type it already is in practice."

   What the comment used to promise was that the two [row_snaps] results at a push site
   were the same list. It was true, and it was one careless edit from being false: two
   calls at two moments would read two different trail states, which is the same trap
   [snapshot_source]'s header describes for D-0013 and the one I-X6 forbids. There is now
   nothing to keep in agreement, because there is one list, one function and one returned
   value. A reason that named a fact the justification did not use would require *this
   function* to be wrong, not a call site -- and [Store.apply]'s [check_agreement] reads
   the variable scopes back on top of that.

   The reason is built eagerly and is plain data: one fact per term, over the row's
   variable scope, with the declared ones dropping out at [Reason.lits]. The justification
   stays [Deferred]: the [Lit.t] chains and any recursive [emit] are the expensive part and
   most prunings are never asked. The thunk closes over [snaps] and [base] only -- no
   store, no live domain (I-X6).

   M2-L0/D-0043: [~concludes] is the third half-that-is-not-a-half -- WHAT this pruning
   derived, as a [Reason.fact]. It is passed in rather than computed here because this
   function serves four sites and only two of them conclude a bound: the two pushes below
   conclude exactly the bound they hand [Store.set_hi]/[set_lo], and the two conflict
   paths conclude falsity, which is not a bound, so they pass [None] and are seen doing
   it. It is NOT derivable from [snaps] -- [snaps] is what was read, the conclusion is
   what came out -- which is exactly why D-0043 puts it on [justified] and not in the
   reason. *)
let justified_of_snaps ~concludes base snaps divisor : Reason.justified =
  Reason.because ~concludes (List.map fact_of_snap snaps)
    (Explanation.deferred (fun () ->
         let summands =
           Explanation.term 1 base :: List.concat_map summands_of_snap snaps
         in
         Explanation.combine summands divisor))

(* D-0013 step 5: a conflict where this row's own new bound for [tm] contradicts a
   bound some *other* propagator instance already holds on the same variable -- add
   this row's own (already fully divided, unit-coefficient) derivation to whatever
   explanation currently holds the *opposite* bound, divisor 1. [new_bound_expl] is
   exactly what [Store.set_hi]/[set_lo] was just handed (the row's own derivation of
   the value that turned out to conflict); the store returns it back unchanged on
   [Conflict], so a caller could equally well reuse the value it already has instead
   of trusting the returned one, and this module does. *)
(* The *opposite* bound involved in a cross-row conflict, as a reason fact, for the one
   variable the two rows disagree about: this row pushed hi for a positive coefficient, so
   the bound it ran into is lo, and vice versa.

   Unconditional now, where it used to test the declared bound and answer [None]: the test
   moved into [Reason.lit_of_fact], where it is made once for every producer in [lib/]. It
   renders to exactly the same literal or to none at all, and the case
   [explain_cross_conflict] refuses outright is the *derivation* being declared, which is
   a different test on a different value (there is nothing to cite, as opposed to nothing
   to state). *)
let opposite_bound_fact store (tm : term) =
  let name = Store.name store tm.x in
  let d = Store.get store tm.x in
  if tm.coeff > 0 then Reason.at_least ~name ~decl:tm.decl_lo (Domain.lo d)
  else Reason.at_most ~name ~decl:tm.decl_hi (Domain.hi d)

(* The derivations the *opposite* bound rests on -- the one this row's new bound ran
   into -- read HERE, at the moment of the pruning, and handed to
   [explain_cross_conflict] below as a plain value.

   Note which bound this reads, because it is the mirror of [snapshot_source]'s: a
   positive coefficient means this row pushed [tm]'s UPPER bound, so the bound it ran
   into is the lower one. O(1) as of M2-T8 ([Store.lo_support]), so the old argument
   that a trail scan per cross-row conflict was not a hot path no longer has to be
   made. *)
let opposite_rests_on store (tm : term) =
  if tm.coeff > 0 then lo_rests_on store tm.x ~decl_lo:tm.decl_lo
  else hi_rests_on store tm.x ~decl_hi:tm.decl_hi

(* docs/DECISIONS.md D-0018 and invariant I-X6 are explicit that a [Deferred] thunk must
   close over a *snapshot* and never read live store state: the whole reason the trace can
   be written later, when a branch fails, rather than eagerly at every pruning, is that a
   reason forced late still renders the derivation as of the moment it was made. This
   function used to call [find_lo_reason]/[find_hi_reason] from inside the thunk, i.e. it
   looked at whatever trail entry happened to witness the opposite bound at *force* time.
   It was harmless in practice only because search forces a conflict's explanation
   immediately; under conflict analysis (M2-T3), or under any change that defers the
   rendering past a backtrack, it would have cited a reason that no longer holds -- and
   the symptom would have been a rejected line somewhere else entirely, which is exactly
   the trap D-0018 quotes from GCS. M1-T13 hoisted the lookup out of the thunk and it has
   stayed out; only building the [Combine] is deferred.

   It takes [~opposite] and NOT the store, which is the point of the signature and not a
   tidy-up. M1-T13's hoist left a [store] in scope one line above a thunk that must not
   read it, so the discipline was one careless edit from being undone and *nothing in the
   suite could see that edit*: measured 2026-09-17, moving the two lines above back inside
   the thunk reddens **zero** checks across every unit binary, keeps all 34 models green
   and leaves all 102 proof artefacts byte-identical. With no store here there is nothing
   live to read, which is how lib/core/reason.ml discharges the same obligation on the
   reason half -- by the type rather than by a reviewer noticing. Putting the store back
   is now a visible change to a signature, and
   [test_prop.ml]'s [test_ix6_cross_conflict_snapshot] is the check that sees it: it
   forces one cross-row conflict at two moments with another row taking over the cited
   bound in between, and it fires on the *derivation being wrong*, not on a crash.

   WHY NO MODEL COVERS THIS, measured 2026-09-17. The only route into this path is a row
   that names the same variable twice (test_matrix.ml's white-box cross-row scene:
   `2d - d <= -4`, where term 0 pushes hi and term 1 then pushes lo from the pre-push
   [mins] and crosses it). Two separate instances meeting in a third row is reported as
   that row's own slack instead. And a repeated variable cannot arrive from the CLI:
   lib/flatzinc/compile.ml's [normalise_terms] merges duplicate coefficients once, for
   both the .opb row and [Linear.make], so `int_lin_le([2,-1],[d,d],-4)` reaches this
   module as `d <= -4` and refutes through the row's own slack -- confirmed by running
   it, whose proof is a single [pol]. So this function is reachable only from a library
   caller today, which is the other half of why breaking it moved no artefact, and it is
   why a test/models/ instance cannot stand in for the unit test above. *)
let explain_cross_conflict ~opposite new_bound_expl =
  Explanation.deferred (fun () ->
      match opposite with
      | _ :: _ ->
          (* One [Term] per reason the opposing bound rests on -- the entry that moved
             it, plus any hole its settle walked over (M1-T44, [Store.lo_reasons]). *)
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

(* Every push below hands [Store] ONE value carrying both halves of docs/DECISIONS.md
   D-0018: the justification (the [pol] the checker is shown when a derivation is
   demanded) and the reason (the bound facts the trace line's clause negates). They come
   from one [justified_of_snaps] call over one [row_snaps] result, so they cannot drift
   apart -- and as of M2-T8 there is no signature here that could carry one without the
   other (I-P4 and I-P5 are one obligation, D-0026).

   Both conflict paths build their [Store.conflict] from a [Reason.justified] too, for
   D-0018 point 3: a
   conflict has no trail entry, so its own reason line carries the facts itself. M2-T7
   turned that from a [Store.record_conflict_facts] call immediately before the return
   into a field of the returned value, which removes the window between arming the facts
   and returning the conflict that the old one-shot slot's comment had to argue about.
   Neither path names this instance's id: [Store.conflict] stamps whoever the engine said
   was running. *)
let propagate t store =
  let mins = List.map (fun tm -> term_min store tm) t.terms in
  let total_min = Checked.sum mins in
  let slack = Checked.sub t.rhs total_min in
  if slack < 0 then
    let snaps = row_snaps store t.terms ~exclude:None in
    Propagator.Conflict
      (Store.conflict store
         (justified_of_snaps ~concludes:None (base_explanation t) snaps 1))
  else
    let result = ref Propagator.Fixpoint in
    let conflict = ref None in
    (* [tm : term] and [idx]'s [tm] below are annotated because [source_snap] is declared
       after [term] and also has a [coeff] field, so OCaml's field disambiguation picks
       [source_snap] for a bare [tm.coeff]. *)
    let cross_conflict (tm : term) snaps expl =
      (* The row's own reason, plus the opposing bound this new one ran into. Both halves
         are snapshotted here, not inside the thunk, for the reason
         [explain_cross_conflict] above spells out. *)
      conflict :=
        Some
          (Store.conflict store
             (Reason.because ~concludes:None
                (List.map fact_of_snap snaps @ [ opposite_bound_fact store tm ])
                (explain_cross_conflict ~opposite:(opposite_rests_on store tm) expl)))
    in
    List.iteri
      (fun idx ((tm : term), m) ->
        if Option.is_none !conflict && tm.coeff <> 0 then
          let max_term = Checked.add m slack in
          let d = Store.get store tm.x in
          if tm.coeff > 0 then (
            let new_hi = floordiv max_term tm.coeff in
            if new_hi < Domain.hi d then
              let snaps = row_snaps store t.terms ~exclude:(Some idx) in
              let concludes =
                Some
                  (Reason.at_most ~name:(Store.name store tm.x) ~decl:tm.decl_hi new_hi)
              in
              let j = justified_of_snaps ~concludes (base_explanation t) snaps tm.coeff in
              match Store.set_hi store tm.x new_hi j with
              | Store.Conflict _ -> cross_conflict tm snaps j.Reason.justification
              | Store.Changed | Store.Unchanged -> ())
          else
            let new_lo = ceildiv max_term tm.coeff in
            if new_lo > Domain.lo d then
              let snaps = row_snaps store t.terms ~exclude:(Some idx) in
              let concludes =
                Some
                  (Reason.at_least ~name:(Store.name store tm.x) ~decl:tm.decl_lo new_lo)
              in
              let j =
                justified_of_snaps ~concludes (base_explanation t) snaps
                  (Checked.neg tm.coeff)
              in
              match Store.set_lo store tm.x new_lo j with
              | Store.Conflict _ -> cross_conflict tm snaps j.Reason.justification
              | Store.Changed | Store.Unchanged -> ())
      (List.combine t.terms mins);
    (match !conflict with Some c -> result := Propagator.Conflict c | None -> ());
    !result
