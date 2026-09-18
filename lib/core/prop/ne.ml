(* int_lin_ne: sum_i a_i * x_i <> c, and its two-variable specialisation int_ne
   (x <> y), over integer variables with possibly negative coefficients.

   Consistency level: VALUE (docs/SPEC.md 3.2, docs/PROOF-FORMAT.md section 4's
   `int_ne` row). The algorithm below is the textbook one for a disequality: do
   nothing while two or more terms are unfixed; when exactly one is unfixed, remove
   from it the single value that would make the sum equal [c]; when none is, report
   a conflict iff the sum *is* [c].

   That is in fact *domain* consistency for a disequality -- with two terms still
   unfixed every remaining value of every variable has a support, because the other
   unfixed term can always be moved off the bad total -- but this module declares
   VALUE, which is what PROOF-FORMAT section 4 records for `int_ne` and what
   [Propagator.consistency] is read for downstream. Declaring the weaker level is
   conservative in the only direction that matters: the level bounds what an
   explanation is allowed to claim (SPEC 3.2), and nothing here claims more than
   "these fixed values are jointly impossible". (docs/GLOSSARY.md defines "bounds"
   and "domain" consistent but not "value"; reported, not invented here.)

   Shape: this follows lib/core/prop/linear.ml, the reference propagator -- compute
   once, snapshot the decision eagerly and build the literals lazily behind
   [Explanation.deferred], one pass to fixpoint, [consistency] declared above. The
   one structural difference from [Linear] is deliberate, and the next paragraph is
   why: this propagator cites no row id, because its justification is a [rup] whose
   target is self-contained.

   D-0011 (one propagator instance, one model row) is satisfied vacuously and it is
   worth being explicit about why, since this is the first propagator in the tree
   that is not a [Linear]. D-0011's hazard was [Explanation.Trivial], which meant
   "whatever ctx.model_id points at" and is unresolvable once it is on the trail with
   no propagator identity attached. **[Explanation.Trivial] no longer exists** (M1-T31/M1-T50,
   D-0037): a decision now carries [Decision of Lit.t] and [Linear.make]'s row id is
   required, so the ambient row is unrepresentable rather than merely unused. Nothing in
   this module ever built [Trivial], or
   [Model_row], or any constructor that names a constraint: every explanation it
   produces is a [Clause] that states its own content in full. So there is nothing to
   route and nothing to get wrong -- which is also why [make] takes no [?row_id],
   unlike [Linear.make]. An unused id parameter would be an invitation to believe it
   was load-bearing.

   ---------------------------------------------------------------------------
   Propagation
   ---------------------------------------------------------------------------

     - two or more terms unfixed        -> Fixpoint, nothing can be inferred
     - exactly one term [j] unfixed     -> the sum equals [c] only if
                                             a_j * x_j = c - sum_{i<>j} a_i v_i
                                           so if that right-hand side is divisible by
                                           a_j and the quotient [w] is still in x_j's
                                           domain, remove [w]; otherwise nothing
     - every term fixed                 -> Conflict iff the sum is exactly [c]

   Zero coefficients are dropped at [make] time rather than skipped at propagate
   time (where [Linear] skips them): a term with coefficient 0 is not part of the
   constraint at all, so it must not count towards "how many terms are unfixed", must
   not appear in an explanation, and is pure churn in [vars] -- the engine would wake
   this propagator every time an irrelevant variable moved.

   ---------------------------------------------------------------------------
   Justification -- one [rup], and what it says
   ---------------------------------------------------------------------------

   docs/PROOF-FORMAT.md section 4 nominates [rup] over direct-encoding literals for
   `int_ne`. This module emits a [rup], and over *order*-encoding literals: see
   [Encoding.ne_clause_lits]'s header (lib/proof/encoding.ml) for why the direct
   encoding is not needed to say "x <> v" inside a clause, only to say it as a single
   literal. Checked against the checker rather than argued; test/unit/test_prop.ml runs
   every shape below through it.

   Every explanation this module builds -- pruning and conflict alike -- is the same
   clause:

       for a set of (variable, value) pairs whose sum is exactly [c],
           NOT (x_1 = v_1  /\  ...  /\  x_n = v_n)
       written out as       (x_1 <> v_1)  \/  ...  \/  (x_n <> v_n)
       and each disjunct as ~[x_i >= v_i] \/ [x_i >= v_i + 1]

   For a *conflict* the pairs are every term at its fixed value, and the clause says
   "this total is forbidden". For a *pruning* of [w] from x_j the pairs are the other
   terms at their fixed values plus (x_j, w) -- so the clause is D-0018's trace-line
   shape, "the claim, disjoined with the negation of its reason's literals", with the
   claim being x_j <> w. The two cases are literally the same function of the same
   data, which is not a coincidence: the reason a value is prunable is that the tuple
   it would complete is the tuple that conflicts.

   Three properties of that clause are worth stating, because each one is a thing a
   later change could quietly break:

   1. It is *globally valid* -- true in every solution of the model, not merely under
      the current decisions -- because it is exactly the model constraint instantiated
      at one tuple. So it is sound to emit at any proof level and never has to be
      guarded by, or wiped with, a decision.

   2. It is *reverse unit propagation* against the two rows [Encoding.add_int_lin_ne]
      posts, in at most two propagation steps: negating it asserts every x_i = v_i as
      units, which makes the sum numerically [c], which forces the selector Boolean b
      true through row A and then falsifies row B. It does not need the checker to
      replay a multi-row bounds fixpoint, which is the thing D-0012/D-0018 record
      veripb cannot do.

   3. It contains *no* direct-encoding literal, so it does not depend on anything
      having been introduced with [red] earlier in the proof, and in particular does
      not depend on the audit (I-X2) retiring anything afterwards.

   What this explanation is *not* is a statement that entails the pruning on its own:
   it says "not all of these values together", not "x_j <> w". That is the correct
   and only honest shape for a clausal reason, and it is what D-0018 asks for, but it
   means an explanation from this module must not be dropped into a cutting-planes
   sum as though it were a bound derivation. [Linear]'s *citing* path does exactly
   that when it cites the trail entry that last moved a bound (lib/core/prop/linear.ml's
   [lo_rests_on], over [Store.lo_reasons]) -- and this propagator *can* move a bound, since
   removing a value at [lo] or [hi] shrinks the interval.

   M1-T17 note on that composition: the [pol] it produces is *sound* (a [pol] is sound
   whatever it cites; it simply derives something valid that is not the bound the row's
   own slack argument claimed), and what was actually broken was downstream --
   lib/core/search.ml's root arm cited that [pol] to [conclusion UNSAT] as though it
   were a contradiction, which veripb rejects. The rejection is worded "The constraint
   with ID <n> is not contradicting, as specified by the hint" (3.0.2, the checker of
   record); test/unit/test_random.ml matches on it.
   [Search.rests_on_a_clause] now recognises a derivation that rests on a clause and
   closes such a root conflict the D-0018 way, over the trace, so nothing this module
   produces is cited as a contradiction it does not establish. Making the citing path
   weaken rather than cite is still open; see the M1-T17 hand-back for the measurement
   of what that costs and which pinned check it moves.

   ---------------------------------------------------------------------------
   Snapshotting
   ---------------------------------------------------------------------------

   The values in the clause are snapshotted *eagerly* into [pairs] and only the
   [Lit.t] list is built lazily. D-0018 is explicit that a [Deferred] thunk reading
   live store state instead of a snapshot silently breaks the trace: an explanation
   forced later must still render the derivation as of the moment it was made, and by
   then the store may have been narrowed further or backtracked. Snapshotting ints is
   cheap; it is the clause construction that is deferred.

   ---------------------------------------------------------------------------
   Arithmetic (roadmap M1-T23)
   ---------------------------------------------------------------------------

   [sum_of], the [rhs - sum] that gives the missing amount, and the divisibility test
   and quotient that turn it into a value all go through [Checked]
   (lib/core/checked.ml), which raises rather than wrapping. The stake is the same one
   [Linear]'s header states and is if anything sharper here, because a wrapped
   [sum_of] does not merely decline to prune: it can make an unrelated total look
   exactly like [rhs] and remove a value that is in a solution, while
   [Encoding.add_int_lin_ne] builds the A/B rows' big-M constants from the same
   wrapped span. [Checked.rem] also answers min_int mod -1 directly, which is the one
   input [Stdlib.mod] is not guaranteed to survive and which [rest mod tm.coeff] can
   reach for a coefficient of -1 -- which is every [int_ne]. *)

module Encoding = Baguette_proof.Encoding
module Lit = Baguette_proof.Lit

(* One term of the sum. [name] and the declared bounds are frozen at [make] time:
   the name because nothing can rename a variable and the deferred thunk should not
   have to hold the store to find it, the bounds because docs/DECISIONS.md D-0010
   requires it -- [Encoding.ne_clause_lits] drops the constant halves of its clause
   against the *declared* domain, which the store stops reporting the moment anything
   narrows the variable. Coefficients here are always non-zero; see [make]. *)
type term = { coeff : int; x : Var.t; name : string; decl_lo : int; decl_hi : int }
type t = { terms : term list; rhs : int }

let name = "int_lin_ne"
let consistency = Propagator.Value

(* [raw_terms] are (coefficient, variable) pairs and [rhs] the value the sum must
   avoid. A variable may appear more than once -- callers that care about propagation
   strength should merge duplicates first, as lib/flatzinc/compile.ml's
   [normalise_terms] does for every row it posts, because two occurrences of the same
   unfixed variable read here as two unfixed terms and this propagator then declines
   to infer anything. Declining is sound, just weaker.

   Reads each variable's domain out of the store, so it must be called before
   anything has narrowed it (the same requirement, for the same D-0010 reason, that
   [Linear.make]'s header states). *)
let make store raw_terms rhs =
  let terms =
    List.filter_map
      (fun (coeff, x) ->
        if coeff = 0 then None
        else
          let d = Store.get store x in
          Some
            {
              coeff;
              x;
              name = Store.name store x;
              decl_lo = Domain.lo d;
              decl_hi = Domain.hi d;
            })
      raw_terms
  in
  { terms; rhs }

let vars t = List.map (fun tm -> tm.x) t.terms

(* ------------------------------------------------------------------ explanations *)

(* "not all of these variables take these values at once", as a clause over the order
   encoding. [pairs] must be a snapshot: see the module header. *)
let nogood pairs =
  Explanation.clause
    (List.concat_map
       (fun (tm, v) ->
         Encoding.ne_clause_lits ~name:tm.name ~decl_lo:tm.decl_lo ~decl_hi:tm.decl_hi v)
       pairs)

(* The clause is short, but building it still allocates and most prunings are never
   asked for a reason (docs/ARCHITECTURE.md, "Deferred explanations"), so it goes
   behind a thunk over the already-snapshotted values. *)
let explain pairs = Explanation.deferred (fun () -> nogood pairs)

(* ---------------------------------------------------------------------------
   The other projection of the same pruning: its bound facts (docs/DECISIONS.md
   D-0018/D-0021, and [Store.entry]'s [facts])
   ---------------------------------------------------------------------------

   Removing a value that sits at [lo] or at [hi] shrinks the interval, so it *is* a
   bound move, so lib/core/trace.ml writes a line for it:

       rup <the order literal the new bound establishes> \/ ~<fact> ... >= 1 ;

   Until M1-T17 this module pruned through a mutator that recorded no facts at all,
   and that line came out with an empty tail -- claiming the new bound
   unconditionally. On a satisfiable model it is not merely unprovable, it is false,
   and veripb rejects it.

   The facts are the same data as the clause and are stated as the *positive*
   literals [Trace] will negate, so that the line it builds is exactly the nogood
   [explain] would have produced for the same pairs:

     - every OTHER term is fixed at [v], which is two order facts, [x >= v] and
       [x <= v]. Negated they are [Encoding.ne_clause_lits]'s two halves, i.e.
       "x <> v", and the constant halves drop at the declared bounds for the same
       reason they drop there (docs/PROOF-FORMAT.md section 3).

     - the PRUNED term contributes the bound the removal is about to move, and only
       that one: with [w] at [lo] the fact is [x >= w] and [Trace]'s own claim is
       [x >= w+1], which are the two halves of "x <> w" between them. Stating [x <= w]
       as well would be stating something false (the domain is wider than that) and
       would duplicate the claim's own literal in the clause.

     - a removal strictly inside the interval moves no bound, gets no line at all
       (lib/core/trace.ml's [claims]), and contributes nothing here. An order literal
       cannot state a hole; that is D-0019 point 3's test for when the direct encoding
       is forced, and M1 does not reach it.

   [d] is the pruned variable's domain as it stands *now*, before the removal, and is
   read here rather than inside the thunk: I-X6, the same snapshot discipline the
   values in [pairs] already follow. *)
(* M2-T8/D-0026: these are [Reason.fact]s, not [Lit.t]s, and the "drop it at the declared
   bound" test they used to make for themselves now lives once, in [Reason.lit_of_fact].
   Nothing else about them changed: the same facts in the same order, so the same tail on
   the same line. *)
let moved_bound_fact tm w d =
  if w = Domain.lo d then [ Reason.at_least ~name:tm.name ~decl:tm.decl_lo w ]
  else if w = Domain.hi d then [ Reason.at_most ~name:tm.name ~decl:tm.decl_hi w ]
  else []

let pruning_reason tm w d fixed_others =
  moved_bound_fact tm w d
  @ List.concat_map
      (fun (o, v) -> Reason.fixed_at ~name:o.name ~decl_lo:o.decl_lo ~decl_hi:o.decl_hi v)
      fixed_others

(* The two halves of one pruning, from one snapshot, in one function -- D-0026, and the
   same shape [Linear.justified_of_snaps] has. The justification's clause is over
   [(tm, w) :: fixed_others] (the pruned term fixed at [w] as well, which is what makes it
   a nogood) and the reason is over the bound [w] is about to move plus the others; the
   two differ exactly there and by construction, not by two call sites agreeing. *)
let justified_pruning ~concludes tm w d fixed_others : Reason.justified =
  Reason.because ~concludes
    (pruning_reason tm w d fixed_others)
    (explain ((tm, w) :: fixed_others))

(* D-0043's conclusion for a *value removal*, which is the one pruning shape whose claim
   is not always a bound.

   [Store.remove] does one of two things (I-D2, and [Domain.classify] reports them as
   disjoint): removing a value AT a bound settles and tightens that bound, and removing
   an interior value punches a hole. The first concludes the bound it settled to -- which
   is exactly the claim lib/core/trace.ml writes for it, a single order literal with the
   holes it stepped over as [settled_over]. The second concludes `x <> w`, a TWO-literal
   clause over the order encoding ([Trace.hole_clause]), and that is not a [Reason.fact]
   in any direction: it is [None], and reason.ml's header states that this [None] is
   about the type and not about a gap in the solver's own partition.

   The settled bound is walked out here rather than recovered from a second
   [Domain.remove] call: that call allocates a hole bitset whose size is
   width-proportional (D-0028), and running it twice per pruning to read one number back
   is the kind of cost this project measures rather than pays. The walk is the same one
   [Trace.holes_above]/[holes_below] do over the same domain, so the number this states
   and the number the trace line claims come from one rule. *)
let removal_conclusion tm w d =
  if w = Domain.lo d then (
    let v = ref (w + 1) in
    while !v <= Domain.hi d && Domain.is_hole d !v do
      incr v
    done;
    Some (Reason.at_least ~name:tm.name ~decl:tm.decl_lo !v))
  else if w = Domain.hi d then (
    let v = ref (w - 1) in
    while !v >= Domain.lo d && Domain.is_hole d !v do
      decr v
    done;
    Some (Reason.at_most ~name:tm.name ~decl:tm.decl_hi !v))
  else None

(* ------------------------------------------------------------------- propagation *)

let fixed_at store tm = Domain.value (Store.get store tm.x)

(* Every term paired with its current fixed value, or [None] if some term is unfixed.
   Only called once every term is known fixed. *)
let all_pairs store terms =
  List.map (fun tm -> (tm, Domain.lo (Store.get store tm.x))) terms

let sum_of store terms =
  List.fold_left
    (fun acc tm ->
      Checked.add acc (Checked.mul tm.coeff (Domain.lo (Store.get store tm.x))))
    0 terms

(* The terms other than the one at [idx] -- by position, not by variable, since a
   variable may legitimately appear twice and each occurrence is its own term. Same
   reasoning as [Linear.others_except]. *)
let others_except terms idx = List.filteri (fun i _ -> i <> idx) terms

(* Positions of the terms that are not yet fixed, at most [limit] of them: the caller
   only ever needs to know "none", "exactly one and which", or "two or more". *)
let unfixed_positions store terms ~limit =
  let rec go i acc = function
    | [] -> List.rev acc
    | tm :: rest ->
        if List.length acc >= limit then List.rev acc
        else if Option.is_none (fixed_at store tm) then go (i + 1) (i :: acc) rest
        else go (i + 1) acc rest
  in
  go 0 [] terms

let propagate t store =
  match unfixed_positions store t.terms ~limit:2 with
  | _ :: _ :: _ -> Propagator.Fixpoint
  | [] ->
      (* I-P3, checking: with everything fixed, fail iff the constraint is violated. *)
      if sum_of store t.terms <> t.rhs then Propagator.Fixpoint
      else
        (* [Reason.none], deliberately and now visibly: an all-fixed violation records no
           bound facts, so [Trace.conflict_line] writes no line for it. The clause IS the
           explanation here (every variable is fixed, so the nogood is the whole story),
           and a reason line restating it would be a second copy of the same claim. Before
           M2-T8 this was the default argument and said nothing. *)
        Propagator.Conflict
          (Store.conflict store
             (Reason.because ~concludes:None Reason.none
                (explain (all_pairs store t.terms))))
  | [ idx ] -> (
      let tm = List.nth t.terms idx in
      let others = others_except t.terms idx in
      let rest = Checked.sub t.rhs (sum_of store others) in
      (* [tm.coeff] is non-zero by construction ([make] drops zero terms), so this
         division is well defined. A non-zero remainder means a_j * x_j can never hit
         the missing amount for any integer x_j: nothing to prune. The remainder is
         zero on the branch below, so [floordiv] is exact division there and its
         rounding never comes into play -- it is used for its min_int / -1 guard. *)
      if Checked.rem rest tm.coeff <> 0 then Propagator.Fixpoint
      else
        let w = Checked.floordiv rest tm.coeff in
        let d = Store.get store tm.x in
        if not (Domain.mem d w) then Propagator.Fixpoint
        else
          let fixed_others =
            List.map (fun o -> (o, Domain.lo (Store.get store o.x))) others
          in
          let concludes = removal_conclusion tm w d in
          match
            Store.remove store tm.x w (justified_pruning ~concludes tm w d fixed_others)
          with
          | Store.Conflict e ->
              (* Unreachable at the interface: [tm] is unfixed, so its domain holds at
                 least two values and removing one cannot empty it. Handled rather
                 than asserted so that a future [Domain] change cannot turn a silent
                 wrong answer into the failure mode -- and the explanation handed back
                 is the one that caused it, exactly as [Store.apply] returns it. *)
              Propagator.Conflict e
          | Store.Changed | Store.Unchanged ->
              (* [Unchanged] happens when [Domain.remove] declines to allocate a hole
                 bitset for an enormous span (lib/core/domain.ml, [max_hole_span]).
                 Declining to prune is sound and no explanation is emitted for a
                 pruning that did not happen, so I-P4 is not at stake; the propagator
                 is simply weaker there. Re-running finds the same thing and still
                 changes nothing, so I-P3 holds either way. *)
              Propagator.Fixpoint)

(* ---------------------------------------------------------------------------
   int_ne: x <> y.

   The two-variable specialisation, [1*x + (-1)*y <> 0], exactly as [Int_le] is a
   specialisation of [Linear] over [1*x + (-1)*y <= 0] -- read that module's header
   (lib/core/prop/int_le.ml) for the fuller case for reuse over a hand-written
   two-variable version. It is the same argument here and it is stronger, because the
   hand-written version of a disequality has a genuinely error-prone part: which of
   the two variables is the one being pruned, and which value of the *other* is the
   reason. Having one implementation means one place where that can be wrong.

   It lives in this file rather than its own because lib/core/dune is
   orchestrator-owned and M1-T9's claim is this one module; [Int_le]/[Int_lt] are
   separate files only because they were written when a file per builtin was free.
   Justification shape: identical to [int_lin_ne]'s -- the same clause over the same
   two rows [Encoding.add_int_lin_ne] posts for [x - y <> 0]. *)
module Int_ne = struct
  type nonrec t = t

  let name = "int_ne"
  let consistency = Propagator.Value
  let make store x y = make store [ (1, x); (-1, y) ] 0
  let vars = vars
  let propagate = propagate
end
