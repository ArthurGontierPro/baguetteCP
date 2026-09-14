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

   [make] also takes [?row_id], the id (a Baguette_proof.Writer.cid, i.e. plain [int] --
   this module has no reason to depend on [Baguette_proof.Writer] just for its type) the
   .opb already gave this instance's own row. D-0011: one instance justifies against
   exactly one row, and that row is posted to the encoding before any propagator ever
   runs, so the id is available at construction time; passing it in beats resolving it
   later through an ambient [Justify.ctx], which is exactly the trap D-0013 hit (see
   [Explanation.Model_row]'s header in lib/core/explanation.ml). It is optional, not
   required, only because no caller in this checkout wires a model to the engine yet
   (D-0010's own note, still true) -- every caller that *has* an id should always pass
   it; see [base_explanation] below for what omitting it costs.

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
   opposite bounds on the same variable, added". *)

module Lit = Baguette_proof.Lit

(* One term of the sum: coefficient (may be negative or zero; zero terms are inert and
   never generate a bound or appear in an explanation), the variable it multiplies, and
   the variable's *declared* domain, frozen at [make] time (D-0010: the offset an
   explanation needs is the declared bound, which the store no longer holds once this or
   any other propagator has narrowed the domain). *)
type term = { coeff : int; x : Var.t; decl_lo : int; decl_hi : int }
type t = { terms : term list; rhs : int; row_id : int option }

let name = "int_lin_le"
let consistency = Propagator.Bounds

(* [row_id] is optional -- and should always be given once a caller has one to give
   (see the module header) -- purely so this stays source-compatible with callers
   that have no id to hand yet (nothing wires the model to the engine before M1-T11,
   docs/DECISIONS.md D-0010's own note). Without one, the base of every [Combine]
   this instance builds falls back to [Explanation.trivial], which -- exactly the
   ambiguity D-0013's own header on [Explanation.Model_row] describes -- only
   resolves correctly for a caller that never combines this instance's explanations
   with another instance's inside one [Combine] and controls [ctx.model_id] itself
   for the single row in play. *)
let make ?row_id store raw_terms rhs =
  let terms =
    List.map
      (fun (coeff, x) ->
        let d = Store.get store x in
        { coeff; x; decl_lo = Domain.lo d; decl_hi = Domain.hi d })
      raw_terms
  in
  { terms; rhs; row_id }

let base_explanation t =
  match t.row_id with Some id -> Explanation.model_row id | None -> Explanation.trivial

let vars t = List.map (fun tm -> tm.x) t.terms

(* -------------------------------------------------------------- integer division *)

(* [Stdlib.(/)] truncates toward zero, which is the wrong rounding for a negative
   dividend or divisor: bounds propagation needs floor/ceil of the exact rational
   quotient regardless of sign. [b] is never zero here (callers only apply these to
   nonzero coefficients). *)
let floordiv a b =
  let q = a / b and r = a mod b in
  if r <> 0 && r < 0 <> (b < 0) then q - 1 else q

let ceildiv a b = -(floordiv (-a) b)

(* ------------------------------------------------------------------- min/max terms *)

(* The smallest value [a * x] can currently take, given [x]'s domain. *)
let term_min store (tm : term) =
  let d = Store.get store tm.x in
  if tm.coeff >= 0 then tm.coeff * Domain.lo d else tm.coeff * Domain.hi d

(* -------------------------------------------------------- locating an earlier reason *)

(* The most recent trail entry for [v] that tightened its *lower* bound to (at least)
   its current value, or [None] if [v]'s current lo is still its declared one.

   Domain lo only ever increases (I-D3/I-D2), so the newest entry for [v] whose [old]
   domain had a strictly smaller lo than the current one is exactly the entry that
   pushed lo to where it now sits: every entry for [v] *more recent* than it (already
   skipped, scanning newest-first) left lo unchanged, or it would have been the one
   found instead. *)
let find_lo_reason store v ~decl_lo =
  let cur = Domain.lo (Store.get store v) in
  if cur <= decl_lo then None
  else
    let rec scan = function
      | [] -> None
      | (e : Store.entry) :: rest ->
          if Var.equal e.var v && Domain.lo e.old < cur then
            Some (Store.explanation store e)
          else scan rest
    in
    scan (Store.trail_entries store)

(* Symmetric for the upper bound: the entry that pushed hi down to its current value. *)
let find_hi_reason store v ~decl_hi =
  let cur = Domain.hi (Store.get store v) in
  if cur >= decl_hi then None
  else
    let rec scan = function
      | [] -> None
      | (e : Store.entry) :: rest ->
          if Var.equal e.var v && Domain.hi e.old > cur then
            Some (Store.explanation store e)
          else scan rest
    in
    scan (Store.trail_entries store)

(* ------------------------------------------------------ per-term summand, snapshotted *)

(* What a term contributes to a [Combine], decided *now* (D-0013: declared vs. derived)
   but with the expensive parts -- the [Lit.t] chain, or forcing the cited explanation
   -- left for [summand_of_snap] to build only when the whole explanation is actually
   forced (docs/ARCHITECTURE.md, "Deferred explanations"). Snapshotting the *decision*
   eagerly, not just cheap ints, matters here specifically because which trail entry
   currently witnesses a bound can change (or vanish on backtrack) between now and
   whenever this explanation is finally forced -- the snapshot pins down *this* row's
   own reason to cite, not whatever happens to be current later. *)
type source_snap =
  | Snap_weaken of { coeff : int; name : string; decl_lo : int; decl_hi : int }
  | Snap_cite of { coeff : int; expl : Explanation.t }

(* [None] only for a zero coefficient (an absent term, contributing nothing). Otherwise
   picks the bound relevant to this term's sign (D-0013's own case split, matching
   [term_min]'s), and within it, declared (weaken) vs. derived (cite): see the module
   header. The defensive branches below (falling back to weakening when the bound is
   tighter than declared but no trail entry can be found) should be unreachable --
   I-D2/I-D3 guarantee a bound only tightens via a recorded entry -- but weakening is
   still *sound* even if this bookkeeping is ever wrong, just weaker than it should be,
   so a defensive fallback here fails soft rather than emitting something unsound. *)
let snapshot_source store (tm : term) : source_snap option =
  if tm.coeff = 0 then None
  else if tm.coeff >= 0 then
    let cur = Domain.lo (Store.get store tm.x) in
    if cur <= tm.decl_lo then
      Some
        (Snap_weaken
           {
             coeff = tm.coeff;
             name = Store.name store tm.x;
             decl_lo = tm.decl_lo;
             decl_hi = tm.decl_hi;
           })
    else
      match find_lo_reason store tm.x ~decl_lo:tm.decl_lo with
      | Some expl -> Some (Snap_cite { coeff = tm.coeff; expl })
      | None ->
          Some
            (Snap_weaken
               {
                 coeff = tm.coeff;
                 name = Store.name store tm.x;
                 decl_lo = tm.decl_lo;
                 decl_hi = tm.decl_hi;
               })
  else
    let cur = Domain.hi (Store.get store tm.x) in
    if cur >= tm.decl_hi then
      Some
        (Snap_weaken
           {
             coeff = tm.coeff;
             name = Store.name store tm.x;
             decl_lo = tm.decl_lo;
             decl_hi = tm.decl_hi;
           })
    else
      match find_hi_reason store tm.x ~decl_hi:tm.decl_hi with
      | Some expl -> Some (Snap_cite { coeff = tm.coeff; expl })
      | None ->
          Some
            (Snap_weaken
               {
                 coeff = tm.coeff;
                 name = Store.name store tm.x;
                 decl_lo = tm.decl_lo;
                 decl_hi = tm.decl_hi;
               })

let summand_of_snap = function
  | Snap_weaken { coeff; name; decl_lo; decl_hi } ->
      let lits, _ = Order_reason.weaken_declared ~coeff ~name ~decl_lo ~decl_hi in
      Explanation.weaken lits
  | Snap_cite { coeff; expl } -> Explanation.term (abs coeff) expl

(* All terms except the one at [idx] (by position, not value - a variable could in
   principle appear twice, and each occurrence is excluded independently). *)
let others_except terms idx = List.filteri (fun i _ -> i <> idx) terms

(* The [Combine] that justifies tightening the term at [idx] (or, for a row-level
   conflict, justifies the row's own contradiction, when [idx] is [None] and every
   term is "other"). Cheap eagerly (the snapshot decision above); the [Lit.t] chain
   and any recursive [emit] happen only once [Justify.emit] actually forces this. *)
let explain_row store base terms ~exclude divisor =
  let others = match exclude with None -> terms | Some idx -> others_except terms idx in
  let snaps = List.filter_map (snapshot_source store) others in
  Explanation.deferred (fun () ->
      let summands = Explanation.term 1 base :: List.map summand_of_snap snaps in
      Explanation.combine summands divisor)

(* D-0013 step 5: a conflict where this row's own new bound for [tm] contradicts a
   bound some *other* propagator instance already holds on the same variable -- add
   this row's own (already fully divided, unit-coefficient) derivation to whatever
   explanation currently holds the *opposite* bound, divisor 1. [new_bound_expl] is
   exactly what [Store.set_hi]/[set_lo] was just handed (the row's own derivation of
   the value that turned out to conflict); the store returns it back unchanged on
   [Conflict], so a caller could equally well reuse the value it already has instead
   of trusting the returned one, and this module does. *)
let explain_cross_conflict store (tm : term) new_bound_expl =
  Explanation.deferred (fun () ->
      let opposite =
        if tm.coeff > 0 then find_lo_reason store tm.x ~decl_lo:tm.decl_lo
        else find_hi_reason store tm.x ~decl_hi:tm.decl_hi
      in
      match opposite with
      | Some opposite_expl ->
          Explanation.combine
            [ Explanation.term 1 new_bound_expl; Explanation.term 1 opposite_expl ]
            1
      | None ->
          (* The opposite bound is still declared, yet contradicts a fresh derivation
             from this row alone -- that would already have been this row's own
             slack < 0 conflict before any per-term push was attempted. Believed
             unreachable at bounds consistency (I-D2/I-D3); fail loudly rather than
             emit an explanation that does not actually derive a contradiction. *)
          invalid_arg
            "Linear.explain_cross_conflict: opposite bound is declared, not derived -- \
             this should have been caught as this row's own slack < 0 conflict")

(* ------------------------------------------------------------------------ propagate *)

let propagate t store =
  let mins = List.map (fun tm -> term_min store tm) t.terms in
  let total_min = List.fold_left ( + ) 0 mins in
  let slack = t.rhs - total_min in
  if slack < 0 then
    Propagator.Conflict (explain_row store (base_explanation t) t.terms ~exclude:None 1)
  else
    let result = ref Propagator.Fixpoint in
    let conflict = ref None in
    List.iteri
      (fun idx (tm, m) ->
        if !conflict = None && tm.coeff <> 0 then
          let max_term = m + slack in
          let d = Store.get store tm.x in
          if tm.coeff > 0 then (
            let new_hi = floordiv max_term tm.coeff in
            if new_hi < Domain.hi d then
              let expl =
                explain_row store (base_explanation t) t.terms ~exclude:(Some idx)
                  tm.coeff
              in
              match Store.set_hi store tm.x new_hi expl with
              | Store.Conflict _ ->
                  conflict := Some (explain_cross_conflict store tm expl)
              | Store.Changed | Store.Unchanged -> ())
          else
            let new_lo = ceildiv max_term tm.coeff in
            if new_lo > Domain.lo d then
              let expl =
                explain_row store (base_explanation t) t.terms ~exclude:(Some idx)
                  (-tm.coeff)
              in
              match Store.set_lo store tm.x new_lo expl with
              | Store.Conflict _ ->
                  conflict := Some (explain_cross_conflict store tm expl)
              | Store.Changed | Store.Unchanged -> ())
      (List.combine t.terms mins);
    (match !conflict with Some e -> result := Propagator.Conflict e | None -> ());
    !result
