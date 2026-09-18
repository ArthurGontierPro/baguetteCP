(* pb_analysis.ml: PSEUDO-BOOLEAN conflict analysis -- eliminate the pivot by linear
   combination and reduction, with the M2-L3 clause path as the fallback (M2-L6, D-0044).

   Consistency level: none -- this is not a propagator. Governing records:
   docs/DECISIONS.md D-0044 and its 2026-09-18 amendment; docs/INVARIANTS.md I-X6
   (frozen reads), I-X8 / D-0029 (coefficient growth must raise), I-S4 (a cited line must
   outlive the line citing it).

   ---------------------------------------------------------------------------
   What this does that lib/core/learn.ml cannot
   ---------------------------------------------------------------------------

   M2-L3 resolves the IMPLICATION GRAPH: nodes are bound facts, and what comes out is a
   clause, the negation of a conjunction. That is sound and it is what a SAT solver does,
   but it throws away the arithmetic. A row like [3x + 3y + z >= 5] enters conflict
   analysis as "these bounds are inconsistent" and leaves as a disjunction of negated
   bounds, which is a much weaker statement than the row itself.

   This module resolves the ROWS. The conflicting constraint and every reason are taken as
   the pseudo-Boolean inequalities the .opb literally contains ([Propagator.pb_row], which
   exists for this and nothing else), and the pivot is eliminated by

       C' = 1 * C  +  a * reduce(R)

   where [a] is the pivot's coefficient in [C] and [reduce] is M2-L5's component, which
   brings the pivot's coefficient in [R] down to 1 so the addition cancels it exactly.
   What comes out is a general PB inequality, and that is the whole justification for this
   row existing: it can be STRICTLY STRONGER than the clause the same conflict yields --
   see "Why the PB row can propagate where the clause cannot" below.

   ---------------------------------------------------------------------------
   Koops et al. (CP 2025), sections 5 and 6 -- what was taken from them
   ---------------------------------------------------------------------------

   READ, at https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2025.21 (LIPIcs
   vol. 340, "Practically Feasible Proof Logging for Pseudo-Boolean Optimization"). Three
   things from it bear on the emission path here, and one of them turned out to be a
   checker-side fact rather than an emitter-side obligation:

     - MERGING ADJACENT WEAKENING STEPS is section 5.4 point 2, and it is CakePB's
       optimisation, not ours: "CakePB now makes a syntactic simplification pass on pol
       lines, where adjacent literal weakening steps are merged into a single simultaneous
       step internally, and adjacent additions of literal axioms (possibly multiplied by
       constants) are also merged." The consequence for an emitter is that the weakening
       axioms of one reduction should be written ADJACENTLY on one [pol] line, which is
       exactly the shape [Explanation.Weaken] already has -- one summand carrying the
       whole list -- so M2-L5's [derivation] needed no change. Recorded because the
       obvious alternative (one [pol] per weakened literal) is the shape that would defeat
       the checker's pass, and nothing else in the tree says not to write it.
     - PARTIAL WEAKENING BEFORE A NON-NORMALISED DIVISION is section 3's MIR machinery:
       the paper weakens on a set [P] by "add[ing] literal axioms to reduce the
       coefficients to the largest multiple of the divisor d" rather than removing the
       literal outright, and its worked [pol] is `pol 29 ~x1 + 3 d` -- literal axioms,
       then a division, on one line. Our [Reduce] rules both weaken a literal AWAY
       entirely. Partial weakening is strictly stronger and would be a THIRD reduction in
       lib/core/reduce.ml's [reductions] rather than a change here: it is the same
       [Combine ([Term (1, e); Weaken ws], d)] shape with a smaller [ws] coefficient. Not
       taken in this row -- M2-L5 owns that list and a new rule owes its own
       postcondition and its own tests -- and left written down here because it is the
       cheapest strength still on the table. See "What is left" at the foot of this file.
     - ANNOTATED RUP for constraints simplified by units (section 5.2) is why the fallback
       path's single [rup] is not a compromise: RoundingSat does the same thing for the
       same reason, having measured that the explicit cutting-planes alternative "causes
       performance issues during proof checking" and "would require ... a quadratic number
       of steps overall".

   ---------------------------------------------------------------------------
   The stopping criterion is SLACK-BASED, and that is not a detail
   ---------------------------------------------------------------------------

   Learning the first ASSERTIVE constraint gives the highest backjump in a SAT solver.
   Le Berre et al. (arXiv 2107.13085) show there is NO SUCH GUARANTEE for PB constraints,
   because a PB constraint propagates by slack rather than by "all but one literal
   falsified". So an assertive constraint is not a sufficient stop condition, and -- the
   part that bites -- a derived row carrying SEVERAL conflict-level literals can still be
   perfectly good and must be ACCEPTED rather than resolved away.

   [assertive_slack] below is therefore stated in slack and counts nothing. It stops when
   the row conflicts or propagates under the assignment WITH THE CONFLICT LEVEL UNDONE,
   which is a question about coefficients and degrees; the number of conflict-level
   literals never enters it. M2-L2 deliberately scoped its 1UIP assertion to
   [Analysis.one_uip]'s own [postcondition] and left [Analysis.conflict_side] accepting
   two conflict-level literals precisely so that this row would not have to re-generalise
   it. It has not been re-generalised: [Analysis.one_uip] is untouched and its
   postcondition is still its own.

   [first_resolution] is the second criterion, and it is here for the reason a second
   implementation always is -- a component with one instance is a constant wearing a
   record. It stops after exactly one elimination, guarantees nothing about levels, and
   says so.

   ---------------------------------------------------------------------------
   [falsified] is frozen AT THE PROPAGATION, and this is the I-X6 obligation
   ---------------------------------------------------------------------------

   lib/core/reduce.ml reads no store on purpose and says whose job this is: "The caller
   (M2-L6) owns freezing that predicate; this module cannot un-freeze it." Here is the
   discharge, and it is not the obvious one.

   The obvious predicate is "falsified under the assignment as it stands at the conflict".
   That is WRONG for a reduction, and wrong in a way that would have shown up as a
   100% fallback rate rather than as an unsound proof. A reason row [R] propagated its
   pivot at trail position [at]; [Reduce]'s postcondition demands that the reduced row
   have slack EXACTLY ZERO, and that holds for the assignment as of [at], not as of the
   conflict. By the conflict, strictly more literals of [R] are falsified, the slack sum
   is smaller, and [Reduce.conflicting_invariant]'s [slack = 0] clause simply fails -- so
   every reduction would be rejected by its own postcondition and every conflict would
   fall back.

   So [bounds_before] reconstructs each variable's domain as of just before [at], out of
   the trail entries' own [old]/[now] pair, and [falsified_before] answers from that. The
   store is read, but only for values the trail already fixes; nothing here can see a
   domain the propagation did not see. That is I-X6 on this half.

   The cost is a downward scan of the trail per variable per elimination. It is bounded by
   [Store.trail_length] and the rows here have few variables; a measurement that finds it
   hot should memoise per [at], not reach for a live read.

   ---------------------------------------------------------------------------
   Why the PB row can propagate where the clause cannot -- D-0044's fork, from the
   other side
   ---------------------------------------------------------------------------

   D-0044's amendment and lib/core/learned.ml's header say [to_linear_row] returns [None]
   on a threshold strictly INSIDE an integer variable's ladder, and that a 1UIP cut over
   integer variables produces exactly those. M2-L3 measured it: 13 of 86 learned clauses
   convert, concentrated in the Boolean models. That is why M2-L3 took fork (ii),
   proof-only.

   A PB row resolved from model rows is a different object and it can land on the right
   side of that test. [Encoding.linear_terms_int_lin_le] gives every rung of a variable's
   ladder the SAME coefficient, so a model row's expansion is ladder-UNIFORM; a positive
   linear combination of ladder-uniform rows is ladder-uniform; and [Reduce.round_to_one]
   keeps a non-falsified literal exactly when its coefficient is divisible by the divisor,
   at [a / d] -- so a uniform run survives a division as a uniform run. Where every step
   happens to preserve uniformity, [Learned.to_linear_row] ACCEPTS the result, and the
   learned object is a real [Linear] instance that prunes, over a conflict whose clause
   [to_linear_row] refuses.

   "Where every step happens to" is doing real work in that sentence: the falsified
   literals kept by a reduction are an arbitrary subset of a ladder and break uniformity
   at once. So this is not a theorem and is not claimed as one -- it is a possibility the
   clause path does not have, and [Search]'s counters measure how often it is realised
   rather than asserting that it is.

   ---------------------------------------------------------------------------
   I-S4, for a [pol] -- the debt lib/core/learn.ml left here explicitly
   ---------------------------------------------------------------------------

   learn.ml's header discharges I-S4's "outlives" half for its own [rup] by observing that
   a [rup] names no id, and then says: "A [pol] citing a hole line across levels WOULD be
   a violation, and M2-L6's reduction steps are the first thing that could write one."

   They do not write one, and the reason is structural rather than lucky. Every leaf of a
   derivation this module builds is an [Explanation.Model_row] carrying a
   [Propagator.pb_row]'s [r_cid] -- a row of the .opb, introduced before the proof's first
   decision and retired by nothing. The only other summand is [Explanation.Weaken], which
   is literal axioms and names no id at all. No hole line, no trace line, no
   conflict-level id is ever cited. [cited_ids] returns the set so a test can assert it
   rather than a reader having to take this paragraph's word for it, and [Search] checks
   it under [Debug].

   ---------------------------------------------------------------------------
   The fallback is permanent, and it is most of the traffic
   ---------------------------------------------------------------------------

   D-0044 records that the M2-L3 clause path is permanent and not transitional, because
   IntSat, HaifaCSP and LLG all need the same fallback. [fallback] below is the reason
   why, enumerated, and every constructor is a measured outcome rather than an error:

     - [No_row] dominates. [Ne], [Bool_clause] and [Bool2int] expose no PB row, because a
       disequality is a pair of big-M rows and a clause propagator is not a single
       inequality either. Any conflict whose conflicting constraint or whose first
       resolvable reason is one of those falls back immediately.
     - [Not_conflicting] is the condition D-0044 names in its own sentence. With
       [division] or [round_to_one] it should not fire -- both reduce to slack zero, and
       adding a slack-zero row to a conflicting one keeps it conflicting -- so a
       non-trivial count here is evidence about a NEW reduction (M2-L7's saturation) and
       not about this loop. It is checked every step regardless, because "should not fire"
       is exactly the kind of claim that stops being true when the component it rests on
       is swapped.
     - [Overflow] is I-X8 / D-0029. Coefficients multiply here and nowhere else in the
       solver, so this is where growth past [Checked]'s cap is met. It RAISES inside
       [Learned.combine] and is caught here, which is the only place it may be caught:
       the answer to overflow is to learn a clause instead, never to wrap and never to
       abandon the solve.
     - [Pivot_not_in_reason] is an attribution or encoding mismatch and is the one arm
       that indicates a defect somewhere else. It is a fallback rather than a raise
       because a wrong learned constraint is a soundness bug and a missing one is not.

   ---------------------------------------------------------------------------
   Determinism
   ---------------------------------------------------------------------------

   No [Hashtbl] is iterated and every list is built in a fixed order: the row's terms come
   from [Learned.make], which sorts, and the pivot is chosen by a total order on trail
   positions. scripts/check_determinism.sh requires two runs to emit a byte-identical
   proof, and a learned row whose terms came out of a hash table is the way that breaks. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer

(* ------------------------------------------------------- the frozen assignment *)

(* The domain of [v] as of just BEFORE trail position [at].

   Read off the trail's own record rather than the store's current state -- see the header
   on I-X6. Three cases and they are exhaustive:

     - the newest entry on [v] strictly below [at] holds the answer in its [now];
     - if there is none, [v] had not moved by [at], so the OLDEST entry on [v] at or above
       [at] holds it in its [old];
     - if there is no entry on [v] at all, [v] has not moved in this search and the
       store's current domain is still the one [at] saw.

   [Domain.t] is a value, so reading [e.old] cannot observe a later narrowing. *)
let bounds_before store ~at v =
  let n = Store.trail_length store in
  let rec down i =
    if i < 0 then None
    else
      let e = Store.trail_entry store i in
      if Var.equal e.Store.var v then Some (Domain.lo e.Store.now, Domain.hi e.Store.now)
      else down (i - 1)
  in
  let rec up i best =
    if i >= n then best
    else
      let e = Store.trail_entry store i in
      if Var.equal e.Store.var v then Some (Domain.lo e.Store.old, Domain.hi e.Store.old)
      else up (i + 1) best
  in
  match down (min (at - 1) (n - 1)) with
  | Some b -> b
  | None -> (
      match up at None with
      | Some b -> b
      | None ->
          let d = Store.get store v in
          (Domain.lo d, Domain.hi d))

(* Is [l] falsified by the assignment as of just before trail position [at]?

   [[x >= k]] is false exactly when [hi x < k]; its negation is false exactly when
   [lo x >= k]. An [Eq] literal (the direct encoding, D-0019/D-0040) has no bound to read
   and is reported NOT falsified, which is the safe direction: [Reduce] weakens away what
   is not falsified, and weakening a literal that happens to be falsified only raises the
   slack, which [Reduce]'s own postcondition then rejects -- a fallback, not a wrong row.
   No [Linear.pb_row] contains one, so this arm is unreached today and is written to be
   unreachable-and-safe rather than unreachable-and-absent. *)
let falsified_before store ~at (l : Lit.t) =
  match l.Lit.v with
  | Lit.Eq _ -> false
  | Lit.Ge (name, k) -> (
      match Store.var_named store name with
      | None -> false
      | Some v ->
          let lo, hi = bounds_before store ~at v in
          if l.Lit.positive then hi < k else lo >= k)

(* The same question at the conflict, i.e. with the whole trail in force. *)
let falsified_now store (l : Lit.t) =
  falsified_before store ~at:(Store.trail_length store) l

(* The trail position at which [l] became falsified, or [Store.no_support] when it is not
   falsified or was already falsified by its declared domain. Used to pick the pivot (the
   most recently falsified conflict-level literal) and to find the entry whose instance
   is the reason. A literal falsified by the declared domain alone has no entry and is
   therefore never a pivot, which is right: nothing propagated it. *)
let falsified_at store (l : Lit.t) =
  if not (falsified_now store l) then Store.no_support
  else
    let n = Store.trail_length store in
    let rec go i =
      if i >= n then Store.no_support
      else if falsified_before store ~at:(i + 1) l then i
      else go (i + 1)
    in
    go 0

(* The decision level at which [l] became falsified; 0 when it is falsified by the
   declared domain or not falsified at all. *)
let level_of store (l : Lit.t) =
  let at = falsified_at store l in
  if at = Store.no_support then 0 else Store.level_of_index store at

(* ------------------------------------------------------- the criterion *)

(* What a criterion is shown: the row under construction, the conflict level, how many
   eliminations have happened, and -- the field that makes this criterion slack-based
   rather than a literal count -- [c_level_of], the level at which each literal became
   falsified. Frozen functions, not a store: a criterion that could reach the store could
   read live state, which is the wrong side of I-X6's line, and lib/core/analysis.ml drew
   the same line for the same reason. *)
type view = {
  c_row : Learned.t;
  c_conflict_level : int;
  c_steps : int;
  c_level_of : Lit.t -> int;
}

type criterion = {
  crit_name : string;
  stop : view -> bool;
  postcondition : view -> bool;
      (* What THIS criterion guarantees about the row it stopped on. It is not a property
         of [view]; see the header, and lib/core/analysis.ml's [criterion] for the same
         decision taken first. *)
}

(* Slack of [v.c_row] under the assignment restricted to levels <= [lvl]: the sum of the
   coefficients of the terms NOT falsified by then, minus the degree. *)
let slack_at v lvl =
  let sum =
    List.fold_left
      (fun acc (tm : Learned.term) ->
        if v.c_level_of tm.Learned.lit <= lvl then acc
        else Checked.add acc tm.Learned.coeff)
      0 (Learned.terms v.c_row)
  in
  Checked.sub sum (Learned.degree v.c_row)

(* Does the row conflict, or propagate something, under the assignment up to [lvl]?

   Both halves are one slack question. Negative slack is a conflict outright; a literal
   still unfalsified at [lvl] whose coefficient exceeds the slack is propagated. Nothing
   here counts literals at any level, which is the point -- see the header. *)
let asserts_at v lvl =
  let s = slack_at v lvl in
  s < 0
  || List.exists
       (fun (tm : Learned.term) ->
         v.c_level_of tm.Learned.lit > lvl && tm.Learned.coeff > s)
       (Learned.terms v.c_row)

(* THE criterion (docs/ROADMAP.md M2-L6 test (a2)). Stop as soon as the row would still
   say something after the conflict level is undone -- that is, as soon as it conflicts or
   propagates at [conflict_level - 1].

   Read what this does NOT say. It does not say "one conflict-level literal". A row
   carrying five of them satisfies this the moment its slack at the lower level is small
   enough, and is accepted. That is Le Berre et al.'s point and it is the reason
   [Analysis.one_uip]'s postcondition could not simply have been reused.

   At least one elimination is required before stopping, because the row before any
   elimination is the conflicting constraint itself: already on the page, already
   citable, and learning it would put a copy of a model row into the proof for nothing.
   See [analyse]'s [Nothing_to_learn]. *)
let assertive_slack =
  let ok v = v.c_steps >= 1 && asserts_at v (v.c_conflict_level - 1) in
  { crit_name = "assertive-slack"; stop = ok; postcondition = ok }

(* The second criterion: stop after exactly one elimination. It guarantees nothing about
   levels and says so, which is what makes it useful -- it is the standing proof that
   [assertive_slack]'s postcondition is [assertive_slack]'s and not a property of the
   type. lib/core/analysis.ml's [conflict_side] is here for the same reason. *)
let first_resolution =
  {
    crit_name = "first-resolution";
    stop = (fun v -> v.c_steps >= 1);
    postcondition = (fun v -> v.c_steps >= 1);
  }

let criteria = [ assertive_slack; first_resolution ]
let find_criterion name = List.find_opt (fun c -> String.equal c.crit_name name) criteria
let postcondition_holds (c : criterion) (v : view) = c.postcondition v

(* ------------------------------------------------------- the outcome *)

(* Why PB analysis handed the conflict back to the clause path. Every one of these is a
   measured outcome, not an error; see the header. *)
type fallback =
  | No_row of string  (** an instance exposes no PB row -- which instance, by name *)
  | Not_conflicting  (** the combination stopped being conflicting: D-0044's condition *)
  | Overflow of string  (** I-X8 / D-0029: coefficient growth past [Checked]'s cap *)
  | Pivot_not_in_reason
  | No_pivot  (** no falsified conflict-level literal is left to resolve on *)
  | Reduction_refused  (** [Reduce] said [None], or its own postcondition did not hold *)
  | Nothing_to_learn  (** the criterion stopped before any elimination happened *)
  | Diverged of int

let fallback_to_string = function
  | No_row n -> Printf.sprintf "no PB row for instance %s" n
  | Not_conflicting -> "the combination stopped being conflicting"
  | Overflow m -> Printf.sprintf "coefficient growth past the cap: %s" m
  | Pivot_not_in_reason -> "the pivot is not a literal of the reason row"
  | No_pivot -> "no falsified conflict-level literal left to resolve on"
  | Reduction_refused -> "the reduction refused, or its postcondition did not hold"
  | Nothing_to_learn -> "the criterion stopped before any elimination"
  | Diverged n -> Printf.sprintf "did not terminate after %d eliminations" n

type t = {
  row : Learned.t;  (** the learned PB inequality *)
  derivation : Explanation.t;  (** the cutting-planes derivation of exactly [row] *)
  steps : int;  (** eliminations performed *)
  pivots : Lit.t list;  (** the literals eliminated, in order *)
  reduction_name : string;
  criterion_name : string;
  antecedents : int list;  (** constraint ids the derivation cites, first-seen order *)
}

type result = Learned_row of t | Fallback of fallback

(* ------------------------------------------------------- reading a derivation *)

(* Every constraint id the derivation cites. The I-S4 discharge in the header is a claim
   about this list: it holds model-row ids and nothing else. Recursion is over the ADT
   rather than a catch-all, so a constructor added to [Explanation] stops compiling here
   and whoever adds it says what it cites. *)
let cited_ids (e : Explanation.t) : int list =
  let acc = ref [] in
  let add id = if not (List.mem id !acc) then acc := !acc @ [ id ] in
  let rec go (e : Explanation.t) =
    match e with
    | Explanation.Model_row id -> add id
    | Explanation.Combine (summands, _) -> List.iter summand summands
    | Explanation.Cut (a, b, _, _) ->
        go a;
        go b
    | Explanation.Deferred _ -> go (Explanation.force e)
    | Explanation.Decision _ | Explanation.Clause _ | Explanation.Linear _ -> ()
  and summand = function Explanation.Term (_, e) -> go e | Explanation.Weaken _ -> () in
  go e;
  !acc

(* ------------------------------------------------------- the loop *)

let coeff_of (row : Learned.t) (l : Lit.t) =
  List.find_map
    (fun (tm : Learned.term) ->
      if Lit.equal tm.Learned.lit l then Some tm.Learned.coeff else None)
    (Learned.terms row)

exception Give_up of fallback

(* Eliminate the pivot by linear combination and reduction.

   [row_of] is [Engine.row_of] partially applied -- the instance's PB row, or [None]. It
   is passed rather than the engine for the reason lib/core/analysis.ml passes [vars_of]:
   this module is shown two narrow questions about the engine and cannot reach anything
   else.

   [name_of] is only for the [No_row] message and may answer anything; a fallback reason
   nobody can read is a counter with no diagnosis behind it. *)
let analyse store (c : Store.conflict) ~(row_of : int -> Propagator.pb_row option)
    ~(name_of : int -> string) ~(reduction : Reduce.t) ~(criterion : criterion) : result =
  let conflict_level = Store.level store in
  let max_steps = Store.trail_length store + 1 in
  let level_of = level_of store in
  let view row steps =
    {
      c_row = row;
      c_conflict_level = conflict_level;
      c_steps = steps;
      c_level_of = level_of;
    }
  in
  (* The literal to resolve on: falsified, established at the conflict level by an entry
     that rests on facts (a decision rests on none and is never resolved away -- the same
     root rule lib/core/analysis.ml states), and the most RECENT such, which is what makes
     the walk terminate: every elimination's pivot is strictly below the last. *)
  let pivot_of row =
    List.fold_left
      (fun best (tm : Learned.term) ->
        let l = tm.Learned.lit in
        let at = falsified_at store l in
        if at = Store.no_support then best
        else if Store.level_of_index store at <> conflict_level then best
        else if Reason.is_empty (Store.trail_entry store at).Store.reason then best
        else match best with Some (_, b) when b >= at -> best | _ -> Some (l, at))
      None (Learned.terms row)
  in
  let step row expl steps pivots antecedents =
    match pivot_of row with
    | None -> raise (Give_up No_pivot)
    | Some (l, at) ->
        let e = Store.trail_entry store at in
        let reason_row =
          match row_of e.Store.prop with
          | None -> raise (Give_up (No_row (name_of e.Store.prop)))
          | Some r -> r
        in
        let r = Learned.of_pb_row reason_row in
        (* The pivot in the REASON is the complement: the conflict row carries [l]
           falsified, and the entry propagated [~l] true. *)
        let p = Lit.negate l in
        if coeff_of r p = None then raise (Give_up Pivot_not_in_reason);
        (* Frozen at the propagation, not at the conflict. This is the I-X6 discharge and
           the header says why it cannot be the conflict-time predicate. *)
        let falsified = falsified_before store ~at in
        let v = { Reduce.row = r; pivot = p; falsified } in
        let o =
          match reduction.Reduce.reduce v with
          | None -> raise (Give_up Reduction_refused)
          | Some o ->
              if Reduce.postcondition_holds reduction v o then o
              else raise (Give_up Reduction_refused)
        in
        let a =
          match coeff_of row l with Some a -> a | None -> raise (Give_up No_pivot)
        in
        (* I-X8 / D-0029: [Learned.combine] multiplies through [Checked], which RAISES
           past the cap. Caught here and turned into a fallback -- never wrapped, and
           never allowed to abandon the solve. *)
        let row' =
          try Learned.combine row 1 o.Reduce.reduced a
          with Checked.Overflow m -> raise (Give_up (Overflow m))
        in
        (* D-0044's named condition, checked every step. See the header on why it should
           not fire for the reductions that exist today and is checked anyway. *)
        let v' = view row' (steps + 1) in
        if not (slack_at v' conflict_level < 0) then raise (Give_up Not_conflicting);
        let expl' =
          Explanation.combine
            [
              Explanation.term 1 expl;
              Explanation.term a
                (o.Reduce.derive (Explanation.model_row reason_row.Propagator.r_cid));
            ]
            1
        in
        let antecedents =
          if List.mem reason_row.Propagator.r_cid antecedents then antecedents
          else antecedents @ [ reason_row.Propagator.r_cid ]
        in
        (row', expl', pivots @ [ l ], antecedents)
  in
  try
    let conflict_row =
      match row_of c.Store.c_prop with
      | None -> raise (Give_up (No_row (name_of c.Store.c_prop)))
      | Some r -> r
    in
    let row0 = Learned.of_pb_row conflict_row in
    let expl0 = Explanation.model_row conflict_row.Propagator.r_cid in
    (* If our reconstruction of the conflicting row is not actually conflicting, the row
       we built is not the row the store conflicted on. That is a real disagreement and it
       falls back rather than deriving from a premise the search does not share. *)
    if not (slack_at (view row0 0) conflict_level < 0) then
      raise (Give_up Not_conflicting);
    let rec loop row expl steps pivots antecedents =
      if criterion.stop (view row steps) then
        if steps = 0 then raise (Give_up Nothing_to_learn)
        else
          Learned_row
            {
              row;
              derivation = expl;
              steps;
              pivots;
              reduction_name = reduction.Reduce.name;
              criterion_name = criterion.crit_name;
              antecedents;
            }
      else if steps >= max_steps then raise (Give_up (Diverged steps))
      else
        let row', expl', pivots', antecedents' = step row expl steps pivots antecedents in
        loop row' expl' (steps + 1) pivots' antecedents'
    in
    loop row0 expl0 0 [] [ conflict_row.Propagator.r_cid ]
  with Give_up f -> Fallback f

(* ------------------------------------------------------- the proof side *)

(* Put the learned PB row on the page and hand back its id.

   AT LEVEL 0 and STATING WHAT IT DERIVES, and both halves matter:

     - level 0, for exactly the reason lib/core/learned.ml's [introduce] gives: a
       constraint derived at the conflict level is deleted by the backjump that follows,
       and both checkers then reject the next line that cites it -- in words that share no
       substring ("Trying to access constraint with ID 3 that has already been deleted"
       under 3.0; "Rule 6 is trying to access constraint (constraintId 3), that was marked
       as safe to delete" under 2.0). [Justify.with_level] moves the level for real in
       both formats.
     - stating, through [Justify.emit_stating], because a bare [pol] derives whatever the
       cutting-planes expression evaluates to and says nothing about what we THINK it
       derived. With the claim on the page the checker's `ia` compares the two, so a
       disagreement between [Learned.combine]'s arithmetic and the checker's surfaces
       here, as a rejected line, instead of propagating silently into whatever cites this
       row. That is this row's own arithmetic being checked by the proof rather than by a
       test, and it is available only because the learned object is a [pol] -- the clause
       path's [rup] has nothing to state.

   I-X2: the id handed back is an id the caller must delete. Nothing else will, because
   no [w] retires level 0. *)
let introduce ctx (t : t) : Writer.cid =
  Justify.with_level ctx 0 (fun () ->
      Justify.emit_stating ctx ~claim:(Learned.to_opb t.row) t.derivation)

let to_string (t : t) =
  Printf.sprintf "[%s/%s] %s | %d step(s), pivots %s | cites %s" t.criterion_name
    t.reduction_name (Learned.to_string t.row) t.steps
    (String.concat " " (List.map Lit.to_string t.pivots))
    (String.concat "," (List.map string_of_int t.antecedents))

(* ---------------------------------------------------------------------------
   What is left, for whoever takes M2-L7 or the next PB row
   ---------------------------------------------------------------------------

   1. PARTIAL WEAKENING, per Koops et al. section 3 (see the header). A third [Reduce.t],
      not a change here: weaken a non-falsified literal's coefficient DOWN to the largest
      multiple of the divisor instead of removing the literal, so it survives the division
      at [floor (a / d)] instead of vanishing. It is free by the same slack argument
      lib/core/reduce.ml gives -- dropping [a mod d] from a non-falsified term removes it
      from both the slack sum and the degree -- and it dominates [round_to_one] as
      [round_to_one] dominates [division].
   2. A RUNTIME INSTANCE for the learned row. [Learned.instance] already builds one when
      [to_linear_row] accepts, and the counters here say how often that is; what is
      missing is the retention policy (M2-L4) that decides which to keep.
   3. BACKJUMPING ON THE PB ROW. This row deliberately does not: the backjump still rests
      on lib/core/learn.ml's decision closure, because the levels a derived row names are
      not a dependency set any more than a 1UIP cut's are, and M2-L3 has the argument
      written out. A PB row that propagates at runtime would change that calculation. *)
