(* int_lin_le_reif:  b <-> (sum_i a_i x_i <= rhs),  and its two-variable specialisation
   int_le_reif (b <-> x <= y).

   Consistency level: BOUNDS (docs/SPEC.md 3.2). Every pruning this instance makes is
   made by [Linear], which is bounds consistent for its own row, and the reifier is a
   bool, which has no interior to be domain consistent about. The level is therefore
   [Linear]'s, unchanged, and nothing here claims more.

   ---------------------------------------------------------------------------
   The three author pieces (roadmap M3-T4), and the two rows that carry five cases
   ---------------------------------------------------------------------------

   lib/core/prop/reif.ml is the dispatcher and its header states the contract: an
   author supplies enforce-hold, enforce-not-hold and entailment, and the dispatcher
   does the collapse and the contrapositive. This author supplies all three out of
   *two ordinary [Linear] instances*, over the two rows lib/proof/encoding.ml's
   [add_int_lin_le_reif_rows] posts:

     FWD   sum a_i x_i  +  K  b  <=  rhs + K       K  = hi - rhs
     BWD  -sum a_i x_i  -  K' b  <=  -rhs - 1      K' = rhs + 1 - lo

     enforce-hold      [Linear] over FWD. With b fixed to 1 the big-M term contributes
                       its full K to the minimum, the slack is exactly the condition's
                       own, and the pass is ordinary bounds propagation on
                       `sum a x <= rhs`.
     enforce-not-hold  [Linear] over BWD. With b fixed to 0 the big-M term contributes
                       nothing and the row is `sum a x >= rhs + 1`, the negation.
     entailment        the SAME two instances, with b unfixed. Then neither row can
                       move a condition variable -- the big-M cushion is by
                       construction exactly the width of the row's own span, so every
                       computed bound lands at or outside the declared one -- and the
                       only term either can push is b itself. FWD pushes hi(b) below 1
                       exactly when min(sum a x) > rhs, which is case 4; BWD pushes
                       lo(b) above 0 exactly when max(sum a x) <= rhs, which is case 3.

   So the five cases are carried by two rows, and the two directions of each row carry
   a case and its own contrapositive. That is not a coincidence to be admired: it is
   why the big-M constants have to be the smallest that work (D-0053), because a larger
   K would leave slack in the cushion and the entailment pushes above would stop firing
   at the right moment.

   ---------------------------------------------------------------------------
   Justification
   ---------------------------------------------------------------------------

   There is none of its own, and that is the point. Every pruning here is [Linear]'s,
   justified by [Linear]'s D-0013 [Combine] over [Model_row fwd_id] or
   [Model_row bwd_id] -- rows the .opb actually contains, posted by the `.opb` door
   D-0053 requires for a model-stated reifier. The reifier is just another term of the
   row, so the [Combine] treats it exactly as it treats a condition variable: still at
   its declared bound, weaken it away with an axiom (D-0009); moved by an earlier step,
   cite that step. No new [Explanation] constructor is involved, and none was added.

   The terms handed to [Linear.make] must be the row's own terms, or [Model_row] would
   name a constraint [Linear.pb_row] cannot reproduce (M2-L6). [k_fwd] and [k_bwd] are
   therefore passed in from the encoding that posted the rows rather than recomputed
   here -- the same discipline, and for the same reason, as [~row_id] itself. *)

type t = Reif.t

let consistency = Propagator.Bounds
let vars = Reif.vars
let propagate = Reif.propagate

(* [terms] is the condition `sum a_i x_i <= rhs` over the *condition's* variables;
   [reifier] is not among them. [fwd_id]/[bwd_id] and [k_fwd]/[k_bwd] come from
   [Encoding.add_int_lin_le_reif_rows], which posted the two rows these cite.

   Reads each variable's declared domain out of the store through [Linear.make], so it
   inherits that function's D-0010 requirement: call it before anything has narrowed a
   domain. *)
let make ~fwd_id ~bwd_id ~k_fwd ~k_bwd store terms rhs ~reifier =
  let fwd =
    Linear.make ~row_id:fwd_id store
      (terms @ [ (k_fwd, reifier) ])
      (Checked.add rhs k_fwd)
  in
  let bwd =
    Linear.make ~row_id:bwd_id store
      (List.map (fun (a, x) -> (Checked.neg a, x)) terms
      @ [ (Checked.neg k_bwd, reifier) ])
      (Checked.sub (Checked.neg rhs) 1)
  in
  let both store =
    match Linear.propagate fwd store with
    | Propagator.Conflict c -> Propagator.Conflict c
    | Propagator.Fixpoint -> Linear.propagate bwd store
  in
  Reif.make ~reifier ~positive:true ~vars:(List.map snd terms)
    ~hold:(Linear.propagate fwd) ~not_hold:(Linear.propagate bwd) ~entail:both store

(* The two named faces, in the [Ne] / [Ne.Int_ne] shape: one implementation, and an
   instance reports the builtin the model actually wrote. *)
module Int_lin_le_reif = struct
  type nonrec t = t

  let name = "int_lin_le_reif"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end

module Int_le_reif = struct
  type nonrec t = t

  let name = "int_le_reif"
  let consistency = consistency
  let vars = vars
  let propagate = propagate
end
