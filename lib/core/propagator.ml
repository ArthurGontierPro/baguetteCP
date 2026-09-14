(* The propagator interface.

   Every propagator MUST document its consistency level in [consistency] and the shape of
   the proof step it emits in its module header — the consistency level determines what
   its explanations are allowed to claim. See docs/SPEC.md section 3.2 and the table in
   docs/PROOF-FORMAT.md section 4.

   [propagate] runs until it has nothing more to say about its own constraint, then
   returns [Fixpoint]. It must be sound, checking, and idempotent at the interface
   (invariants I-P1 to I-P3). *)

type result =
  | Fixpoint
  | Conflict of Explanation.t

module type S = sig
  type t

  val name : string

  (* One of: "bounds", "domain", "value", "checking". Documented, not decorative. *)
  val consistency : string

  val vars : t -> Var.t list
  val propagate : t -> Store.t -> result
end
