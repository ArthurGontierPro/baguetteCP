(* The propagator interface.

   Every propagator MUST document its consistency level in [consistency] and the shape of
   the proof step it emits in its module header - the consistency level determines what
   its explanations are allowed to claim. See docs/SPEC.md section 3.2 and the table in
   docs/PROOF-FORMAT.md section 4.

   [propagate] runs until it has nothing more to say about its own constraint, then
   returns [Fixpoint]. It must be sound, checking, and idempotent at the interface
   (invariants I-P1 to I-P3). *)

(* M2-T7: a conflict is [Store.conflict], which carries the reporting instance's [id] and
   the D-0018 point 3 bound facts alongside the [Explanation.t]. Note what a propagator
   does NOT do here: it never writes its own id. Either it forwards the [Store.conflict]
   a failing mutator handed it, unchanged, or it builds one with [Store.conflict store]
   -- and that function stamps whoever [Engine] said was running. No function a
   propagator calls to change a domain or to report a conflict takes an id, so a
   propagator that wanted to name the wrong one would have to go out of its way, through
   [Store.with_running], which the engine needs public. That route is not sealed; it is
   *checked*, by [Engine.check_attribution], and test_engine.ml's [Steals_credit] walks
   through it on purpose to prove the check fires. Sealing it is not available: [Store]
   cannot tell an engine from a propagator, since it cannot see either type.

   Reach the payload with [c_why] where the old [Conflict of Explanation.t] gave it
   directly. *)
type result = Fixpoint | Conflict of Store.conflict

(* One of these, not a free-form string, so that a typo cannot silently claim a stronger
   consistency than the code delivers. docs/GLOSSARY.md defines each. *)
type consistency = Bounds | Domain | Value | Checking

let consistency_to_string = function
  | Bounds -> "bounds"
  | Domain -> "domain"
  | Value -> "value"
  | Checking -> "checking"

module type S = sig
  type t

  val name : string
  val consistency : consistency
  val vars : t -> Var.t list
  val propagate : t -> Store.t -> result
end

(* The engine holds a heterogeneous collection of propagators, so it needs them erased to
   a common type. Packing at registration time keeps [propagate] a plain closure call on
   the hot path instead of a first-class-module application. *)
type instance = {
  id : int;
  inst_name : string;
  inst_consistency : consistency;
  inst_vars : Var.t list;
  run : Store.t -> result;
}

let pack (type a) ~id (module P : S with type t = a) (p : a) : instance =
  {
    id;
    inst_name = P.name;
    inst_consistency = P.consistency;
    inst_vars = P.vars p;
    run = (fun store -> P.propagate p store);
  }
