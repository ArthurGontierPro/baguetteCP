(* The propagator interface.

   Every propagator MUST document its consistency level in [consistency] and the shape of
   the proof step it emits in its module header - the consistency level determines what
   its explanations are allowed to claim. See docs/SPEC.md section 3.2 and the table in
   docs/PROOF-FORMAT.md section 4.

   [propagate] runs until it has nothing more to say about its own constraint, then
   returns [Fixpoint]. It must be sound, checking, and idempotent at the interface
   (invariants I-P1 to I-P3). *)

type result = Fixpoint | Conflict of Explanation.t

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
