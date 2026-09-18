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

(* ------------------------------------------------------------------ M2-L6: the PB row

   The pseudo-Boolean inequality an instance IS, as the .opb already contains it:
   [sum r_terms >= r_degree] over order literals, with [r_cid] the id of that very
   constraint on the page.

   PB conflict analysis (lib/core/pb_analysis.ml) resolves ROWS, not clauses, and that is
   the whole of why it can learn something the clause path cannot. It therefore needs,
   for a propagation, the constraint that DID the propagating -- which for a PB solver is
   not "the facts the propagator read" but the row itself. lib/core/analysis.ml's graph
   answers the first question; this field answers the second, and nothing else in the
   codebase did.

   Three things about the shape, each deliberate:

     - it is a plain [(coeff, lit) list] and not a [Learned.t], because [Learned] depends
       on [Linear] which depends on this module. The dependency runs one way and this
       field must not turn it into a cycle. [Learned.of_pb_row] is the conversion and it
       lives where the cycle allows it.
     - it is a FUNCTION of the store, not a value, because an instance is packed before
       any store exists ([Compile] builds pending instances first) and because the
       expansion needs each variable's NAME. It is emphatically not a function of the
       store because it reads live domains: [Linear.pb_row] reads [Store.name] and the
       DECLARED bounds the instance froze at [make] time, and nothing else. A row that
       moved with the search would be the wrong side of I-X6, and every [pol] built on it
       would derive something other than what the .opb actually says.
     - [r_cid] is required, not optional. A row nobody can cite is a row no [pol] can be
       built from; an instance offering terms without an id would be offering arithmetic
       with no proof behind it.

   [None] -- the default -- means "this instance does not expose a PB row", which is the
   honest answer for [Ne] (a disequality is a pair of big-M rows, not one), for
   [Bool_clause] and for [Bool2int]. That is not a defect: it is exactly the condition
   under which M2-L6 falls back to the M2-L3 clause path, and how often it is the answer
   is the fallback rate [Search] reports. D-0044 records that the clause path is
   permanent, and this is the mechanism that makes it so. *)
type pb_row = { r_terms : (int * Baguette_proof.Lit.t) list; r_degree : int; r_cid : int }

(* The engine holds a heterogeneous collection of propagators, so it needs them erased to
   a common type. Packing at registration time keeps [propagate] a plain closure call on
   the hot path instead of a first-class-module application. *)
type instance = {
  id : int;
  inst_name : string;
  inst_consistency : consistency;
  inst_vars : Var.t list;
  run : Store.t -> result;
  inst_row : Store.t -> pb_row option;
      (* M2-L6. See [pb_row] above. [pack] defaults it to "no row", so a propagator
         family that has not been taught its own row is not silently credited with one. *)
}

let no_row : Store.t -> pb_row option = fun _ -> None

let pack (type a) ?(row = no_row) ~id (module P : S with type t = a) (p : a) : instance =
  {
    id;
    inst_name = P.name;
    inst_consistency = P.consistency;
    inst_vars = P.vars p;
    run = (fun store -> P.propagate p store);
    inst_row = row;
  }
