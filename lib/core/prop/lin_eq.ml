(* int_lin_eq: sum_i a_i * x_i = c, over integer variables with possibly negative or
   zero coefficients.

   Consistency level: BOUNDS (docs/SPEC.md 3.2), same as [Linear] (lib/core/prop/linear.ml):
   this module only ever tightens lo/hi, never punches a hole.

   Justification shape (docs/PROOF-FORMAT.md section 4, `int_lin_eq` row): "two
   int_lin_le derivations". This module takes that literally rather than inventing a
   fused equality reasoning of its own -- [make] builds *two* [Linear.t] values,

     le : sum_i  a_i * x_i <=  c
     ge : sum_i -a_i * x_i <= -c        (i.e. sum_i a_i * x_i >= c)

   and [propagate] is nothing but running both to fixpoint. Every explanation this
   module ever returns is therefore, unmodified, exactly the [Cut (Trivial, Linear
   (units, units_rhs), 1, 1)] shape [Linear.explain] already produces and that veripb
   already accepts (D-0009, D-0010) -- there is no new derivation kind to prove sound,
   only two existing ones run side by side. This is also why there is no new call into
   [Order_reason] here: [Linear] already calls it, and this module never touches a
   chain literal directly.

   The one thing this module owns that plain [int_lin_le] does not: which underlying
   model constraint a given pruning's [Trivial] refers to. [Encoding.add_equality]
   posts the equality as exactly these same two rows (its own comment says so: "this is
   the same split"), yielding two ids. A caller wiring this propagator's explanations to
   a proof therefore needs the *pair* of ids and must route an explanation to the ctx
   pointed at whichever of [le]/[ge] produced it -- [le]/[ge] below expose the two
   [Linear.t] values themselves (by structural identity, not by name) so a caller can
   tell which one is asking, exactly the way test/unit/test_justify.ml's [build_two_ctx]
   / [for_constraint] pattern already handles two model rows sharing one writer.

   Fixpoint requires alternating the two directions, not one pass of each: for a
   positive coefficient, [le] tightens the hi bound and [ge] tightens the lo bound (and
   vice versa for a negative coefficient), and each direction's own slack computation
   reads the *other* variables' current bounds -- so a tightening [le] makes to x_j can
   let [ge] tighten some other x_i further, which can in turn let [le] tighten more.
   [propagate] therefore loops both to a shared fixpoint (comparing a full store
   snapshot each round, cheaply, since domains only ever shrink so the loop provably
   terminates - I-D3) rather than assuming one round of each suffices. *)

type t = { le : Linear.t; ge : Linear.t }

let name = "int_lin_eq"
let consistency = Propagator.Bounds

let negate_terms terms = List.map (fun (a, x) -> (-a, x)) terms

let make store terms rhs =
  let le = Linear.make store terms rhs in
  let ge = Linear.make store (negate_terms terms) (-rhs) in
  { le; ge }

(* Both halves range over the same variables (one is the other's negation), so either
   suffices; [le] is arbitrary. *)
let vars t = Linear.vars t.le

(* Exposed so a caller can tell [le] and [ge] apart by structural identity (as
   [Justify]'s memo already does for [Explanation.t], see lib/core/justify.ml's header)
   when deciding which model constraint's ctx to justify a given pruning against. *)
let le t = t.le
let ge t = t.ge

let propagate t store =
  let rec loop () =
    let snap = Store.snapshot store in
    match Linear.propagate t.le store with
    | Propagator.Conflict _ as c -> c
    | Propagator.Fixpoint -> (
        match Linear.propagate t.ge store with
        | Propagator.Conflict _ as c -> c
        | Propagator.Fixpoint ->
            if Store.same_domains store snap then Propagator.Fixpoint else loop ())
  in
  loop ()
