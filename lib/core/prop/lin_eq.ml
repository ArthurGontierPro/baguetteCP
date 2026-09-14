(* int_lin_eq: sum_i a_i * x_i = c, over integer variables with possibly negative or
   zero coefficients.

   docs/DECISIONS.md D-0011: one propagator instance justifies against exactly one
   model row. An equality is *two* rows -- [Encoding.add_equality] posts the `<=` and
   `>=` halves separately and hands back two distinct ids -- so [int_lin_eq] is not
   itself a propagator instance. [make] returns a PAIR of ordinary [Linear.t] values,

     le : sum_i  a_i * x_i <=  c
     ge : sum_i -a_i * x_i <= -c        (i.e. sum_i a_i * x_i >= c)

   for a caller to post as two separate, independently watched propagators, each paired
   with its own id from [Encoding.add_equality] -- that function's own comment says its
   two ids are `(geq, leq)`, so [ge] pairs with the first and [le] with the second.
   Each of [le]/[ge] is exactly [int_lin_le] as it already exists: same module, same
   propagate, same explanation shape. This file contributes nothing beyond the
   negation that builds [ge] from [le]'s terms.

   An earlier version of this module fused [le] and [ge] into one propagator that
   alternated them internally to a shared fixpoint, and proposed that a caller route
   each resulting explanation to the model id for whichever half produced it by
   comparing against the exposed [Linear.t] values. D-0011 records why that is wrong:
   a pruning's explanation is recorded on the trail as [{ var; old; why }]
   (lib/core/store.ml's [entry]) -- **the trail records no propagator identity** -- so a
   caller walking the trail later (conflict analysis, from M2-T3 on) has the
   explanation and nothing else and cannot tell which half produced it. [Trivial] is
   then unresolvable: there is no way to route it to the correct [ctx.model_id]. The
   fix is not a cleverer routing scheme, it is to never need one: post [le] and [ge] as
   two instances, each of which is asked to justify only against the one row it knows
   about, so [Trivial] is resolvable by construction and nothing ever has to inspect an
   explanation to work out which row it meant.

   The fixpoint reasoning the old fused loop used to justify itself is still correct,
   it just belongs to the engine now, not here: [engine.ml] runs propagators to a
   fixpoint and re-wakes a propagator when a variable it watches changes. Tightening
   [le]'s bound on some x_i can enable [ge] to tighten a bound on some x_j (their slack
   computations read each other's current bounds -- [le] tightens hi for a positive
   coefficient and lo for a negative one, [ge] the opposite, and each's slack depends on
   every term's *current* min), which is exactly "a watched variable changed, re-run the
   propagators watching it" -- the engine's own job. Positing [le] and [ge] as two
   ordinary instances therefore reaches the same fixpoint a hand-written alternation
   would reach, without a second, ad hoc scheduler duplicating what the engine already
   does. Do not re-add a loop here.

   Consistency level: BOUNDS, inherited entirely from [Linear] (see that module's
   header). Justification shape: each of [le]/[ge] is exactly [int_lin_le]'s own
   [Cut (Trivial, Linear (units, units_rhs), 1, 1)] -- docs/PROOF-FORMAT.md section 4's
   `int_lin_eq` row, "two int_lin_le derivations", taken completely literally. *)

let negate_terms terms = List.map (fun (a, x) -> (-a, x)) terms

(* [make store terms rhs] : (le, ge), the two [Linear.t] instances the equality
   [sum terms = rhs] decomposes into. Post both to the engine; pair [le] with the
   `<=` id and [ge] with the `>=` id from [Encoding.add_equality] (whose own return
   order is [(geq, leq)]). *)
let make store terms rhs =
  let le = Linear.make store terms rhs in
  let ge = Linear.make store (negate_terms terms) (-rhs) in
  (le, ge)
