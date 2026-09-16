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
   explanation and nothing else and cannot tell which half produced it. A reason that
   names no row is then unresolvable: there is no way to route it to the right model
   constraint. The fix is not a cleverer routing scheme, it is to never need one: post
   [le] and [ge] as two instances, each of which is asked to justify only against the
   one row it knows about and each of which carries that row's id, so every base is a
   [Model_row] and nothing ever has to inspect an explanation to work out which row it
   meant. M1-T31 finished the job by deleting the fallback: there is no ambient row
   left to route to, so a row that is not named cannot be guessed.

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
   docs/DECISIONS.md D-0013 [Combine] -- docs/PROOF-FORMAT.md section 4's
   `int_lin_eq` row, "two int_lin_le derivations", taken completely literally, each
   against its own row id ([~le_id]/[~ge_id], from [Encoding.add_equality]). *)

(* [Checked.neg] rather than [-]: min_int has no negation, so an unchecked negation
   here would turn the `>=` half of an equality into a row that is not the negation of
   the `<=` half -- and both halves would then be justified against .opb rows that do
   not say what the propagators believe (roadmap M1-T23, lib/core/checked.ml). *)
let negate_terms terms = List.map (fun (a, x) -> (Checked.neg a, x)) terms

(* [make store terms rhs ~le_id ~ge_id] : (le, ge), the two [Linear.t] instances the
   equality [sum terms = rhs] decomposes into. Post both to the engine; pair [le]
   with the `<=` id and [ge] with the `>=` id from [Encoding.add_equality] (whose own
   return order is [(geq, leq)] -- i.e. [~ge_id] is that function's first result,
   [~le_id] its second). Both required for the same reason [Linear.make]'s [~row_id]
   is (M1-T31) -- see that module's header. The pairing is this function's whole
   point: the two halves are two different rows, so an instance that could not name
   its own would have to fall back on whichever one happened to be ambient, and that
   is precisely the ambiguity D-0011 named. *)
let make ~le_id ~ge_id store terms rhs =
  let le = Linear.make ~row_id:le_id store terms rhs in
  let ge = Linear.make ~row_id:ge_id store (negate_terms terms) (Checked.neg rhs) in
  (le, ge)
