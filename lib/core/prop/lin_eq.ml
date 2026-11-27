(* int_lin_eq: sum_i a_i * x_i = c, over integer variables with possibly negative or
   zero coefficients.

   Consistency level: BOUNDS (docs/SPEC.md 3.2), inherited entirely from [Linear] (see
   that module's header). This module defines no propagator of its own, so it has no
   [consistency] value: the two instances it builds are [Linear.t]s and report [Linear]'s.

   One instance, one row (D-0011, restated by D-0027 as a rule about NAMING rows: every
   explanation an instance builds names the model row it was derived from, as [Model_row
   id] in the value). An equality is TWO rows in the .opb, because
   [Encoding.add_equality] posts the `>=` and `<=` halves separately and returns two
   distinct ids. So [make] does not build one propagator over both. It returns a PAIR of
   ordinary [Linear.t] values,

     le : sum_i  a_i * x_i <=  c
     ge : sum_i -a_i * x_i <= -c        (i.e. sum_i a_i * x_i >= c)

   which the caller posts as two separate, independently watched instances, each paired
   with its own row id. [Encoding.add_equality] returns its ids as [(geq, leq)], so [ge]
   takes the first and [le] the second. Each of [le]/[ge] is exactly [int_lin_le]: same
   module, same propagate, same explanation shape. This file contributes nothing beyond
   the negation that builds [ge] from [le]'s terms.

   Why two instances and not one fused propagator. A fused instance owning both rows
   would have to work out, for each pruning, which half produced it and so which row the
   justification must cite. Nothing downstream can do that for it. A [Store.entry] does
   carry the instance that made it (its [prop] field, since M2-T7), but that names the
   fused instance, which owns both rows, so it cannot tell the halves apart. And
   lib/core/justify.ml renders an explanation from the value alone, without the entry.
   With two instances the question never arises: each one justifies only against the
   row it was built with, and every base it writes is that row's [Model_row]. The id is
   a required argument, so a row that is not named cannot be guessed (M1-T31 removed the
   ambient "current row" fallback that used to stand in for it).

   The fixpoint needs no loop here either, because the engine already provides it.
   lib/core/engine.ml runs propagators to a fixpoint and re-wakes an instance when a
   variable it watches changes. Tightening a bound through [le] can let [ge] tighten
   another, since each half's slack reads every term's current minimum ([le] tightens hi
   for a positive coefficient and lo for a negative one, [ge] the opposite), and that is
   exactly "a watched variable changed, re-run the instances watching it". Two ordinary
   instances therefore reach the same fixpoint a hand-written alternation would, without
   a second scheduler duplicating the engine's job. Do not re-add a loop here.

   History, in one line: an earlier version fused [le] and [ge] into one propagator
   alternating to a shared fixpoint, at a time when the trail recorded no propagator
   identity at all; D-0011 replaced it with the pair.

   Justification shape: each of [le]/[ge] is [int_lin_le]'s own [Combine], the "weaken,
   divide, add" derivation of D-0013 (the other terms' bounds are weakened away from the
   row, the sum divided by the pruned variable's coefficient), against its own row id
   ([~le_id]/[~ge_id]). That is docs/PROOF-FORMAT.md section 4's `int_lin_eq` row, "two
   int_lin_le derivations", taken literally. *)

(* [Checked.neg] rather than [-]: min_int has no negation, so an unchecked negation here
   would turn the `>=` half of an equality into a row that is not the negation of the
   `<=` half, and both halves would then be justified against .opb rows that do not say
   what the propagators believe. Checked arithmetic, which raises [Checked.Overflow]
   instead of wrapping, is lib/core/checked.ml (roadmap M1-T23). *)
let negate_terms terms = List.map (fun (a, x) -> (Checked.neg a, x)) terms

(* [make store terms rhs ~le_id ~ge_id] : (le, ge), the two [Linear.t] instances the
   equality [sum terms = rhs] decomposes into. Post both to the engine. [~le_id] is the
   `<=` row's id and [~ge_id] the `>=` row's, so with [Encoding.add_equality]'s
   [(geq, leq)] result, [~ge_id] is its first component and [~le_id] its second. Both are
   required for the reason [Linear.make]'s [~row_id] is (see that module's header). The
   pairing is this function's whole point: the two halves are two different rows, and an
   instance that could not name its own would be back to the ambiguity D-0011 removed. *)
let make ~le_id ~ge_id store terms rhs =
  let le = Linear.make ~row_id:le_id store terms rhs in
  let ge = Linear.make ~row_id:ge_id store (negate_terms terms) (Checked.neg rhs) in
  (le, ge)
