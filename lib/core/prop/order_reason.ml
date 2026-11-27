(* Order-encoding chains of literals that state, or weaken away, a variable's
   contribution to a linear row. Not a propagator: a helper for the propagators and
   for lib/core/justify.ml, which renders their explanations into proof lines.

   The currency rule (D-0010): a bound fact must be stated in the same currency as the
   model row it is combined with, and that currency is the order encoding's own
   substitution

     x = lo_decl + sum_{v = lo_decl+1}^{hi_decl} [x >= v]

   which lib/proof/encoding.ml performs on the model side ([Encoding.expand_int_lin_le],
   [Encoding.linear_terms_int_lin_le]). The two must agree on the constant, or the
   pieces do not combine. A single literal [x_ge_b] does NOT say "x >= b is worth b
   units": an order literal is 0/1, so [a * x_ge_b] tops out at [a], not [a * b]. The
   chain of literals from just past the DECLARED bound up to the current one is what
   sums to the right number of units, which is why the offset here is always the
   declared bound (fixed when the model is built) and never the current value.

   Two kinds of chain live here. [lower_bound_terms]/[upper_bound_terms] ASSERT a
   current bound, relative to the declared one. [weaken_declared] WEAKENS a variable's
   whole contribution out of a row, across its full declared width, and is the one the
   solver uses today: lib/core/justify.ml calls it to render an [Explanation.Linear_term]
   whose bound is still the declared one, which is how every [int_lin_le] pruning and
   every instance delegating to [Linear] (int_lin_eq, int_le, int_lt, int_eq, the
   reified rows) gets its chain. The assertion chains are called by test/unit/test_prop.ml
   only. Keeping the chains in one module is the point: a chain built inline in four
   places is a bug four times. *)

module Lit = Baguette_proof.Lit

(* The chain witnessing "x >= b", scaled by [coeff], together with the numeric
   contribution it makes to a right-hand side: [coeff * (b - decl_lo)].

   Terms are [(coeff, Lit.ge name v)] for [v] in [decl_lo+1 .. b] - exactly the
   prefix of the model's own expansion of [x] that is currently known true. [coeff]
   is the caller's own coefficient and MUST be positive (the sign that makes "x is at
   least its lower bound" a lower bound on the term [coeff * x]); a caller with a
   negative constraint coefficient wants [upper_bound_terms] instead, on [-coeff].

   Returns [([], 0)] when [b <= decl_lo]: the fact "x >= decl_lo" is the model's own
   constant true (docs/PROOF-FORMAT.md section 3: "x >= l is the constant true"; see
   also [Encoding.ge]'s [Holds]), so no literal is needed and it contributes nothing. *)
let lower_bound_terms ~coeff ~name ~decl_lo b =
  if coeff <= 0 then invalid_arg "Order_reason.lower_bound_terms: coeff must be > 0";
  if b <= decl_lo then ([], 0)
  else
    let n = Checked.sub b decl_lo in
    (List.init n (fun i -> (coeff, Lit.ge name (decl_lo + 1 + i))), Checked.mul coeff n)

(* The chain witnessing "x <= b", scaled by [coeff] (again a positive magnitude -
   pass [-a] when the constraint's own coefficient [a] is negative), contributing
   [coeff * (decl_hi - b)].

   Terms are [(coeff, Lit.le name u)] for [u] in [b .. decl_hi-1] - i.e.
   [(coeff, Lit.negate (Lit.ge name (u+1)))] - the suffix of the expansion currently
   known false. Returns [([], 0)] when [b >= decl_hi] (the constant true "x <= hi"). *)
let upper_bound_terms ~coeff ~name ~decl_hi b =
  if coeff <= 0 then invalid_arg "Order_reason.upper_bound_terms: coeff must be > 0";
  if b >= decl_hi then ([], 0)
  else
    let n = Checked.sub decl_hi b in
    (List.init n (fun i -> (coeff, Lit.le name (b + i))), Checked.mul coeff n)

(* ---------------------------------------------------------------------------
   Full-declared-range WEAKENING chains (the "weaken" step of D-0013)
   ---------------------------------------------------------------------------

   D-0013 justifies a bounds pruning by "weaken, divide, add": every other term of the
   row is weakened away, the sum is divided by the pruned variable's coefficient, and
   opposite bounds are added for a conflict. The weakening needs a different chain from
   [lower_bound_terms]/[upper_bound_terms] above, which ASSERT a fact ("x currently >=
   b") relative to the declared bound. This one REMOVES a variable's entire contribution
   from a row, using literal axioms. An axiom cannot assert a bound (D-0009: a bound fact
   in a [pol] needs a constraint id, not a literal), but it can weaken one away. The
   chain therefore always spans the variable's WHOLE declared width, not a prefix up to
   some current value: nothing about it is current, it is valid whatever value the
   variable takes, and that is the reason to use it instead of a fact.

   Which literal polarity cancels depends on the SIGN of the row's own coefficient for
   the term, not on which bound is being pinned. The model row a propagator justifies
   against is always the checker's ">=" normalisation of "sum coeff_i x_i <= rhs"
   (lib/proof/opb.ml's [Opb.le]), which negates every coefficient.
     - [coeff > 0]: the stored row has a NEGATIVE coefficient on the positive literal
       [x_ge_v]. An axiom of the same polarity at coefficient [coeff] cancels it exactly
       (equal magnitudes of opposite sign on one literal sum to zero), and adds nothing
       to the right-hand side.
     - [coeff < 0]: the stored row has a POSITIVE coefficient on [x_ge_v]. The negated
       literal [~x_ge_v] (the shape of [upper_bound_terms]'s) at coefficient [-coeff]
       cancels it, and since [l + ~l = 1], each step of the chain adds [-coeff] to the
       right-hand side.
   For example, in D-0013's worked example, row 6's positive-coefficient x1 term weakens
   via [~x1_ge_v] and contributes 2 per step, while row 5's negative-STORED term weakens
   via [x1_ge_v] and contributes 0. Both cases are checked against the checker in
   test/unit/test_prop.ml. The pass that made this derivation real, with [Combine],
   [Weaken] and [Model_row], was M1-T12.

   Returns [([], 0)] when [coeff = 0] (an absent term needs no weakening) or when
   [decl_lo = decl_hi] (a fixed variable has no order literals at all).

   The arithmetic goes through [Checked] (lib/core/checked.ml, which raises instead of
   wrapping; roadmap M1-T23) for the reason [Linear]'s does: a chain's numeric
   contribution is a coefficient times a declared width, and if that product wrapped,
   the [pol] the explanation renders to would state a different constant from the one
   the derivation needs. Under lib/flatzinc/compile.ml's cap on declared bounds none of
   these can raise: a width is at most 2 * max(|lo|,|hi|) and the product is at most
   twice the row's own magnitude. *)
let weaken_declared ~coeff ~name ~decl_lo ~decl_hi =
  let width = Checked.sub decl_hi decl_lo in
  if coeff = 0 || width <= 0 then ([], 0)
  else if coeff > 0 then
    (List.init width (fun i -> (coeff, Lit.ge name (decl_lo + 1 + i))), 0)
  else
    let c = Checked.neg coeff in
    (List.init width (fun i -> (c, Lit.le name (decl_lo + i))), Checked.mul c width)
