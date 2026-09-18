(* Order-encoding "bound fact" chains, shared by every propagator that appeals to a
   variable's current bound in an [Explanation.Linear]/[Explanation.Cut].

   docs/DECISIONS.md D-0010: a bound fact must be stated in the *same currency* as the
   model row a propagator's explanation combines with, which is the order encoding's own
   substitution

     x = lo_decl + sum_{v = lo_decl+1}^{hi_decl} [x >= v]

   (see [Encoding.expand_int_lin_le] / [Encoding.linear_terms_int_lin_le] in
   lib/proof/encoding.ml, which performs the identical substitution on the model side -
   read it, don't edit it, and note the two must agree on the constant or the pieces
   don't combine). A single literal [x_ge_b] is *not* a restatement of "x >= b costs b
   units": an order literal is 0/1, so [a * x_ge_b] tops out at [a], not [a * b]. The
   chain of literals from just past the *declared* bound up to the *current* one is what
   actually sums to the right number of units, which is why the offset here is always the
   declared bound (fixed at the model's construction) and never the raw current value.

   [int_lin_le] (lib/core/prop/linear.ml) is the reference propagator specifically so
   that int_lin_eq, int_le, int_lt and the M4 globals can call this module instead of
   rebuilding the chain themselves - a chain built inline four times is a bug four
   times. *)

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
   M1-T12 / docs/DECISIONS.md D-0013: full-declared-range *weakening* chains.

   [lower_bound_terms]/[upper_bound_terms] above build a chain that *asserts* a
   fact ("x currently >= b"), relative to the declared bound, for use in a [rup]
   row (D-0010). D-0013 needs a different chain: one that *weakens a variable's
   entire contribution out of a row*, via literal axioms (D-0009: an axiom cannot
   assert a bound, but it can weaken one away). That chain always spans the
   variable's *whole* declared width, not a prefix relative to some current value
   -- there is nothing "current" about it, it is valid regardless of what the
   variable turns out to be, which is the whole point of using it instead of a
   fact.

   Which literal polarity cancels depends on the *sign* of the row's own
   coefficient for that term, not on which bound (lower/upper) is being pinned:
   the model row a propagator justifies against is always the checker's ">="
   normalisation of "sum coeff_i x_i <= rhs" (lib/proof/opb.ml's [Opb.le]), which
   negates every coefficient. So a term with [coeff > 0] appears in the *stored*
   row with a *negative* coefficient on the positive literal [x_ge_v] -- cancelling
   it needs an axiom of the *same* polarity, at coefficient [coeff], and nets to
   the row exactly (opposite-sign equal-magnitude coefficients on the same literal
   sum to zero: nothing is added to the right-hand side). A term with [coeff < 0]
   appears with a *positive* stored coefficient on [x_ge_v] -- cancelling it needs
   the *negated* literal [~x_ge_v] (same shape as [upper_bound_terms]'s), at
   coefficient [-coeff], and (same-variable opposite-polarity equal-magnitude
   literals sum to a constant) adds [-coeff] to the right-hand side for every step
   of the chain. Both cases are checked directly against the checker in
   test/unit/test_prop.ml and are exactly D-0013's worked example (row 6's
   positive-coefficient x1 term weakens via [~x1_ge_v], contributing 2 per step;
   row 5's negative-*stored* term weakens via [x1_ge_v], contributing 0).

   Returns [([], 0)] when [coeff = 0] (an absent term needs no weakening) or when
   [decl_lo = decl_hi] (a fixed variable has no order literals at all). *)
(* The arithmetic here goes through [Checked] (lib/core/checked.ml, roadmap M1-T23)
   for the same reason [Linear]'s does: a chain's numeric contribution is a
   coefficient times a declared width, and if that product wraps the [pol] the
   explanation renders to states a different constant from the one the derivation
   needs. Under lib/flatzinc/compile.ml's cap none of these can raise -- a width is at
   most 2 * max(|lo|,|hi|) and the product is at most twice the row's own magnitude. *)
let weaken_declared ~coeff ~name ~decl_lo ~decl_hi =
  let width = Checked.sub decl_hi decl_lo in
  if coeff = 0 || width <= 0 then ([], 0)
  else if coeff > 0 then
    (List.init width (fun i -> (coeff, Lit.ge name (decl_lo + 1 + i))), 0)
  else
    let c = Checked.neg coeff in
    (List.init width (fun i -> (c, Lit.le name (decl_lo + i))), Checked.mul c width)
