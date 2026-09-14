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
    let n = b - decl_lo in
    (List.init n (fun i -> (coeff, Lit.ge name (decl_lo + 1 + i))), coeff * n)

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
    let n = decl_hi - b in
    (List.init n (fun i -> (coeff, Lit.le name (b + i))), coeff * n)
