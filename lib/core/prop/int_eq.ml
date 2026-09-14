(* int_eq: x = y, over two integer variables.

   Consistency level required by M1: BOUNDS (docs/SPEC.md 3.2) -- inherited entirely
   from [Linear] via [Lin_eq].

   docs/DECISIONS.md D-0011: not a fused propagator, for exactly the reason [Lin_eq]'s
   header gives -- an equality is two model rows, and a pruning's explanation carries
   no propagator identity once it is on the trail, so one instance must justify against
   exactly one row. [make] is a two-variable specialisation of [Lin_eq.make]: it
   returns the same [(le, ge)] pair of ordinary [Linear.t] instances, for
   [1*x + (-1)*y = 0]. Post both, exactly as for [int_lin_eq]. This is a
   specialisation, not a new derivation kind, for the same reasons [Int_le]'s header
   (lib/core/prop/int_le.ml) gives for [int_le] over [int_lin_le].

   Justification shape: [Lin_eq]'s -- "two int_lin_le derivations" (docs/PROOF-FORMAT.md
   section 4's `int_lin_eq` row), i.e. each pruning is docs/DECISIONS.md D-0013's
   [Combine] over whichever of the model rows [x - y <= 0] / [y - x <= 0] the
   producing instance ([le] or [ge] respectively) was built against.

   What a DOMAIN-consistent version would need, and why this one stops short of it:
   bounds consistency only ever moves lo/hi, so it happily leaves [x] and [y] each
   sitting on values the other's domain does not contain, as long as the *intervals*
   overlap correctly -- e.g. x in {0,2,4}, y in {1,2,3} bounds-propagates to nothing
   useful (the intervals [0,4] and [1,3] already overlap on lo/hi alone). A
   domain-consistent [int_eq] would instead intersect the two domains *value by value*,
   including holes -- for every v, v is in the result iff v is in both [Domain.t]'s
   (mem, not just [lo,hi]) -- and prune each variable down to exactly that
   intersection, with an explanation that names the specific excluded value's absence
   from the other domain rather than a bound chain. That needs [Domain.remove] on
   interior holes and a different, value-indexed explanation shape; M1 does not ask for
   it and this module does not build it. *)

let make ?le_id ?ge_id store x y = Lin_eq.make ?le_id ?ge_id store [ (1, x); (-1, y) ] 0
