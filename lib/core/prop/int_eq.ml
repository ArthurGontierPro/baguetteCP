(* int_eq: x = y, over two integer variables.

   Consistency level required by M1: BOUNDS (docs/SPEC.md 3.2) -- this module only ever
   tightens lo/hi. [x = y] is the degenerate linear equality [1*x + (-1)*y = 0], so
   [make] hands that straight to [Lin_eq.make] (lib/core/prop/lin_eq.ml) and
   [propagate]/[vars] are [Lin_eq]'s own, unmodified; this is a specialisation of
   [int_lin_eq], not a new derivation kind, for exactly the reasons [Int_le]'s header
   (lib/core/prop/int_le.ml) gives for [int_le] over [int_lin_le].

   Justification shape: [Lin_eq]'s -- "two int_lin_le derivations" (docs/PROOF-FORMAT.md
   section 4's `int_lin_eq` row), i.e. each pruning is [Cut (Trivial, Linear (units,
   units_rhs), 1, 1)] over whichever of the model rows [x - y <= 0] / [y - x <= 0]
   produced it (see [Lin_eq.le] / [Lin_eq.ge] for telling the two apart). There is no
   `int_eq` row in the table yet; the one requested is "same as int_lin_eq, specialised
   to two variables".

   What a DOMAIN-consistent version would need, and why this one stops short of it:
   bounds consistency only ever moves lo/hi, so it happily leaves [x] and [y] each
   sitting on values the other's domain does not contain, as long as the *intervals*
   overlap correctly -- e.g. x in {0,2,4}, y in {1,2,3} bounds-propagates to nothing
   (lo/hi already agree at [0,4] vs [1,3] once y's hi=3 caps x's hi and x's lo=0 has no
   effect... concretely hi(x) would drop to 3 and lo(y) would rise to 0, still leaving
   x=4-turned-3 a hole state and value 1 or 3 in x with no matching value in y unpruned).
   A domain-consistent [int_eq] would instead intersect the two domains *value by
   value*, including holes -- for every v, v is in the result iff v is in both
   [Domain.t]'s (mem, not just [lo,hi]) -- and prune each variable down to exactly that
   intersection, with an explanation that names the specific excluded value's absence
   from the other domain rather than a bound chain. That needs [Domain.remove] on
   interior holes and a different, value-indexed explanation shape; M1 does not ask for
   it and this module does not build it. *)

type t = Lin_eq.t

let name = "int_eq"
let consistency = Propagator.Bounds
let make store x y = Lin_eq.make store [ (1, x); (-1, y) ] 0
let vars = Lin_eq.vars
let propagate = Lin_eq.propagate
let le = Lin_eq.le
let ge = Lin_eq.ge
