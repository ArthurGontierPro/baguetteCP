(* int_lt: x < y, over two integer variables.

   Consistency level: BOUNDS (docs/SPEC.md 3.2).

   Over integers, [x < y] is [x <= y - 1], the degenerate linear constraint
   [1*x + (-1)*y <= -1]. As with [Int_le] (lib/core/prop/int_le.ml, read that module's
   header for the fuller case for reuse over a hand-written comparator), [make] hands
   this straight to [Linear.make] and [propagate]/[vars] are [Linear]'s own, unmodified.

   Justification shape: identical to [int_lin_le]'s -- [Cut (Trivial, Linear (units,
   units_rhs), 1, 1)] over the model row [x - y <= -1]. See docs/DECISIONS.md D-0009 and
   D-0010. docs/PROOF-FORMAT.md section 4 has no `int_lt` row yet; the one requested is
   "same as int_lin_le". *)

type t = Linear.t

let name = "int_lt"
let consistency = Propagator.Bounds
let make store x y = Linear.make store [ (1, x); (-1, y) ] (-1)
let vars = Linear.vars
let propagate = Linear.propagate
