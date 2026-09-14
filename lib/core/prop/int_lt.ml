(* int_lt: x < y, over two integer variables.

   Consistency level: BOUNDS (docs/SPEC.md 3.2).

   Over integers, [x < y] is [x <= y - 1], the degenerate linear constraint
   [1*x + (-1)*y <= -1]. As with [Int_le] (lib/core/prop/int_le.ml, read that module's
   header for the fuller case for reuse over a hand-written comparator), [make] hands
   this straight to [Linear.make] and [propagate]/[vars] are [Linear]'s own, unmodified.

   Justification shape: identical to [int_lin_le]'s -- docs/DECISIONS.md D-0013's
   [Combine] over the model row [x - y <= -1] (its own row id passed in as
   [~row_id]). docs/PROOF-FORMAT.md section 4 has no `int_lt` row yet; the one
   requested is "same as int_lin_le". *)

type t = Linear.t

let name = "int_lt"
let consistency = Propagator.Bounds
let make ?row_id store x y = Linear.make ?row_id store [ (1, x); (-1, y) ] (-1)
let vars = Linear.vars
let propagate = Linear.propagate
