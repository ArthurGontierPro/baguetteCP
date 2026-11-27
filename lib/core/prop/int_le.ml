(* int_le: x <= y, over two integer variables.

   Consistency level: BOUNDS (docs/SPEC.md 3.2).

   [x <= y] is the degenerate linear constraint [1*x + (-1)*y <= 0], so this module
   propagates nothing itself: [make] hands the two terms straight to [Linear.make]
   (lib/core/prop/linear.ml) and [propagate]/[vars] are [Linear]'s own functions,
   unmodified. The rule is one trusted bounds algorithm rather than several. A
   hand-written two-variable comparator (computing [hi x' = min (hi x) (hi y)] and so on
   directly) would save a few list operations per call, which is negligible next to the
   store accesses and explanation bookkeeping every propagator pays. It would also be a
   second place that has to get the bound-fact chain right (D-0010: a bound fact is
   stated as a chain of order literals over the variable's declared range, not as one
   literal). So this is a thin instance, not a rewrite.

   Who calls it. The solver does not: lib/flatzinc/compile.ml lowers an `int_le` to its
   difference terms and posts them through [Linear] itself. [make] is the entry point
   the unit tests (test_prop, test_matrix, test_random) use to build the constraint by
   name.

   Justification shape: identical to [int_lin_le]'s, the [Combine] of D-0013's "weaken,
   divide, add" derivation, over the model row [x - y <= 0] (its own row id passed in as
   [~row_id], required exactly as [Linear.make]'s is). docs/PROOF-FORMAT.md section 4's
   `int_le` row says the same: the instance `1*x + -1*y <= 0` of `int_lin_le`. *)

type t = Linear.t

let name = "int_le"
let consistency = Propagator.Bounds
let make ~row_id store x y = Linear.make ~row_id store [ (1, x); (-1, y) ] 0
let vars = Linear.vars
let propagate = Linear.propagate
