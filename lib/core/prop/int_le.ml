(* int_le: x <= y, over two integer variables.

   Consistency level: BOUNDS (docs/SPEC.md 3.2).

   [x <= y] is the degenerate linear constraint [1*x + (-1)*y <= 0], so this module does
   not propagate anything itself: [make] hands the two terms straight to [Linear.make]
   (lib/core/prop/linear.ml) and [propagate]/[vars] are [Linear]'s own functions,
   unmodified. The alternative -- a hand-written two-variable comparator computing
   [hi x' = min (hi x) (hi y)] etc. directly -- would be a handful of lines cheaper per
   call, but it would also be a second, independent place that has to get D-0010's chain
   substitution right, for a saving that will not show up anywhere near a profiler: this
   is a two-term sum, and [Linear]'s per-term overhead (a couple of list operations) is
   negligible next to the store accesses and explanation bookkeeping every propagator
   pays regardless. A smaller trusted core -- one bounds-propagation algorithm and one
   D-0010 chain substitution instead of five -- is worth more here than the hot path
   would be, so this is a thin instance, not a rewrite.

   Justification shape: identical to [int_lin_le]'s -- docs/DECISIONS.md D-0013's
   "weaken, divide, add" [Combine], over the model row [x - y <= 0] (its own row id
   passed in as [~row_id], required exactly as [Linear.make]'s is). See
   docs/PROOF-FORMAT.md section 4's `int_le` row, which currently describes a direct,
   hand-modelled `int_le` ("pol -- single model constraint, unit"); as implemented
   here the row should instead say "same as int_lin_le" -- reported back per this
   task's instructions, since that table is orchestrator-owned. *)

type t = Linear.t

let name = "int_le"
let consistency = Propagator.Bounds
let make ~row_id store x y = Linear.make ~row_id store [ (1, x); (-1, y) ] 0
let vars = Linear.vars
let propagate = Linear.propagate
