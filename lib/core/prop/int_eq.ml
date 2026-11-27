(* int_eq: x = y, over two integer variables.

   Consistency level: BOUNDS (docs/SPEC.md 3.2), inherited entirely from [Linear] through
   [Lin_eq]. Like [Lin_eq], this module builds two [Linear.t] instances and has no
   [consistency] value of its own.

   [make] is the two-variable case of [Lin_eq.make]: it returns the same [(le, ge)] pair
   of ordinary [Linear.t] instances, for [1*x + (-1)*y = 0]. Post both, exactly as for
   [int_lin_eq]. It is not a fused propagator, for the reason [Lin_eq]'s header gives: an
   equality is two model rows, and each instance justifies against the one row it names
   (D-0011, one instance one row). It is a specialisation, not a new derivation kind, for
   the reason [Int_le]'s header (lib/core/prop/int_le.ml) gives for [int_le] over
   [int_lin_le]: one bounds algorithm and one justification to trust instead of several.

   Who calls it. The solver does not: lib/flatzinc/compile.ml lowers an `int_eq` to its
   difference terms and posts them through [Lin_eq.make] itself. [make] is the entry
   point the unit tests (test_prop, test_matrix, test_random) use to build the
   constraint by name.

   Justification shape: [Lin_eq]'s, "two int_lin_le derivations" (docs/PROOF-FORMAT.md
   section 4's `int_eq` and `int_lin_eq` rows). Each pruning is [Linear]'s [Combine], the
   "weaken, divide, add" derivation of D-0013, over whichever of the model rows
   [x - y <= 0] / [y - x <= 0] the producing instance ([le] or [ge] respectively) was
   built against.

   What a DOMAIN-consistent version would need, and why this one stops short of it.
   Bounds consistency only ever moves lo/hi, so it leaves [x] and [y] each sitting on
   values the other's domain does not contain as long as the INTERVALS agree. For
   example x in {0,2,4}, y in {1,2,3} bounds-propagates to nothing useful, because the
   intervals [0,4] and [1,3] already overlap. A domain-consistent [int_eq] would
   intersect the two domains value by value, holes included (v stays iff [Domain.mem]
   holds for both, not just [lo,hi]), and prune each variable to exactly that
   intersection, with an explanation that names the excluded value's absence from the
   other domain rather than a bound chain. That needs [Store.remove] on interior values
   and a value-indexed explanation shape. SPEC 3.2 asks only for bounds here, and this
   module does not build the stronger version. *)

let make ~le_id ~ge_id store x y = Lin_eq.make ~le_id ~ge_id store [ (1, x); (-1, y) ] 0
