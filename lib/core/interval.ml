(* Integer interval arithmetic: multiplication, squaring and division of bounds.

   ---------------------------------------------------------------------------
   What this module is, and what it deliberately is not (roadmap M4-T4a)
   ---------------------------------------------------------------------------

   A port of GCS's [constraints/innards/product_bounds.hh] -- free functions over
   integers with no solver types at all. There is no [Store], no [Explanation], no
   [Encoding] and no [Var] in this file, and there should never be one: M4-T4b builds
   [int_times]/[int_div]/[int_abs] *on top of* this, and the point of the split is that
   everything here is checkable by brute force over small ranges, with no proof
   machinery and no scene to set up. test/unit/test_interval.ml does exactly that.

   Nothing here prunes anything. These functions answer arithmetic questions --
   "what is the range of x*y over this box?", "which x can satisfy x*y = z?" -- and a
   propagator turns an answer into a pruning, with its own explanation. A bound this
   module computes is not a justification for anything on its own.

   ---------------------------------------------------------------------------
   Overflow (docs/DECISIONS.md D-0029)
   ---------------------------------------------------------------------------

   Multiplying two bounds is precisely where D-0029's soundness gap lived: a wrapped
   product pruned wrongly *and* the .opb row was folded from the same wrapped
   arithmetic, so the checker agreed with the solver because both were wrong. A
   four-corner product bound is four multiplications, so this module is four times that
   same hazard and it uses [Checked] rather than [*] and [+] throughout.

   Per function, either the checked operation is used or the absence of overflow is
   argued in a comment at the site. The rule followed here is D-0029's: overflow
   *raises*, it never wraps and never quietly returns a weaker answer. A caller that
   would rather decline than fail may catch [Checked.Overflow] -- but it must then also
   know that no artefact has been written from the same arithmetic, which is a question
   about the caller and not about this module.

   [Checked.limit] (max_int/16) keeps the raise unreachable for any model the CLI
   accepts, and none of the guards below rely on that: the raise is real and tested.

   ---------------------------------------------------------------------------
   Division rounds toward negative/positive infinity, never toward zero
   ---------------------------------------------------------------------------

   [Stdlib.(/)] truncates toward zero. For bounds reasoning that is simply the wrong
   function: with x in 1..10 and 2*x <= -3, the largest admissible x is
   floor(-3/2) = -2, and truncation answers -1. The trap is already worked around in
   lib/core/prop/linear.ml (which now re-exports [Checked]'s versions under its own
   names), and [div_floor]/[div_ceil] here are [Checked.floordiv]/[Checked.ceildiv]
   under the names the GCS header uses. They are aliases and not a second
   implementation on purpose -- two roundings that must agree is how D-0009 started.

   The test file checks their rounding against an independent float reference rather
   than assuming it, over every sign combination, because "we reused the shared one" is
   not evidence about what the shared one does.

   **A warning for M4-T4b, which is easy to get backwards.** This rounding is about
   *bounds*, not about what [int_div] means. The FlatZinc/MiniZinc [int_div] relation
   truncates toward zero, with the remainder taking the dividend's sign, and the roadmap
   records that as a SPEC addition M4-T4b needs before any code. The two are not in
   conflict and must not be conflated: the relation says which triples (x, y, q) are
   solutions, while [div_floor]/[div_ceil] answer "what is the widest bound this
   constraint permits", which rounds outward whatever the relation does. A propagator
   that used the relation's rounding to compute a bound would prune values that have
   support. *)

(* An integer interval. [lo > hi] means empty, which [square_filter] can return and
   which callers must test with [is_empty] before reading the bounds. *)
type t = { lo : int; hi : int }

let make lo hi = { lo; hi }
let is_empty i = i.lo > i.hi
let empty = { lo = 1; hi = 0 }
let mem i v = i.lo <= v && v <= i.hi
let to_string i = if is_empty i then "{}" else Printf.sprintf "[%d, %d]" i.lo i.hi

(* Every function below takes its *inputs* as non-empty intervals: a propagator asks
   these questions about live domains, and a live domain is never empty (I-D1 -- an
   emptied domain is a conflict, not a value). Passing an empty one is a caller bug
   rather than a case with a right answer, so it is rejected loudly. *)
let require_nonempty who i =
  if is_empty i then
    invalid_arg (Printf.sprintf "Interval.%s: empty input %s" who (to_string i))

(* ------------------------------------------------------------------- division *)

(* Floor division: the largest q with q*b <= a for b > 0 (and the analogous rounding
   toward -infinity for b < 0). Raises [Invalid_argument] on b = 0 and
   [Checked.Overflow] on the one quotient with no representable answer, min_int / -1.
   Total otherwise. *)
let div_floor a b = Checked.floordiv a b

(* Ceiling division: the smallest q with q*b >= a for b > 0. Same two failures. *)
let div_ceil a b = Checked.ceildiv a b

(* ---------------------------------------------------------------- square roots *)

(* Floor of the square root. Total on n >= 0; [Invalid_argument] on n < 0 (there is no
   answer, and returning 0 would quietly make a wrong bound look like a right one).

   Newton's method on integers. The initial estimate must be >= isqrt n for the descent
   to be monotone; ceil(n/2) is, for every n >= 2, since n/2 + 1 - sqrt n =
   ((sqrt n - 1)^2 + 1)/2 > 0. GCS writes that estimate as (n+1)/2, which *overflows at
   max_int*; [n/2 + n mod 2] is the same number and does not.

   The sum inside the loop cannot overflow either: x stays in [isqrt n, ceil(n/2)] and
   x + n/x is maximised at the ends of that range, giving at most n/2 + 2. It is still
   written with [Checked.add], so a mistake in that argument raises instead of wrapping.
   x is never 0 (it stays >= isqrt n >= 1 for n >= 2), so n/x is never a division by
   zero. *)
let isqrt n =
  if n < 0 then invalid_arg (Printf.sprintf "Interval.isqrt: %d is negative" n);
  if n < 2 then n
  else
    let x = ref n and y = ref ((n / 2) + (n mod 2)) in
    while !y < !x do
      x := !y;
      y := Checked.add !x (n / !x) / 2
    done;
    !x

(* Ceiling of the square root. [r*r] cannot overflow: r = isqrt n, so r*r <= n. It is
   written with [Checked.mul] regardless, for the same reason as above. *)
let ceil_isqrt n =
  let r = isqrt n in
  if Checked.mul r r = n then r else r + 1

(* -------------------------------------------------------------- multiplication *)

(* Exact bounds of x*y over the box x by y: the extremes of a bilinear function on a
   box are attained at its corners, so the four corner products are the whole story and
   the answer is tight, not merely sound.

   Four multiplications, each [Checked.mul]; any of them may raise [Checked.Overflow].
   This is the function D-0029 is about. *)
let product_bounds x y =
  require_nonempty "product_bounds" x;
  require_nonempty "product_bounds" y;
  let a = Checked.mul x.lo y.lo in
  let b = Checked.mul x.lo y.hi in
  let c = Checked.mul x.hi y.lo in
  let d = Checked.mul x.hi y.hi in
  { lo = min (min a b) (min c d); hi = max (max a b) (max c d) }

(* Exact bounds of x*x for x in this interval. Kept separate from [product_bounds x x]
   and not derived from it, because the two are genuinely different functions: over
   [-3, 2], product_bounds gives [-6, 9] -- a product of two *independent* values -- and
   a square is never negative, so the answer here is [0, 9]. Using the general one for a
   square is sound and weak; using this one for a product would be unsound.

   Two multiplications, each [Checked.mul]; may raise [Checked.Overflow] (at min_int,
   for one). *)
let square_bounds x =
  require_nonempty "square_bounds" x;
  let lo2 = Checked.mul x.lo x.lo and hi2 = Checked.mul x.hi x.hi in
  if x.lo <= 0 && 0 <= x.hi then { lo = 0; hi = max lo2 hi2 }
  else { lo = min lo2 hi2; hi = max lo2 hi2 }

(* ------------------------------------------------------------------ filtering *)

(* The hull of { v in x : v*v in z } -- what squaring can tell you about x. May return
   an empty interval when nothing is supported; callers must check [is_empty].

   The supported set is x intersected with ([-u, -m] union [m, u]), where u = isqrt z.hi
   bounds |v| above and m = ceil_isqrt z.lo bounds it below. That union has a hole in
   the middle, which is why this cannot be phrased as one intersection: if the surviving
   range lies entirely inside the hole the answer is empty, and if it merely *starts*
   inside the hole the bound jumps the hole rather than nudging past it.

   The result is the exact hull, not merely sound: each endpoint returned is itself a
   supported value whenever the result is non-empty (the test file asserts this against
   brute force rather than taking the argument's word for it).

   No overflow is possible: isqrt and ceil_isqrt of a non-negative argument return a
   value in [0, 3037000499], and the only arithmetic applied to them is negation. *)
let square_filter ~x ~z =
  require_nonempty "square_filter" x;
  require_nonempty "square_filter" z;
  if z.hi < 0 then empty
  else
    let u = isqrt z.hi in
    let lo = ref (max x.lo (-u)) and hi = ref (min x.hi u) in
    if z.lo > 0 then (
      let m = ceil_isqrt z.lo in
      if !lo > -m then lo := max !lo m;
      if !hi < m then hi := min !hi (-m));
    { lo = !lo; hi = !hi }

(* What the bounds of y and z say about x in x*y = z. Three outcomes, kept as a variant
   rather than collapsed into an interval, because "nothing can be said" and "nothing is
   possible" are opposite answers and an interval of [min_int, max_int] would be a lie
   about the first and unrepresentable for the second. *)
type filter =
  | No_filter  (** 0 is in both y and z: y = 0, z = 0 supports every x. *)
  | Empty_because_y_zero  (** y is fixed to 0 and z excludes 0: no x works. *)
  | Bounds of t  (** x lies in this interval, which may itself be empty. *)

(* The case split is JaCoP's, by way of GCS. It is **sound but not exact**, and that is
   inherited deliberately rather than overlooked:

   - in the sign-fixed-y case the corner quotients bound the *rational* range of z/y,
     and an integer endpoint of that range need not be an exact quotient of any
     admissible pair (y in 2..3, z in 5..5 returns [2, 2] where nothing is supported);
   - in the y-spans-zero case only the symmetric magnitude bound |x| <= max |z| is
     derived, since |y| >= 1 there.

   The test file measures that gap against brute force instead of assuming it is small;
   what it asserts is containment, plus tightness for the cases that are exact.

   Overflow: [Checked.abs] in the spanning case raises at z = min_int, and the eight
   corner quotients raise on min_int / -1. Nothing else multiplies. *)
let quotient_filter ~y ~z =
  require_nonempty "quotient_filter" y;
  require_nonempty "quotient_filter" z;
  if z.lo <= 0 && z.hi >= 0 && y.lo <= 0 && y.hi >= 0 then No_filter
  else if y.lo = 0 && y.hi = 0 then Empty_because_y_zero
  else if y.lo < 0 && y.hi > 0 then
    (* y contains -1, 0 and 1, and z is entirely positive or entirely negative, so
       y <> 0 and |x| = |z| / |y| <= |z|. *)
    let largest = max (Checked.abs z.lo) (Checked.abs z.hi) in
    Bounds { lo = -largest; hi = largest }
  else
    (* y does not straddle zero. It may still have a zero endpoint, and that endpoint
       can be dropped: reaching here means z excludes 0 (the first branch would have
       fired otherwise), and y = 0 forces z = 0. *)
    let y_lo = if y.lo = 0 then 1 else y.lo in
    let y_hi = if y.hi = 0 then -1 else y.hi in
    (* ceil and floor are monotone, so the min of the four ceilings is the ceiling of
       the smallest corner quotient and the max of the four floors is the floor of the
       largest -- i.e. exactly the integer hull of the rational range of z/y. *)
    let smallest =
      min
        (min (div_ceil z.lo y_lo) (div_ceil z.lo y_hi))
        (min (div_ceil z.hi y_lo) (div_ceil z.hi y_hi))
    in
    let largest =
      max
        (max (div_floor z.lo y_lo) (div_floor z.lo y_hi))
        (max (div_floor z.hi y_lo) (div_floor z.hi y_hi))
    in
    Bounds { lo = smallest; hi = largest }
