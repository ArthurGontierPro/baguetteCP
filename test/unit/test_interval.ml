(* Unit tests for lib/core/interval.ml -- the proof-free arithmetic of M4-T4a.

   This module has no solver types in it, which is exactly what makes it testable the
   way nothing else in this project is: for small ranges the *whole* answer can be
   computed by enumeration, so almost every check below is "the interval function agrees
   with brute force", not "the interval function returns what I expected it to".

   Three things are deliberate about how that is done.

   1. **The sweeps cross every sign boundary.** A four-corner product and a floor
      division are the two places where a positive-only test passes on a broken
      implementation: three corners out of four suffice when both intervals are
      non-negative, and truncation *is* floor when the quotient is positive. Every
      sweep therefore ranges over intervals whose endpoints run from negative to
      positive, and the division sweep covers all four sign combinations of (a, b)
      explicitly as well.

   2. **Tightness is asserted where it is claimed, and only there.**
      [product_bounds], [square_bounds] and [square_filter] are exact, so the sweeps
      demand equality with the brute-force hull. [quotient_filter] is documented as
      sound but not exact, so its sweep demands containment -- and the test pins one
      concrete inexact instance (y in 2..3, z = 5) so that the gap is recorded rather
      than merely tolerated. Asserting equality there would be a wrong test; asserting
      containment for the exact ones would be a test that cannot see a corner go
      missing.

   3. **The independent reference for division is a float, not another integer
      routine.** [div_floor] is an alias of [Checked.floordiv], so checking it against
      a second hand-written integer floor division would mostly check that two
      copies of the same idea agree. For |a|, |b| <= 40 every value and every exact
      quotient is representable in a double, and the distance from a non-integral
      quotient to the nearest integer is at least 1/40, so [Float.floor] of the
      division is exactly right and is derived from nothing this project wrote.

   The overflow edges (min_int, max_int, min_int / -1, min_int * -1) are checked as
   raises, per D-0029: overflow raises here, it never wraps and never silently returns
   a weaker interval. *)

module I = Baguette_core.Interval
module Checked = Baguette_core.Checked

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* A sweep reports one check for the whole enumeration plus, when it fails, the first
   counterexample -- printing one line per case would bury the suite. *)
let report name n bad =
  check (Printf.sprintf "%s (%d cases)" name n) (bad = None);
  match bad with
  | Some m -> Printf.printf "       first counterexample: %s\n" m
  | None -> ()

let raises_with name pred f =
  match f () with
  | exception e when pred e -> Printf.printf "ok   %s\n" name
  | exception e ->
      incr failures;
      Printf.printf "FAIL %s (wrong exception: %s)\n" name (Printexc.to_string e)
  | _ ->
      incr failures;
      Printf.printf "FAIL %s (no exception raised)\n" name

let raises_overflow name f =
  raises_with name (function Checked.Overflow _ -> true | _ -> false) f

let raises_invalid name f =
  raises_with name (function Invalid_argument _ -> true | _ -> false) f

let returns name f =
  match f () with
  | exception e ->
      incr failures;
      Printf.printf "FAIL %s (raised %s)\n" name (Printexc.to_string e)
  | v -> check name v

let lo (i : I.t) = i.I.lo
let hi (i : I.t) = i.I.hi
let str = I.to_string

(* Every non-empty interval with endpoints in [a, b]. *)
let intervals a b =
  let acc = ref [] in
  for l = a to b do
    for h = l to b do
      acc := I.make l h :: !acc
    done
  done;
  List.rev !acc

(* ------------------------------------------------------------------- division *)

(* Independent of anything in lib/: see the header. *)
let ref_floordiv a b = int_of_float (Float.floor (float_of_int a /. float_of_int b))
let ref_ceildiv a b = int_of_float (Float.ceil (float_of_int a /. float_of_int b))

let test_division_against_float () =
  let bad = ref None and n = ref 0 in
  for a = -40 to 40 do
    for b = -40 to 40 do
      if b <> 0 then (
        incr n;
        let f = I.div_floor a b and c = I.div_ceil a b in
        if (f <> ref_floordiv a b || c <> ref_ceildiv a b) && !bad = None then
          bad :=
            Some
              (Printf.sprintf "%d / %d: floor %d (want %d), ceil %d (want %d)" a b f
                 (ref_floordiv a b) c (ref_ceildiv a b)))
    done
  done;
  report "div_floor/div_ceil match a float reference over all four sign quadrants" !n !bad

(* The defining property, which does not mention any other division: q = floor(a/b)
   iff q <= a/b < q+1, i.e. q*b <= a < (q+1)*b for b > 0 and the reverse for b < 0. *)
let test_division_characterisation () =
  let bad = ref None and n = ref 0 in
  for a = -40 to 40 do
    for b = -40 to 40 do
      if b <> 0 then (
        incr n;
        let f = I.div_floor a b and c = I.div_ceil a b in
        let ok =
          if b > 0 then f * b <= a && a < (f + 1) * b && c * b >= a && a > (c - 1) * b
          else f * b >= a && a > (f + 1) * b && c * b <= a && a < (c - 1) * b
        in
        if (not ok) && !bad = None then
          bad := Some (Printf.sprintf "a = %d, b = %d, floor %d, ceil %d" a b f c))
    done
  done;
  report "div_floor/div_ceil satisfy the bracketing inequalities" !n !bad

(* Spelled out by hand for the negative operands, and stated *against* truncation, so
   that an implementation which reverts to [Stdlib.(/)] fails here by name rather than
   only inside a sweep. *)
let test_division_negative_cases () =
  check "div_floor (-7) 2 = -4 (truncation would say -3)" (I.div_floor (-7) 2 = -4);
  check "div_ceil (-7) 2 = -3" (I.div_ceil (-7) 2 = -3);
  check "div_floor 7 (-2) = -4" (I.div_floor 7 (-2) = -4);
  check "div_ceil 7 (-2) = -3" (I.div_ceil 7 (-2) = -3);
  check "div_floor (-7) (-2) = 3" (I.div_floor (-7) (-2) = 3);
  check "div_ceil (-7) (-2) = 4 (truncation would say 3)" (I.div_ceil (-7) (-2) = 4);
  check "div_floor 7 2 = 3" (I.div_floor 7 2 = 3);
  check "div_ceil 7 2 = 4" (I.div_ceil 7 2 = 4);
  (* The two divisions the trap is about: these are the cases where Stdlib disagrees. *)
  check "div_floor differs from Stdlib (/) on a negative dividend"
    (I.div_floor (-7) 2 <> -7 / 2);
  check "div_ceil differs from Stdlib (/) on two negative operands"
    (I.div_ceil (-7) (-2) <> -7 / -2);
  (* Exact division rounds nowhere, whatever the signs. *)
  check "exact quotients are untouched in all four quadrants"
    (I.div_floor (-8) 2 = -4
    && I.div_ceil (-8) 2 = -4
    && I.div_floor 8 (-2) = -4
    && I.div_ceil 8 (-2) = -4
    && I.div_floor (-8) (-2) = 4
    && I.div_ceil (-8) (-2) = 4)

(* 2^61 and 2^61 - 1, written out because max_int/2 is the thing under test. *)
let two_to_61 = 2305843009213693952

let test_division_edges () =
  check "max_int = 2^62 - 1 on this platform" (max_int = 4611686018427387903);
  check "div_floor max_int 1 = max_int" (I.div_floor max_int 1 = max_int);
  check "div_ceil min_int 1 = min_int" (I.div_ceil min_int 1 = min_int);
  check "div_floor max_int 2 = 2^61 - 1" (I.div_floor max_int 2 = two_to_61 - 1);
  check "div_ceil max_int 2 = 2^61" (I.div_ceil max_int 2 = two_to_61);
  check "div_floor min_int 2 = -2^61" (I.div_floor min_int 2 = -two_to_61);
  check "div_ceil min_int 2 = -2^61" (I.div_ceil min_int 2 = -two_to_61);
  (* min_int / -1 = 2^62 has no representable answer. D-0029: it raises. *)
  raises_overflow "div_floor min_int (-1) raises Overflow" (fun () ->
      I.div_floor min_int (-1));
  raises_overflow "div_ceil min_int (-1) raises Overflow" (fun () ->
      I.div_ceil min_int (-1));
  check "max_int / -1 is representable and exact" (I.div_floor max_int (-1) = -max_int);
  raises_invalid "div_floor by zero raises Invalid_argument" (fun () -> I.div_floor 3 0);
  raises_invalid "div_ceil by zero raises Invalid_argument" (fun () -> I.div_ceil 3 0)

(* ---------------------------------------------------------------- square roots *)

let test_isqrt_exhaustive () =
  let bad = ref None and n = ref 0 in
  for v = 0 to 20000 do
    incr n;
    let r = I.isqrt v and c = I.ceil_isqrt v in
    let floor_ok = r >= 0 && r * r <= v && (r + 1) * (r + 1) > v in
    let ceil_ok = c >= 0 && c * c >= v && (c = 0 || (c - 1) * (c - 1) < v) in
    if ((not floor_ok) || not ceil_ok) && !bad = None then
      bad := Some (Printf.sprintf "n = %d, isqrt %d, ceil_isqrt %d" v r c)
  done;
  report "isqrt/ceil_isqrt bracket n exhaustively on 0..20000" !n !bad

let test_isqrt_around_squares () =
  let bad = ref None and n = ref 0 in
  (* From 2: at k = 1, k^2 - 1 is 0 and ceil_isqrt 0 = 0 rather than k, which is the
     right answer and not the pattern below. The small cases are in [test_isqrt_edges]. *)
  let ks = List.init 400 (fun i -> i + 2) @ [ 1_000_000; 46_341; 2_147_483_646 ] in
  List.iter
    (fun k ->
      incr n;
      let sq = k * k in
      let ok =
        I.isqrt sq = k
        && I.ceil_isqrt sq = k
        && I.isqrt (sq - 1) = k - 1
        && I.ceil_isqrt (sq - 1) = k
        && I.isqrt (sq + 1) = k
        && I.ceil_isqrt (sq + 1) = k + 1
      in
      if (not ok) && !bad = None then bad := Some (Printf.sprintf "k = %d" k))
    ks;
  report "isqrt/ceil_isqrt are exact at k^2 - 1, k^2, k^2 + 1" !n !bad

let test_isqrt_edges () =
  check "isqrt 0 = 0" (I.isqrt 0 = 0);
  check "isqrt 1 = 1" (I.isqrt 1 = 1);
  check "isqrt 2 = 1" (I.isqrt 2 = 1);
  check "isqrt 3 = 1" (I.isqrt 3 = 1);
  check "isqrt 4 = 2" (I.isqrt 4 = 2);
  check "ceil_isqrt 0 = 0" (I.ceil_isqrt 0 = 0);
  check "ceil_isqrt 2 = 2" (I.ceil_isqrt 2 = 2);
  (* max_int is the case GCS's (n+1)/2 initial estimate overflows on, so it is not an
     ornamental edge: 2^31 - 1 squared is the largest square below max_int. *)
  returns "isqrt max_int = 2^31 - 1, without overflowing the initial estimate" (fun () ->
      I.isqrt max_int = 2147483647);
  returns "ceil_isqrt max_int = 2^31" (fun () -> I.ceil_isqrt max_int = 2147483648);
  returns "isqrt is exact at the largest representable square" (fun () ->
      I.isqrt (2147483647 * 2147483647) = 2147483647);
  raises_invalid "isqrt (-1) raises Invalid_argument" (fun () -> I.isqrt (-1));
  raises_invalid "isqrt min_int raises Invalid_argument" (fun () -> I.isqrt min_int)

(* -------------------------------------------------------------- multiplication *)

let brute_product x y =
  let mn = ref max_int and mx = ref min_int in
  for a = lo x to hi x do
    for b = lo y to hi y do
      let p = a * b in
      if p < !mn then mn := p;
      if p > !mx then mx := p
    done
  done;
  (!mn, !mx)

let test_product_bounds_brute () =
  let bad = ref None and n = ref 0 in
  let is = intervals (-5) 5 in
  List.iter
    (fun x ->
      List.iter
        (fun y ->
          incr n;
          let got = I.product_bounds x y in
          let want_lo, want_hi = brute_product x y in
          if (lo got <> want_lo || hi got <> want_hi) && !bad = None then
            bad :=
              Some
                (Printf.sprintf "x = %s, y = %s: got %s, want [%d, %d]" (str x) (str y)
                   (str got) want_lo want_hi))
        is)
    is;
  report "product_bounds is exactly the brute-force hull over -5..5 x -5..5" !n !bad

let test_product_bounds_corners () =
  (* Chosen so that each of the four corners is, in some case, the unique extreme:
     dropping any one of them changes an answer below. *)
  let pb a b c d = I.product_bounds (I.make a b) (I.make c d) in
  check "product_bounds [-3,2] [-5,7] = [-21, 15] (lo*hi is the min, lo*lo the max)"
    (pb (-3) 2 (-5) 7 = I.make (-21) 15);
  check "product_bounds [2,3] [-5,7] = [-15, 21] (hi*lo is the min, hi*hi the max)"
    (pb 2 3 (-5) 7 = I.make (-15) 21);
  check "product_bounds [-3,-2] [-5,-4] = [8, 15] (both negative: hi*hi is the min)"
    (pb (-3) (-2) (-5) (-4) = I.make 8 15);
  check "product_bounds [0,0] [-5,7] = [0, 0]" (pb 0 0 (-5) 7 = I.make 0 0);
  check "product_bounds is symmetric" (pb (-3) 2 (-5) 7 = pb (-5) 7 (-3) 2)

let test_product_bounds_overflow () =
  let m x = I.make x x in
  raises_overflow "product_bounds max_int * 2 raises Overflow" (fun () ->
      I.product_bounds (m max_int) (m 2));
  raises_overflow "product_bounds min_int * -1 raises Overflow" (fun () ->
      I.product_bounds (m min_int) (m (-1)));
  raises_overflow "an overflowing corner raises even when the others are tiny" (fun () ->
      I.product_bounds (I.make min_int 1) (I.make (-1) 1));
  returns "min_int * 1 is representable and is not refused" (fun () ->
      I.product_bounds (m min_int) (m 1) = I.make min_int min_int);
  returns "a large product just inside the range is computed, not refused" (fun () ->
      I.product_bounds (I.make 0 1_000_000_000) (I.make 0 4_000_000_000)
      = I.make 0 4_000_000_000_000_000_000)

(* --------------------------------------------------------------------- squares *)

let brute_square x =
  let mn = ref max_int and mx = ref min_int in
  for a = lo x to hi x do
    let p = a * a in
    if p < !mn then mn := p;
    if p > !mx then mx := p
  done;
  (!mn, !mx)

let test_square_bounds_brute () =
  let bad = ref None and n = ref 0 in
  List.iter
    (fun x ->
      incr n;
      let got = I.square_bounds x in
      let want_lo, want_hi = brute_square x in
      if (lo got <> want_lo || hi got <> want_hi) && !bad = None then
        bad :=
          Some
            (Printf.sprintf "x = %s: got %s, want [%d, %d]" (str x) (str got) want_lo
               want_hi))
    (intervals (-6) 6);
  report "square_bounds is exactly the brute-force hull of v*v over -6..6" !n !bad

let test_square_bounds_is_not_product () =
  (* The reason the two are separate functions, made observable rather than asserted in
     a comment: over an interval spanning zero they give different answers, and the
     product's is wrong for a square. *)
  let x = I.make (-3) 2 in
  check "square_bounds [-3,2] = [0, 9]" (I.square_bounds x = I.make 0 9);
  check "product_bounds [-3,2] [-3,2] = [-6, 9] -- weaker, and not a square's range"
    (I.product_bounds x x = I.make (-6) 9);
  check "square_bounds is never negative where product_bounds is"
    (lo (I.square_bounds x) > lo (I.product_bounds x x));
  check "away from zero the two agree"
    (I.square_bounds (I.make 2 5) = I.product_bounds (I.make 2 5) (I.make 2 5));
  raises_overflow "square_bounds min_int raises Overflow" (fun () ->
      I.square_bounds (I.make min_int 0))

(* -------------------------------------------------------------- square_filter *)

let brute_square_filter x z =
  let mn = ref max_int and mx = ref min_int in
  for v = lo x to hi x do
    let s = v * v in
    if s >= lo z && s <= hi z then (
      if v < !mn then mn := v;
      if v > !mx then mx := v)
  done;
  if !mn > !mx then None else Some (!mn, !mx)

let test_square_filter_brute () =
  let bad = ref None and n = ref 0 in
  let xs = intervals (-6) 6 and zs = intervals (-6) 12 in
  List.iter
    (fun x ->
      List.iter
        (fun z ->
          incr n;
          let got = I.square_filter ~x ~z in
          let want = brute_square_filter x z in
          let ok =
            match want with
            | None -> I.is_empty got
            | Some (l, h) -> (not (I.is_empty got)) && lo got = l && hi got = h
          in
          if (not ok) && !bad = None then
            bad :=
              Some
                (Printf.sprintf "x = %s, z = %s: got %s, want %s" (str x) (str z)
                   (str got)
                   (match want with
                   | None -> "{}"
                   | Some (l, h) -> Printf.sprintf "[%d, %d]" l h)))
        zs)
    xs;
  report "square_filter is exactly the brute-force hull (x in -6..6, z in -6..12)" !n !bad

let test_square_filter_cases () =
  let sf xl xh zl zh = I.square_filter ~x:(I.make xl xh) ~z:(I.make zl zh) in
  check "square_filter keeps a range that straddles the excluded middle"
    (sf (-5) 5 4 9 = I.make (-3) 3);
  check "a range starting inside the hole jumps it rather than nudging past it"
    (sf 0 5 4 9 = I.make 2 3);
  check "a range entirely inside the hole is empty" (I.is_empty (sf (-1) 1 4 9));
  check "a range ending inside the hole jumps to the negative side"
    (sf (-5) 0 4 9 = I.make (-3) (-2));
  check "no square lies in 5..8, so that range is empty" (I.is_empty (sf (-1) 5 5 8));
  check "negative z is unsatisfiable" (I.is_empty (sf (-5) 5 (-9) (-4)));
  check "z containing 0 admits 0" (sf (-5) 5 0 9 = I.make (-3) 3);
  check "the upper bound is isqrt, not a rounded-up square root"
    (sf 0 100 0 10 = I.make 0 3);
  returns "square_filter on a full-width z does not overflow" (fun () ->
      I.square_filter ~x:(I.make 0 max_int) ~z:(I.make 0 max_int) = I.make 0 2147483647)

(* ------------------------------------------------------------ quotient_filter *)

let supported_x ~y ~z x =
  let ok = ref false in
  for vy = lo y to hi y do
    let p = x * vy in
    if p >= lo z && p <= hi z then ok := true
  done;
  !ok

(* The sweep range for x: with |z| <= 6 and |y| >= 1 every supported x has |x| <= 6,
   except in the No_filter case where every x is supported, so -12..12 is wide enough
   to catch a bound that is too narrow and to confirm No_filter's claim. *)
let x_range = 12

let test_quotient_filter_brute () =
  let bad = ref None and n = ref 0 in
  let ys = intervals (-4) 4 and zs = intervals (-6) 6 in
  let inexact = ref 0 in
  List.iter
    (fun y ->
      List.iter
        (fun z ->
          incr n;
          let got = I.quotient_filter ~y ~z in
          let sup = ref [] in
          for x = -x_range to x_range do
            if supported_x ~y ~z x then sup := x :: !sup
          done;
          let sup = List.rev !sup in
          let fail m =
            if !bad = None then
              bad := Some (Printf.sprintf "y = %s, z = %s: %s" (str y) (str z) m)
          in
          match got with
          | I.No_filter ->
              (* No_filter claims nothing can be said, so everything must be
                 supported -- otherwise it is not "no information", it is a missed
                 pruning dressed up as one. *)
              if List.length sup <> (2 * x_range) + 1 then
                fail "No_filter but some x in the sweep is unsupported"
          | I.Empty_because_y_zero ->
              if sup <> [] then fail "Empty_because_y_zero but some x is supported"
          | I.Bounds b ->
              List.iter
                (fun x ->
                  if not (I.mem b x) then
                    fail (Printf.sprintf "supported x = %d outside %s" x (str b)))
                sup;
              (* Record, without asserting, how often the documented inexactness
                 bites: the bound is allowed to be wider than the hull. *)
              let exact =
                match sup with
                | [] -> I.is_empty b
                | _ -> lo b = List.hd sup && hi b = List.nth sup (List.length sup - 1)
              in
              if not exact then incr inexact)
        zs)
    ys;
  report "quotient_filter contains every supported x (y in -4..4, z in -6..6)" !n !bad;
  Printf.printf "       (%d of %d cases are wider than the exact hull -- documented)\n"
    !inexact !n

(* Where the filter *is* exact, say so and check it: a fixed non-zero y makes the
   answer [ceil(z_lo/y), floor(z_hi/y)] with every integer between supported. This is
   the check that sees a swapped div_ceil/div_floor, which containment alone cannot. *)
let test_quotient_filter_exact_for_fixed_y () =
  let bad = ref None and n = ref 0 in
  List.iter
    (fun k ->
      List.iter
        (fun z ->
          if k <> 0 then (
            incr n;
            let y = I.make k k in
            match I.quotient_filter ~y ~z with
            | I.Bounds b ->
                let sup = ref [] in
                for x = -x_range to x_range do
                  if supported_x ~y ~z x then sup := x :: !sup
                done;
                let sup = List.rev !sup in
                let ok =
                  match sup with
                  | [] -> I.is_empty b
                  | _ -> lo b = List.hd sup && hi b = List.nth sup (List.length sup - 1)
                in
                if (not ok) && !bad = None then
                  bad :=
                    Some
                      (Printf.sprintf "y = %d, z = %s: got %s, support %s" k (str z)
                         (str b)
                         (String.concat "," (List.map string_of_int sup)))
            | _ ->
                if !bad = None then
                  bad := Some (Printf.sprintf "y = %d, z = %s: not Bounds" k (str z))))
        (intervals (-6) 6))
    [ -4; -3; -2; -1; 1; 2; 3; 4 ];
  report "quotient_filter is exact when y is fixed and non-zero" !n !bad

let test_quotient_filter_cases () =
  let qf yl yh zl zh = I.quotient_filter ~y:(I.make yl yh) ~z:(I.make zl zh) in
  check "0 in y and 0 in z: nothing can be said" (qf 0 5 0 7 = I.No_filter);
  check "0 in y and 0 in z, both straddling" (qf (-2) 3 (-4) 4 = I.No_filter);
  check "y fixed to zero and z excluding zero: nothing is possible"
    (qf 0 0 3 7 = I.Empty_because_y_zero);
  check "y fixed to zero and z containing zero is No_filter, not empty"
    (qf 0 0 0 5 = I.No_filter);
  check "y straddles zero, z is sign-fixed: the symmetric magnitude bound"
    (qf (-2) 3 4 9 = I.Bounds (I.make (-9) 9));
  check "a zero endpoint of y is dropped when z excludes zero"
    (qf 0 5 3 7 = I.Bounds (I.make 1 7));
  check "a negative zero endpoint of y is dropped the same way"
    (qf (-5) 0 3 7 = I.Bounds (I.make (-7) (-1)));
  check "sign-fixed y takes the quotient corners"
    (qf 2 3 (-3) 7 = I.Bounds (I.make (-1) 3));
  (* The documented inexactness, pinned to a concrete instance so that it is a known
     property rather than a surprise: no x satisfies x*y = 5 for y in 2..3, and the
     filter still answers [2, 2]. *)
  check "the documented inexact case still answers [2, 2] for y in 2..3, z = 5"
    (qf 2 3 5 5 = I.Bounds (I.make 2 2));
  check "and brute force agrees nothing is supported there"
    (not
       (List.exists
          (fun x -> supported_x ~y:(I.make 2 3) ~z:(I.make 5 5) x)
          (List.init 25 (fun i -> i - 12))))

let test_quotient_filter_edges () =
  raises_overflow "quotient_filter raises when |z| overflows in the straddling case"
    (fun () -> I.quotient_filter ~y:(I.make (-1) 1) ~z:(I.make min_int min_int));
  raises_overflow "quotient_filter raises on the min_int / -1 corner" (fun () ->
      I.quotient_filter ~y:(I.make (-1) (-1)) ~z:(I.make min_int min_int));
  returns "min_int / 1 is representable and is not refused" (fun () ->
      I.quotient_filter ~y:(I.make 1 1) ~z:(I.make min_int min_int)
      = I.Bounds (I.make min_int min_int));
  returns "a full-width z against a unit y is computed" (fun () ->
      I.quotient_filter ~y:(I.make 1 1) ~z:(I.make 1 max_int)
      = I.Bounds (I.make 1 max_int))

(* ------------------------------------------------------------------ interface *)

let test_interval_type () =
  check "is_empty" (I.is_empty (I.make 3 2) && not (I.is_empty (I.make 3 3)));
  check "empty is empty" (I.is_empty I.empty);
  check "mem" (I.mem (I.make (-2) 4) (-2) && I.mem (I.make (-2) 4) 4);
  check "mem excludes outside"
    ((not (I.mem (I.make (-2) 4) 5)) && not (I.mem (I.make (-2) 4) (-3)));
  check "to_string" (I.to_string (I.make (-2) 4) = "[-2, 4]" && I.to_string I.empty = "{}")

(* An empty input interval is a caller bug, not a case with an answer: every entry
   point rejects it rather than returning something that looks like a bound. *)
let test_empty_inputs_rejected () =
  let e = I.make 3 2 and ok = I.make 0 4 in
  raises_invalid "product_bounds rejects an empty left input" (fun () ->
      I.product_bounds e ok);
  raises_invalid "product_bounds rejects an empty right input" (fun () ->
      I.product_bounds ok e);
  raises_invalid "square_bounds rejects an empty input" (fun () -> I.square_bounds e);
  raises_invalid "square_filter rejects an empty x" (fun () -> I.square_filter ~x:e ~z:ok);
  raises_invalid "square_filter rejects an empty z" (fun () -> I.square_filter ~x:ok ~z:e);
  raises_invalid "quotient_filter rejects an empty y" (fun () ->
      I.quotient_filter ~y:e ~z:ok);
  raises_invalid "quotient_filter rejects an empty z" (fun () ->
      I.quotient_filter ~y:ok ~z:e)

let () =
  test_division_against_float ();
  test_division_characterisation ();
  test_division_negative_cases ();
  test_division_edges ();
  test_isqrt_exhaustive ();
  test_isqrt_around_squares ();
  test_isqrt_edges ();
  test_product_bounds_brute ();
  test_product_bounds_corners ();
  test_product_bounds_overflow ();
  test_square_bounds_brute ();
  test_square_bounds_is_not_product ();
  test_square_filter_brute ();
  test_square_filter_cases ();
  test_quotient_filter_brute ();
  test_quotient_filter_exact_for_fixed_y ();
  test_quotient_filter_cases ();
  test_quotient_filter_edges ();
  test_interval_type ();
  test_empty_inputs_rejected ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ninterval unit tests passed"
