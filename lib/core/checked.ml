(* Checked integer arithmetic, and the compile-time cap that keeps it off the hot path.

   ---------------------------------------------------------------------------
   Why this module exists (roadmap M1-T23)
   ---------------------------------------------------------------------------

   Until M1-T23 nothing in [lib/] checked for overflow. OCaml's native [int] is 63
   bits and wraps silently, and the failure that produces is worse than a wrong
   answer: the propagator and the .opb row are computed from the *same* wrapped
   arithmetic, so they agree with each other, and veripb -- which only ever sees
   the .opb -- accepts the refutation of a model that is not the model the user
   wrote.

   The instance that demonstrated it (test/unit/test_matrix.ml's overflow axis,
   [overflow_compile_rejected], and the header of test_prop.ml's [overflow_cells]):

       array [1..1] of int: c = [-2305843009213693952];    % -2^61
       var 3..4: x;
       constraint int_lin_le(c, [x], 0);
       constraint int_le(x, 3);

   x = 3 satisfies it: -2^61 * 3 = -6917529027641081856 <= 0. What baguette did
   before this module existed was print =====UNSATISFIABLE===== and emit a proof
   veripb accepted, because

     - [Encoding.linear_terms_int_lin_le] folds the constant  sum_i a_i * lo_i,
       here -2^61 * 3, which wraps to +2^61, so the .opb row came out as
       `+2305843009213693952 x_ge_4 >= 2305843009213693952 ;` -- a row that
       *forces* x = 4, where the true row is vacuously true; and
     - [Linear.propagate]'s [term_min] wraps the identical product, so its slack
       agreed with the corrupted row and it reported a root conflict.

   The .opb was a different model from the .fzn, the solver propagated that same
   different model, and the proof of the corrupted model's unsatisfiability was
   perfectly valid. I-S1 could not see it: no solution was printed, and
   [Model.check_assignment] evaluates `sum a_i v_i` with the same wrapping [+] and
   [*] anyway.

   ---------------------------------------------------------------------------
   The policy: overflow RAISES. It never wraps, and it never quietly declines
   ---------------------------------------------------------------------------

   The two defensible policies are "raise" and "fall back to no pruning". This
   module raises, and the reason is specific rather than a matter of taste:

   *Declining to prune would not make the run sound.* It is sound for the
   propagator in isolation -- keeping a value you were entitled to remove never
   removes a solution -- but by the time any propagator runs, the .opb row for that
   same constraint has already been written, by [Encoding.linear_terms_int_lin_le],
   from arithmetic this module does not police (lib/proof/ is not ours to change,
   and did not need to be: see the cap below). A propagator that silently declines
   on an overflowing row leaves a corrupted artefact on disk and says nothing. The
   quiet solver would be the bug.

   So [Overflow] is a loud failure, and the compile-time cap below is what keeps it
   unreachable for any model the CLI accepts. The raise is the backstop for the two
   callers the cap does not cover: code that builds propagators directly (every
   unit test in test/unit/ does), and a future cap that is wrong.

   ---------------------------------------------------------------------------
   The cap, and the arithmetic that justifies it
   ---------------------------------------------------------------------------

   Define, for a row  sum_i a_i x_i  ~  c  over variables declared on [l_i, u_i]:

       B_i = max (|l_i|, |u_i|)
       S   = sum_i |a_i| * B_i
       M   = |c| + S                      ([row_magnitude] below)

   Every integer the solver or the encoder derives from that row is bounded by a
   small multiple of M. Taking the four paths in turn:

   1. [Linear.propagate]: each [term_min] is |a_i * l_i| or |a_i * u_i| <= S; the
      fold of them is <= S (a partial sum is bounded by the sum of the magnitudes);
      slack = c - total_min <= M; max_term = min_i + slack <= S + M <= 2M; and
      floordiv/ceildiv of max_term by a_i is <= |max_term| since |a_i| >= 1. So
      propagation stays within 2M.

   2. [Ne.propagate]: sum_of over a subset of the terms at fixed values <= S, and
      rest = c - that <= M. The quotient is <= |rest|. Within M.

   3. The .opb row for an int_lin_le (lib/proof/encoding.ml
      [linear_terms_int_lin_le] + lib/proof/opb.ml [le], [normalise]): the folded
      constant is <= S, the row's right-hand side c - const is <= M, and
      [Opb.normalise] moves one coefficient to the right-hand side per negative
      term, a total of sum_i |a_i| * (u_i - l_i) <= 2S. So the emitted right-hand
      side is <= M + 2S <= 3M.

   4. The .opb A/B pair for an int_lin_ne ([Encoding.add_int_lin_ne]) is the worst
      case. Its span L, U are each <= S; its big-M coefficients U - c + 1 and
      c + 1 - L are each <= M + 1; row A is  sum a_i x_i - (U-c+1) b <= c - 1  over
      b in 0..1, whose own magnitude is |c-1| + S + (M+1) <= 3M + 2; and that row
      then goes through path 3, giving <= 3(3M + 2) = 9M + 6.

   So 9M + 6 bounds everything. [limit] is set at [max_int / 16], i.e. a row whose
   magnitude the compiler accepts has at least a factor of 16/9 in hand over the
   largest intermediate any of the four paths computes. (The +6 is absorbed: for
   M >= 1 the slack 16M - (9M + 6) = 7M - 6 is non-negative, and M = 0 is a row
   with no variables and a zero right-hand side.)

       limit = max_int / 16 = 288230376151711743  (about 2.9 * 10^17)

   lib/flatzinc/compile.ml enforces it twice, on the two things that multiply: each
   *declared bound* must satisfy |bound| <= limit, and each *row* must satisfy
   M <= limit. Neither implies the other -- a huge coefficient on a small domain
   overflows without any bound being large, and a variable in no row at all is
   still handed to [Domain.make] and [Encoding.declare_int]. *)

exception Overflow of string

let fail fmt = Printf.ksprintf (fun s -> raise (Overflow s)) fmt

(* ------------------------------------------------------------------ the operations *)

let neg a =
  if a = min_int then fail "-(%d) overflows a 63-bit int (min_int has no negation)" a
  else -a

let abs a =
  if a = min_int then fail "abs %d overflows a 63-bit int (min_int has no negation)" a
  else Stdlib.abs a

(* Two's complement addition is exact modulo 2^63, so a sum can only be wrong when the
   true result leaves the representable range -- which is exactly "both operands have
   the same sign and the result does not". *)
let add a b =
  let s = a + b in
  if a >= 0 = (b >= 0) && s >= 0 <> (a >= 0) then
    fail "%d + %d overflows a 63-bit int" a b
  else s

let sub a b =
  let d = a - b in
  if a >= 0 <> (b >= 0) && d >= 0 <> (a >= 0) then
    fail "%d - %d overflows a 63-bit int" a b
  else d

(* |a| and |b| both below 2^30 bound the product by 2^60, well inside max_int = 2^62-1,
   which is every coefficient and bound a real FlatZinc model has. That fast path is
   four comparisons; the exact path below costs a division, so it is worth not paying
   it per term per propagation on the engine's hot loop. *)
let small = 0x3FFFFFFF (* 2^30 - 1 *)

let mul a b =
  if a >= -small && a <= small && b >= -small && b <= small then a * b
  else if a = 0 || b = 0 then 0
  else if a = -1 then neg b
  else if b = -1 then neg a
  else
    (* [a] is neither 0 nor -1 here, so the division neither divides by zero nor is
       itself the one overflowing division (min_int / -1). *)
    let p = a * b in
    if p / a <> b then fail "%d * %d overflows a 63-bit int" a b else p

let sum l = List.fold_left add 0 l

(* [Stdlib.(/)] truncates toward zero, which is the wrong rounding for a negative
   dividend or divisor: bounds propagation needs floor/ceil of the exact rational
   quotient regardless of sign. [Stdlib.mod] takes the sign of the dividend, so for a
   non-zero remainder "the exact quotient is positive" is exactly
   [(r < 0) = (b < 0)] -- and truncation rounds a positive quotient down and a negative
   one up, which is the case split below.

   The only division that overflows is min_int / -1; every other quotient is bounded by
   the dividend. The [q - 1] and [q + 1] corrections cannot overflow either: reaching
   q = max_int or q = min_int needs |b| = 1, and then the remainder is zero and no
   correction is applied. *)
let floordiv a b =
  if b = 0 then invalid_arg "Checked.floordiv: division by zero";
  if a = min_int && b = -1 then fail "%d / %d overflows a 63-bit int" a b;
  let q = a / b and r = a mod b in
  if r <> 0 && r < 0 <> (b < 0) then q - 1 else q

let ceildiv a b =
  if b = 0 then invalid_arg "Checked.ceildiv: division by zero";
  if a = min_int && b = -1 then fail "%d / %d overflows a 63-bit int" a b;
  let q = a / b and r = a mod b in
  if r <> 0 && r < 0 = (b < 0) then q + 1 else q

(* min_int mod -1 is 0 mathematically and is the one input [Stdlib.mod] is not
   guaranteed to survive, so it is answered directly rather than computed. *)
let rem a b =
  if b = 0 then invalid_arg "Checked.rem: division by zero";
  if a = min_int && b = -1 then 0 else a mod b

(* ------------------------------------------------------------------------ the cap *)

(* See the header for the derivation. Everything the four arithmetic paths compute from
   a row of magnitude M is bounded by 9M + 6, so a row the compiler accepts has a
   factor of 16/9 in hand. *)
let limit = max_int / 16

(* |c| + sum_i |a_i| * max (|l_i|, |u_i|), over terms given as (coefficient, declared
   lo, declared hi). [None] means the magnitude does not itself fit in a native int,
   which is far past [limit] and is reported as "too large" rather than as a number. *)
let row_magnitude (terms : (int * int * int) list) rhs : int option =
  try
    Some
      (List.fold_left
         (fun acc (a, lo, hi) -> add acc (mul (abs a) (max (abs lo) (abs hi))))
         (abs rhs) terms)
  with Overflow _ -> None

let row_fits terms rhs =
  match row_magnitude terms rhs with Some m -> m <= limit | None -> false

let bound_fits b = b <> min_int && Stdlib.abs b <= limit
