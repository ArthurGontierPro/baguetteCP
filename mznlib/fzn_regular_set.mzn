%-----------------------------------------------------------------------------%
% regular over a SET alphabet stays whole too (M7-T28, D-0146).
%
% std's `regular(xs, Q, set of int: S, ...)` calls fzn_regular when min(S) = 1 and
% fzn_regular_set otherwise; std/fzn_regular_set.mzn decomposes like fzn_regular.mzn
% and also defines the set-alphabet overload of fzn_regular, so this file replaces both.
%
% The alphabet's HULL min(S)..max(S) is the symbol range handed to baguette_regular, and
% a value of the hull outside S gets the column 0 (fail) in every state: the propagator
% removes it at the root with the same rup as any letter no live edge carries.  The
% declarations are narrowed to the hull, not to S itself, so a gappy alphabet costs no
% declared set domain (whose holes would each be an Ne instance, M7-T11) for what the
% table already says.
%-----------------------------------------------------------------------------%

include "fzn_regular.mzn";

predicate fzn_regular_set(
  array [int] of var int: xs,
  int: Q,
  set of int: S,
  array [int, int] of int: d,
  int: q0,
  set of int: F,
) =
  if length(xs) = 0 then
    q0 in F
  else
    let {
      array [1..(length(xs) + 1) * Q] of var bool: s;
    } in forall (i in index_set(xs)) (xs[i] in min(S)..max(S))
      /\ baguette_regular(
        array1d(xs),
        Q,
        min(S),
        [if v in S then d[q, v] else 0 endif | q in 1..Q, v in min(S)..max(S)],
        q0,
        [f | f in F],
        s,
      )
  endif;

predicate fzn_regular(
  array [int] of var int: xs,
  int: Q,
  set of int: S,
  array [int, int] of int: d,
  int: q0,
  set of int: F,
) = fzn_regular_set(xs, Q, S, d, q0, F);
