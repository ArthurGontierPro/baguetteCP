%-----------------------------------------------------------------------------%
% diffn: std's pairwise non-overlap, plus its two CUMULATIVE RELAXATIONS routed to
% lib/core/prop/cumulative.ml (M18-coverage-T2, docs/DECISIONS.md D-0213).
%
% std/fzn_diffn.mzn (MiniZinc 2.10.1) is the pairwise disjunction, kept verbatim
% below: per pair i < j, four int_lin_le_reif and one bool_clause.  It propagates
% each pair on its own, so a column of rectangles whose heights add up past the
% strip's height is never seen as full.  The relaxation sees it:
%
%   at every integer x-coordinate t, the rectangles whose x-interval contains t
%   pairwise overlap in x, so diffn makes them pairwise disjoint in y; disjoint
%   y-intervals inside [min lb(y), max (ub(y) + ub(dy))) have lengths adding up
%   to at most that window.  So cumulative(x, lb(dx), lb(dy), Hy) holds, Hy the
%   window's length, and symmetrically cumulative(y, lb(dy), lb(dx), Wx).
%
% Only the rectangles with lb(dx) > 0 and lb(dy) > 0 are tasks: one of width 0
% covers no t, and diffn_nonstrict lets a rectangle with a zero side overlap
% anything, so with both lower bounds positive the argument holds for both
% predicates.  Using the LOWER bounds of variable sizes keeps the tasks' sizes
% constant, as cumulative.ml requires, and only weakens the rows.
%
% WHAT THIS ADDS TO THE TRUSTED BASE (D-0213 section 3): the two cumulatives are
% CONSEQUENCES of diffn that the FlatZinc states as constraints, so the .opb
% carries their capacity rows as model rows and the checker does not re-derive
% them.  That is the trust every mznlib redefinition already carries (the
% FlatZinc is what the proof is about); the argument above is the theorem it
% rests on, and test/unit/test_compile.ml checks it by brute force
% (test_diffn_relaxation_theorem).
%
% A projection is posted only when it can prune (its tasks' resources add up
% past its capacity) and under cumulative's own horizon test (late - early <=
% 5000), the capacity rows being one per time point.  Otherwise it is omitted,
% which gives back std's decomposition alone.  Its starts are COPIES of the
% coordinates (baguette_diffn_order_copy below), so that cumulative's hold on the
% order encoding does not reach the pairwise rows.  Delete the two relaxation
% calls and this file is std's.
%-----------------------------------------------------------------------------%

include "fzn_cumulative.mzn";

% The start a projection's cumulative reads: a fresh variable over s's bounds, tied to
% s by TWO int_lin_le rows, which MiniZinc does not merge into an alias (it would
% merge `c = s` or one int_lin_eq).  cumulative.ml's capacity rows hold their
% starts on the ORDER encoding, so a coordinate the pairwise rows would keep on bits
% (the default, D-0201) keeps it, and only the copy pays the ladder.  A fixed s is
% passed as it is.
function var int: baguette_diffn_order_copy(var int: s) =
  if is_fixed(s) then
    s
  else
    let {
      var lb(s)..ub(s): c;
      constraint int_lin_le([1, -1], [c, s], 0);
      constraint int_lin_le([-1, 1], [c, s], 0);
    } in c
  endif;

% One projection: the coordinates s along it and the sizes ds along it, the
% coordinates a across it and the sizes da across it.  The tasks are the
% rectangles with both lower bounds positive; the capacity is the window the
% across intervals can occupy.
predicate baguette_diffn_projection(
  array [int] of var int: s,
  array [int] of var int: ds,
  array [int] of var int: a,
  array [int] of var int: da,
) =
  let {
    set of int: T =
      {i | i in index_set(s) where has_bounds(ds[i]) /\ has_bounds(da[i])
                                   /\ lb(ds[i]) > 0 /\ lb(da[i]) > 0};
  } in if card(T) < 2
     \/ not forall (i in T) (has_bounds(s[i]) /\ has_bounds(a[i]))
  then
    true
  else
    let {
      int: cap = max([ub(a[i]) + ub(da[i]) | i in T]) - min([lb(a[i]) | i in T]);
      int: early = min([lb(s[i]) | i in T]);
      int: late = max([ub(s[i]) + lb(ds[i]) | i in T]);
    } in if sum([lb(da[i]) | i in T]) <= cap \/ late - early > 5000 then
      true
    else
      baguette_cumulative(
        [baguette_diffn_order_copy(s[i]) | i in T],
        [lb(ds[i]) | i in T],
        [lb(da[i]) | i in T],
        cap,
      )
    endif
  endif;

predicate fzn_diffn(
  array [int] of var int: x,
  array [int] of var int: y,
  array [int] of var int: dx,
  array [int] of var int: dy,
) =
  % std/fzn_diffn.mzn, verbatim
  forall (i, j in index_set(x) where i < j) (
    x[i] + dx[i] <= x[j] \/ y[i] + dy[i] <= y[j] \/ x[j] + dx[j] <= x[i] \/ y[j] + dy[j] <= y[i]
  )
  /\ baguette_diffn_projection(x, dx, y, dy)
  /\ baguette_diffn_projection(y, dy, x, dx);
