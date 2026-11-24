%-----------------------------------------------------------------------------%
% diffn_nonstrict: std's pairwise decomposition plus the same two cumulative
% relaxations as mznlib/fzn_diffn.mzn (M18-coverage-T2, D-0213).  The tasks of a
% projection are the rectangles with BOTH sizes' lower bounds positive, and for
% those diffn_nonstrict's escape (a zero side) is closed, so the relaxation's
% argument in fzn_diffn.mzn holds unchanged.
%-----------------------------------------------------------------------------%

include "fzn_diffn.mzn";

predicate fzn_diffn_nonstrict(
  array [int] of var int: x,
  array [int] of var int: y,
  array [int] of var int: dx,
  array [int] of var int: dy,
) =
  % std/fzn_diffn_nonstrict.mzn, verbatim
  forall (i, j in index_set(x) where i < j) (
    dx[i] = 0 \/
      dx[j] = 0 \/
      dy[i] = 0 \/
      dy[j] = 0 \/
      x[i] + dx[i] <= x[j] \/
      y[i] + dy[i] <= y[j] \/
      x[j] + dx[j] <= x[i] \/
      y[j] + dy[j] <= y[i]
  )
  /\ baguette_diffn_projection(x, dx, y, dy)
  /\ baguette_diffn_projection(y, dy, x, dx);
