%-----------------------------------------------------------------------------%
% disjunctive_strict, routed to lib/core/prop/cumulative.ml as cap = 1, r_i = 1
% (D-0096) ONLY when every duration is fixed and at least 1: a zero-duration task
% is still constrained under the strict form (it may not sit strictly inside
% another task), and time-table drops it.  Same horizon test as
% fzn_disjunctive.mzn; anything else gets std's pairwise decomposition, verbatim.
%-----------------------------------------------------------------------------%

include "fzn_cumulative.mzn";

predicate fzn_disjunctive_strict(
  array [int] of var int: start,
  array [int] of var int: duration,
) =
  % Nested, not one conjunction: fix() of an unfixed duration is an error, and the
  % second test may only be evaluated once the first holds.
  if forall (i in index_set(duration)) (is_fixed(duration[i])) then
    if forall (i in index_set(duration)) (fix(duration[i]) >= 1)
       /\ (card(index_set(start)) = 0
           \/ max([ub(start[i]) + fix(duration[i]) | i in index_set(start)])
              - min([lb(start[i]) | i in index_set(start)]) <= 5000)
    then
      baguette_cumulative(
        start,
        [fix(duration[i]) | i in index_set(start)],
        [1 | i in index_set(start)],
        1,
      )
    else
      fzn_disjunctive_strict_std(start, duration)
    endif
  else
    fzn_disjunctive_strict_std(start, duration)
  endif;

% std's decomposition, verbatim (MiniZinc 2.10.1, std/fzn_disjunctive_strict.mzn).
predicate fzn_disjunctive_strict_std(
  array [int] of var int: start,
  array [int] of var int: duration,
) =
    forall (i in index_set(duration)) (duration[i] >= 0) /\
    forall (i, j in index_set(duration) where i < j) (
      start[i] + duration[i] <= start[j] \/ start[j] + duration[j] <= start[i]
    );
