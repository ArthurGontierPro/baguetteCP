%-----------------------------------------------------------------------------%
% disjunctive is cumulative with unit resources and capacity 1 (D-0096), and with
% FIXED, non-negative durations and a horizon std's own cumulative would index
% by time (late - early <= 5000) it is routed to lib/core/prop/cumulative.ml.
% A zero-duration task is unconstrained here exactly as it is in cumulative
% (both drop it).  Anything else gets std's pairwise decomposition, verbatim.
%
% A STRENGTH NOTE, measured in the M4-T10 handoff rather than assumed: for unit
% capacity the pairwise disjunctions propagate precedences that time-table does
% not see before compulsory parts exist.  The trade is n^2 reified disjunctions
% for one row per time point.
%-----------------------------------------------------------------------------%

include "fzn_cumulative.mzn";

predicate fzn_disjunctive(
  array [int] of var int: start,
  array [int] of var int: duration,
) =
  % Nested, not one conjunction: fix() of an unfixed duration is an error, and the
  % second test may only be evaluated once the first holds.
  if forall (i in index_set(duration)) (is_fixed(duration[i])) then
    if forall (i in index_set(duration)) (fix(duration[i]) >= 0)
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
      fzn_disjunctive_std(start, duration)
    endif
  else
    fzn_disjunctive_std(start, duration)
  endif;

% std's decomposition, verbatim (MiniZinc 2.10.1, std/fzn_disjunctive.mzn).
predicate fzn_disjunctive_std(
  array [int] of var int: start,
  array [int] of var int: duration,
) =
    forall (i in index_set(duration)) (duration[i] >= 0) /\
      forall (i, j in index_set(duration) where i < j) (
        duration[i] = 0 \/ duration[j] = 0 \/ start[i] + duration[i] <= start[j] \/ start[j] + duration[j] <= start[i]
      );
