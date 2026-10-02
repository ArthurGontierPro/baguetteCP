%-----------------------------------------------------------------------------%
% cumulative stays whole when its durations, resources and capacity are fixed.
%
% std/fzn_cumulative.mzn decomposes to, per time point t, `b >= sum_i ((s_i <= t
% /\ t < s_i + d_i) * r_i)` -- one reified conjunction per task and time
% (cumulative_time), or per task pair when the horizon is over 5000
% (cumulative_task).  On 2008_rcpsp that is 14 328 Booleans and 20 070
% constraints.  lib/core/prop/cumulative.ml posts the same capacity row per time
% point over the starts' ORDER literals with no auxiliary at all, and
% time-table-filters over it with a cutting-planes derivation per push.  D-0096
% is the design record, its census and its worked proof.
%
% WHAT IS ROUTED, and the rest goes to std's own decomposition, kept verbatim
% below because shadowing fzn_cumulative replaces std's whole file:
%   - every duration, every resource and the capacity FIXED, and none negative
%     (cumulative.ml's rows are over constants; a variable resource -- the 0/1
%     machine choice of fjsp, gfd-schedule, unison -- is not linear over the
%     order encoding, D-0096 section 5);
%   - std's own horizon test passed (late - early <= 5000): the rows are one per
%     time point, and a horizon past that is std's task-based form today and
%     stays so.
%-----------------------------------------------------------------------------%

predicate baguette_cumulative(
  array [int] of var int: s,
  array [int] of int: d,
  array [int] of int: r,
  int: b,
);

predicate fzn_cumulative(
  array [int] of var int: start,
  array [int] of var int: duration,
  array [int] of var int: resource,
  var int: capacity,
) =
  let {
    set of int: Tasks = {i | i in index_set(start) where ub(resource[i]) > 0 /\ ub(duration[i]) > 0};
  } in if 0 == card(Tasks) then
    0 == card(index_set(start)) \/ capacity >= 0
  else
    let {
      int: early = min([lb(start[i]) | i in Tasks]);
      int: late = max([ub(start[i]) + ub(duration[i]) | i in Tasks]);
      bool: fixed_shape =
        is_fixed(capacity)
        /\ forall (i in index_set(start)) (is_fixed(duration[i]))
        /\ forall (i in index_set(start)) (is_fixed(resource[i]));
    } in (
      % Nested, not one conjunction: fix() of an unfixed value is an error.
      if fixed_shape /\ late - early <= 5000 then
        if fix(capacity) >= 0
           /\ forall (i in index_set(start)) (fix(duration[i]) >= 0 /\ fix(resource[i]) >= 0)
        then
          baguette_cumulative(
            start,
            [fix(duration[i]) | i in index_set(start)],
            [fix(resource[i]) | i in index_set(start)],
            fix(capacity),
          )
        else
          fzn_cumulative_time(start, duration, resource, capacity)
        endif
      elseif late - early > 5000 then
        fzn_cumulative_task(start, duration, resource, capacity)
      else
        fzn_cumulative_time(start, duration, resource, capacity)
      endif
    )
  endif;

% std's two decompositions, verbatim (MiniZinc 2.10.1, std/fzn_cumulative.mzn).
predicate fzn_cumulative_time(
  array [int] of var int: s,
  array [int] of var int: d,
  array [int] of var int: r,
  var int: b,
) =
  let {
    set of int: Tasks = {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0};
    int: early = min([lb(s[i]) | i in Tasks]);
    int: late = max([ub(s[i]) + ub(d[i]) | i in Tasks]);
  } in (forall (t in early..late) (b >= sum (i in Tasks) ((s[i] <= t /\ t < s[i] + d[i]) * r[i])));

predicate fzn_cumulative_task(
  array [int] of var int: s,
  array [int] of var int: d,
  array [int] of var int: r,
  var int: b,
) =
  let {
    set of int: Tasks = {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0};
  } in (
    forall (j in Tasks) (
      % Note: i can equal j. If j has a duration of 0, then it is not considered.
      b >= sum (i in Tasks) ((s[i] <= s[j] /\ s[j] < s[i] + d[i]) * r[i])
    )
  );
