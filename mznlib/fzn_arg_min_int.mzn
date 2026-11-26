% M18-coverage-T6 (docs/DECISIONS.md D-0240): arg_min over var int, the mirror of
% fzn_arg_max_int.mzn (read that header): m = min(xs), kept whole by baguette
% (array_int_minimum), and two implications per position,
%   idx = j  ->  xs[j] <= m      idx > j  ->  xs[j] > m
% in place of std's copies w[j] = n * xs[j] + j and their minimum. The FIRST position of the
% minimum wins, as in std.

predicate fzn_minimum_arg_int(array [int] of var int: xs, var int: idx) =
  let {
    int: l = min(index_set(xs));
    int: u = max(index_set(xs));
    var lb_array(xs)..ub_array(xs): m = min(xs);
  } in
  idx >= l /\ idx <= u
    /\ forall (j in l..u) ((idx = j -> xs[j] <= m) /\ (idx > j -> xs[j] > m));
