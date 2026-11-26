% M18-coverage-T6 (docs/DECISIONS.md D-0240): arg_min over var bool, the mirror of
% fzn_arg_max_bool.mzn. m = forall(xs), then
%   idx = j  ->  not xs[j] \/ m      idx > j  ->  xs[j] /\ not m
% so idx is the first false position, or the first position when every xs[j] is true.

predicate fzn_minimum_arg_bool(array [int] of var bool: xs, var int: idx) =
  let {
    int: l = min(index_set(xs));
    int: u = max(index_set(xs));
    var bool: m = forall(xs);
  } in
  idx >= l /\ idx <= u
    /\ forall (j in l..u) ((idx = j -> (not xs[j] \/ m)) /\ (idx > j -> (xs[j] /\ not m)));
