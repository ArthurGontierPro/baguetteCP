% M18-coverage-T6 (docs/DECISIONS.md D-0240): arg_max over var bool, without std's integer
% copies w[j] = n * xs[j] + (u - j) and their maximum. m = exists(xs), then
%   idx = j  ->  xs[j] \/ not m      idx > j  ->  not xs[j] /\ m
% so idx is the first true position, or the first position when every xs[j] is false (std's
% answer: there every w[j] = u - j and the largest is at j = l). The `/\ m` is that second
% case: with no true position, no j can lie before idx.

predicate fzn_maximum_arg_bool(array [int] of var bool: xs, var int: idx) =
  let {
    int: l = min(index_set(xs));
    int: u = max(index_set(xs));
    var bool: m = exists(xs);
  } in
  idx >= l /\ idx <= u
    /\ forall (j in l..u) ((idx = j -> (xs[j] \/ not m)) /\ (idx > j -> (not xs[j] /\ m)));
