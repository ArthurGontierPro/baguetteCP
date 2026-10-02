% Provenance model for test/models/count_var_value_sat.fzn (M7-T23, D-0097).
% A VARIABLE value has no cover at flatten time, so it keeps std's decomposition: the int_eq_reif sum, and no gcc call. This pins the fallback branch of mznlib/fzn_count_eq.mzn.
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/count_var_value_sat.fzn (the flattener's own output).
% MUST-EMIT: int_eq_reif
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: count_var_value_sat
include "globals.mzn";
array [1..3] of var 1..3: x;
var 1..3: y;
var 0..3: n;
constraint count(x, y, n);
constraint n = 2;
constraint y >= 2;
solve satisfy;
