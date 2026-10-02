% Provenance model for test/models/at_most_sat.fzn (M7-T23, D-0097).
% at_most(n, xs, v) is std's count(xs, v) <= n, so it reaches fzn_count_eq and routes.
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/at_most_sat.fzn (the flattener's own output).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: at_most_sat
include "globals.mzn";
array [1..3] of var 1..3: x;
constraint at_most(1, x, 1);
constraint at_most(1, x, 2);
constraint x[1] < x[3];
solve satisfy;
