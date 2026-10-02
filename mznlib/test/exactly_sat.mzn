% Provenance model for test/models/exactly_sat.fzn (M7-T23, D-0097).
% exactly(n, xs, v) is std's n == count(xs, v), so it reaches fzn_count_eq and routes; the par n becomes a one-value count (D-0082).
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/exactly_sat.fzn (the flattener's own output).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: exactly_sat
include "globals.mzn";
array [1..4] of var 1..3: x;
constraint exactly(2, x, 1);
constraint exactly(1, x, 3);
constraint x[1] > x[2];
solve satisfy;
