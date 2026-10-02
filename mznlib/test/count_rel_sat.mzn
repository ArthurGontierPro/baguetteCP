% Provenance model for test/models/count_rel_sat.fzn (M7-T23, D-0097).
% The relational forms count_leq/geq/lt/gt/neq reach fzn_count_eq through std's count function (z = count(xs, v), then z OP n), so they route too. std's direction: count_leq(xs, v, n) is n <= count.
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/count_rel_sat.fzn (the flattener's own output).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: count_rel_sat
include "globals.mzn";
array [1..5] of var 1..3: x;
var 0..5: m;
constraint count_leq(x, 1, 2);
constraint count_geq(x, 2, 1);
constraint count_lt(x, 3, 0);
constraint count_gt(x, 3, 3);
constraint count_neq(x, 1, m);
constraint m >= 4;
solve satisfy;
