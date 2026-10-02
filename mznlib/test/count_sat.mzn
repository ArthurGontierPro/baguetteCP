% Provenance model for test/models/count_sat.fzn (M7-T23, D-0097).
% count(xs, v, n) and the count(xs, v) function with a CONSTANT v route through mznlib/fzn_count_eq.mzn to ONE baguette_global_cardinality call each, not std's int_eq_reif sum.
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/count_sat.fzn (the flattener's own output).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: count_sat
include "globals.mzn";
array [1..4] of var 1..3: x;
var 0..4: n;
constraint count(x, 2, n);
constraint n >= 2;
constraint count(x, 3) = 1;
constraint x[1] >= x[4];
solve satisfy;
