% Provenance model for test/models/count_unsat.fzn (M7-T23, D-0097).
% The counts close it: 1 occurs at least twice, 2 at least twice, 3 exactly once, over four variables -- five tallies for four slots.
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/count_unsat.fzn (the flattener's own output).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: count_unsat
include "globals.mzn";
array [1..4] of var 1..3: x;
var 0..4: n;
constraint count(x, 1, n);
constraint n >= 2;
constraint count(x, 2) >= 2;
constraint count_eq(x, 3, 1);
solve satisfy;
