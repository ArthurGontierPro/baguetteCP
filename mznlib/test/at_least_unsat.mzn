% Provenance model for test/models/at_least_unsat.fzn (M7-T23, D-0097).
% The counts close it: at least two 1s, two 2s and one 3 over four variables.
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/at_least_unsat.fzn (the flattener's own output).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: at_least_unsat
include "globals.mzn";
array [1..4] of var 1..3: x;
constraint at_least(2, x, 1);
constraint at_least(2, x, 2);
constraint at_least(1, x, 3);
solve satisfy;
