% Provenance model for test/models/exactly_unsat.fzn (M7-T23, D-0097).
% The counts close it: exactly three 1s and exactly two 2s over four variables.
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/exactly_unsat.fzn (the flattener's own output).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: exactly_unsat
include "globals.mzn";
array [1..4] of var 1..3: x;
constraint exactly(3, x, 1);
constraint exactly(2, x, 2);
solve satisfy;
