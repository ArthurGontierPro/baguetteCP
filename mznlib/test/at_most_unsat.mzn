% Provenance model for test/models/at_most_unsat.fzn (M7-T23, D-0097).
% The counts close it: three variables over 1..2 with at most one 1 and at most one 2.
% check_mznlib.sh flattens this against mznlib/, checks the directives below, and
% compares the body with the committed test/models/at_most_unsat.fzn (the flattener's own output).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: at_most_unsat
include "globals.mzn";
array [1..3] of var 1..2: x;
constraint at_most(1, x, 1);
constraint at_most(1, x, 2);
solve satisfy;
