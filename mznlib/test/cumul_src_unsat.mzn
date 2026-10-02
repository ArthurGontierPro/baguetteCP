% Provenance model for test/models/cumulative_unsat.fzn (M4-T10, D-0096): the capacity
% refutes it, through the routed call.
% MUST-EMIT: baguette_cumulative
% MUST-NOT-EMIT: int_le_reif
% SOLVES-AS: cumulative_unsat
include "globals.mzn";
var 0..3: sa;
var 0..4: sb;
var 0..4: sc;
var 0..4: sd;
constraint cumulative([sa, sb, sc, sd], [3, 2, 2, 2], [2, 1, 1, 1], 2);
solve :: int_search([sb, sc, sd, sa], input_order, indomain_min, complete) satisfy;
