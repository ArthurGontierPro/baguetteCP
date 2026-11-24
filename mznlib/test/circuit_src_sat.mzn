% Provenance model for test/models/circuit_sat.fzn (M18-coverage-T3, D-0217).
% Five nodes, every successor first tried at its smallest value: each chain's closing
% arc back to its start is removed by prevent before the search can try it.
% MUST-EMIT: baguette_circuit
% SOLVES-AS: circuit_sat
include "globals.mzn";
array [1..5] of var 1..5: s;
constraint circuit(s);
constraint s[3] != 4;
solve :: int_search(s, input_order, indomain_min) satisfy;
