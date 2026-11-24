% Provenance model for test/models/circuit_unsat.fzn (M18-coverage-T3, D-0217).
% Six nodes; 1, 2 and 3 can only point among themselves, so any circuit closes a
% cycle of three through the root (node 1): refuted by the LE and END rows summed.
% MUST-EMIT: baguette_circuit
% SOLVES-AS: circuit_unsat
include "globals.mzn";
array [1..6] of var 1..6: s;
constraint circuit(s);
constraint forall (i in 1..3) (s[i] <= 3);
solve :: int_search(s, input_order, indomain_min) satisfy;
