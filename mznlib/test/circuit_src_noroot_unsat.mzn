% Provenance model for test/models/circuit_noroot_unsat.fzn (M18-coverage-T3, D-0217).
% Six nodes; 4, 5 and 6 can only point among themselves, a cycle of three that avoids
% the root: refuted by the GE rows summed.
% MUST-EMIT: baguette_circuit
% SOLVES-AS: circuit_noroot_unsat
include "globals.mzn";
array [1..6] of var 1..6: s;
constraint circuit(s);
constraint forall (i in 4..6) (s[i] >= 4);
solve :: int_search(s, input_order, indomain_max) satisfy;
