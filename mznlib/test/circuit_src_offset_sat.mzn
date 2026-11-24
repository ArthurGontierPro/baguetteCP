% Provenance model for test/models/circuit_offset_sat.fzn (M18-coverage-T3, D-0217).
% The index set 3..7 (the root is node 3) and one successor fixed by the model.
% MUST-EMIT: baguette_circuit
% SOLVES-AS: circuit_offset_sat
include "globals.mzn";
array [3..7] of var 3..7: s;
constraint circuit(s);
constraint s[4] = 6;
constraint s[3] > s[5];
solve satisfy;
