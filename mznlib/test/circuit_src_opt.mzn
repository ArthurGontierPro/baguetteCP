% Provenance model for test/models/circuit_opt.fzn (M18-coverage-T3, D-0217).
% A six-city tour, minimised: the proof of the optimum runs through the prevent lines.
% MUST-EMIT: baguette_circuit
% SOLVES-AS: circuit_opt
include "globals.mzn";
int: n = 6;
array [1..n, 1..n] of int: d =
  [| 0, 3, 4, 2, 7, 5 | 3, 0, 4, 6, 3, 2 | 4, 4, 0, 5, 8, 3
   | 2, 6, 5, 0, 6, 4 | 7, 3, 8, 6, 0, 2 | 5, 2, 3, 4, 2, 0 |];
array [1..n] of var 1..n: s;
constraint circuit(s);
solve minimize sum (i in 1..n) (d[i, s[i]]);
