% Provenance model for test/models/table_opt.fzn (M18-coverage-T1, D-0206).
% A cost table over (item, colour) and two items that must differ in colour; minimise
% the summed cost. Exercises the proof of an optimum through the selectors.
% MUST-EMIT: baguette_table
% SOLVES-AS: table_opt
include "globals.mzn";
array [1..2] of var 1..3: c;
array [1..2] of var 0..9: cost;
constraint table([c[1], cost[1]], [| 1, 4 | 2, 2 | 3, 7 |]);
constraint table([c[2], cost[2]], [| 1, 3 | 2, 1 | 3, 2 |]);
constraint c[1] != c[2];
solve minimize cost[1] + cost[2];
