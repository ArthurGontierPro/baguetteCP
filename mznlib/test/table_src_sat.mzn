% Provenance model for test/models/table_sat.fzn (M18-coverage-T1, D-0206).
% Three positions over 1..5, eight tuples, and a sum and a disequality that leave two
% tuples: search kills tuples by bounds and by the hole x[2] != 3 punches.
% The call must reach mznlib/fzn_table_int.mzn: one baguette_table, none of std's
% elements.
% MUST-EMIT: baguette_table
% MUST-NOT-EMIT: array_int_element
% SOLVES-AS: table_sat
include "globals.mzn";
array [1..3] of var 1..5: x;
constraint table(x, [| 1, 2, 3 | 1, 3, 5 | 2, 3, 1 | 2, 4, 4 | 3, 1, 2 | 3, 3, 3
                     | 4, 2, 5 | 5, 5, 1 |]);
constraint x[2] != 3;
constraint x[1] + x[2] + x[3] >= 10;
constraint x[1] < x[3];
solve satisfy;
