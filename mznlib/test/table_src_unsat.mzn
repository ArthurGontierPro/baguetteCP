% Provenance model for test/models/table_unsat.fzn (M18-coverage-T1, D-0206).
% Two tables sharing y, each over 1..6, and x + y + z = 12 with all three distinct:
% every combination the two tables allow either repeats a value or misses the sum.
% MUST-EMIT: baguette_table
% MUST-NOT-EMIT: array_int_element
% SOLVES-AS: table_unsat
include "globals.mzn";
var 1..6: x;
var 1..6: y;
var 1..6: z;
constraint table([x, y], [| 1, 2 | 2, 4 | 3, 6 | 4, 1 | 5, 3 | 6, 5 |]);
constraint table([y, z], [| 1, 1 | 2, 3 | 3, 5 | 4, 2 | 5, 4 | 6, 6 |]);
constraint all_different([x, y, z]);
constraint x + y + z = 12;
solve satisfy;
