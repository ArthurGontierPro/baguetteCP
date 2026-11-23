% Provenance model for test/models/table_alias_sat.fzn (M18-coverage-T1, D-0206).
% x occurs twice in the table's tuple, so the instance is packed Aliased (Checking):
% only the tuples with equal first two values can hold, and y > 2 leaves one.
% MUST-EMIT: baguette_table
% SOLVES-AS: table_alias_sat
include "globals.mzn";
var 1..4: x;
var 1..4: y;
constraint table([x, x, y], [| 1, 2, 3 | 2, 2, 1 | 3, 3, 4 | 4, 1, 4 | 1, 1, 2 |]);
constraint y > 2;
solve satisfy;
