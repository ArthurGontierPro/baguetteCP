% Provenance model for test/models/argmax_sat.fzn (M18-coverage-T6, D-0240).
% std's arg_max pinned through baguette: w[j] = n * x[j] + (u - j), one int_lin_eq per
% position, array_int_maximum over the w, and (i != j) = (max(w) > w[j]) as one reified row
% aliased with i's indicator. D-0240 measured three routes without the copies and kept this
% one. A TIE is forced: x[2] = x[4] and both reach the maximum, so the index is 2, the first
% of them; x[1] is kept below.
% MUST-EMIT: array_int_maximum
% MUST-EMIT: int_lin_le_reif
% SOLVES-AS: argmax_sat
include "globals.mzn";
array [1..4] of var 0..5: x;
var 1..4: i = arg_max(x);
constraint x[2] = x[4];
constraint x[1] < x[2];
constraint x[3] <= 3;
constraint i != 4;
constraint x[1] + x[2] + x[3] + x[4] >= 13;
solve :: int_search(x, input_order, indomain_min, complete) satisfy;
output ["x = \(x);\ni = \(i);\n"];
