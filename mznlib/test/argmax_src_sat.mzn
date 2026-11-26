% Provenance model for test/models/argmax_sat.fzn (M18-coverage-T6, D-0240).
% arg_max over four variables where a TIE is forced: x[2] = x[4] and both reach the
% maximum, so the index is 2, the first of them; x[1] is kept below. The maximum is
% array_int_maximum over x itself, and no scaled copy of x is introduced (std's
% decomposition defines one int_lin_eq copy n * x[j] + (u - j) per position).
% MUST-EMIT: array_int_maximum
% MUST-NOT-EMIT: int_lin_eq
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
