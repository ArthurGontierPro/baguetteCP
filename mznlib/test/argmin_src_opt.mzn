% Provenance model for test/models/argmin_opt.fzn (M18-coverage-T6, D-0240).
% std's arg_min pinned through baguette (copies n * y[j] + j and array_int_minimum over
% them), over an array indexed from 0, inside an objective: maximise the index of the
% minimum under a floor on the sum. The best answer puts the minimum last, and the tie rule
% (the FIRST position of the minimum) forbids any earlier position from equalling it.
% MUST-EMIT: array_int_minimum
% SOLVES-AS: argmin_opt
include "globals.mzn";
array [0..3] of var 1..4: y;
var 0..3: k = arg_min(y);
constraint alldifferent([y[0], y[1]]);
constraint y[3] >= 2;
constraint sum(y) >= 11;
solve maximize k;
output ["y = \(y);\nk = \(k);\n"];
