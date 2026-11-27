% Provenance model for test/models/argmax_unsat.fzn (M18-coverage-T6, D-0240).
% std's arg_max pinned through baguette (read argmax_src_sat.mzn). The index of the maximum
% is asked to be 2 or more while x[1] = x[3] and x[2] < x[3]: x[1] then reaches the maximum
% and comes first, so no assignment satisfies the model. The refutation needs the tie-break
% that the (u - j) term of the copies carries.
% MUST-EMIT: array_int_maximum
include "globals.mzn";
array [1..3] of var 0..4: x;
var 1..3: i = arg_max(x);
constraint i >= 2;
constraint x[2] < x[3];
constraint x[1] = x[3];
solve satisfy;
output ["x = \(x);\n"];
