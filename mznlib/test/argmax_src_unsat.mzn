% Provenance model for test/models/argmax_unsat.fzn (M18-coverage-T6, D-0240).
% The index of the maximum is asked to be 2 or more while x[1] = x[3]: whatever x[3]'s
% value, either x[2] is larger (and then x[1] is not the maximum, but neither may x[2] be:
% x[2] is kept below x[3]) or x[1] reaches the maximum and comes first. No assignment
% satisfies the model; the refutation needs the tie-break row `i > 1 -> x[1] < m`.
% MUST-EMIT: array_int_maximum
% MUST-NOT-EMIT: int_lin_eq
include "globals.mzn";
array [1..3] of var 0..4: x;
var 1..3: i = arg_max(x);
constraint i >= 2;
constraint x[2] < x[3];
constraint x[1] = x[3];
solve satisfy;
output ["x = \(x);\n"];
