% Provenance model for test/models/argmax_bool_sat.fzn (M18-coverage-T6, D-0240).
% arg_max and arg_min over var bool. b has no true position (its sum is 0), so arg_max(b)
% is the FIRST position, 2 (std's answer: every scaled copy is equal there and the first
% wins); c's first false position is pinned to 4 by its index, so c[2] and c[3] are true.
% MUST-EMIT: array_bool_and
% MUST-NOT-EMIT: array_int_maximum
% SOLVES-AS: argmax_bool_sat
include "globals.mzn";
array [2..4] of var bool: b;
array [2..5] of var bool: c;
var 2..4: ib = arg_max(b);
var 2..5: ic = arg_min(c);
constraint sum (j in 2..4) (bool2int(b[j])) = 0;
constraint ic = 4;
constraint c[5] = c[4];
solve satisfy;
output ["b = \(b);\nc = \(c);\nib = \(ib);\nic = \(ic);\n"];
