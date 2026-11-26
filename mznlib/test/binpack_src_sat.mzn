% Provenance model for test/models/binpack_sat.fzn (M18-coverage-T4, D-0220).
% bin_packing with one capacity over bins 0..3, a zero-weight item, and item 1 forced out
% of bin 0: the range is std's lb_array..ub_array.
% MUST-EMIT: baguette_bool_lin_le
% MUST-NOT-EMIT: bool2int
% SOLVES-AS: binpack_sat
include "globals.mzn";
array [1..5] of var 0..3: x;
constraint bin_packing(5, x, [4, 3, 3, 0, 2]);
constraint x[1] != 0 /\ x[2] = x[3] - 1;
solve satisfy;
