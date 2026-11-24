% Provenance model for test/models/binpack_opt.fzn (M18-coverage-T4, D-0220).
% The fewest bins: six items of capacity-7 bins, the highest bin used minimised (3).
% MUST-EMIT: baguette_bool_lin_le
% MUST-NOT-EMIT: bool2int
% SOLVES-AS: binpack_opt
include "globals.mzn";
array [1..6] of var 1..4: x;
constraint bin_packing(7, x, [5, 4, 3, 3, 2, 2]);
solve minimize max(x);
