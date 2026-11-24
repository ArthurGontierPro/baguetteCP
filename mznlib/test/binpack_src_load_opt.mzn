% Provenance model for test/models/binpack_load_opt.fzn (M18-coverage-T4, D-0220).
% Seven items into three bins, the heaviest load minimised (the optimum is 6 of a total 17).
% MUST-EMIT: baguette_bool_lin_eq
% MUST-NOT-EMIT: bool2int
% SOLVES-AS: binpack_load_opt
include "globals.mzn";
array [1..7] of int: w = [5, 4, 3, 2, 1, 1, 1];
array [1..7] of var 1..3: x;
array [1..3] of var 0..17: load;
var 0..17: top;
constraint bin_packing_load(load, x, w);
constraint forall (b in 1..3) (load[b] <= top);
constraint x[1] = 1;
solve minimize top;
