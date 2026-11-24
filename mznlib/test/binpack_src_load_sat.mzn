% Provenance model for test/models/binpack_load_sat.fzn (M18-coverage-T4, D-0220).
% Six items into three bins with loads, item 2 kept off bin 1 by its domain, two loads pinned.
% MUST-EMIT: baguette_bool_lin_eq
% MUST-NOT-EMIT: bool2int
% SOLVES-AS: binpack_load_sat
include "globals.mzn";
array [1..6] of int: w = [4, 3, 3, 2, 2, 1];
array [1..6] of var 1..3: x;
array [1..3] of var 0..9: load;
constraint x[2] != 1;
constraint bin_packing_load(load, x, w);
constraint load[1] = 7 /\ load[3] = 3;
solve satisfy;
