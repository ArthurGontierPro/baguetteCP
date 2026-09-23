% Provenance model for test/models/gcc_shim_sat.fzn (M7-T15).
% The two-argument global_cardinality of MiniZinc 1.x, whose cover is the index
% set of the counts array; mznlib/compat_mzn1.mzn bridges it onto the standard
% three-argument predicate, which then decomposes.
% Unique solution: x = [0, 0, 1, 2], c = [2, 1, 1] over 0..2.
include "globals.mzn";
array [1..4] of var 0..2: x;
array [0..2] of var 0..4: c;
constraint global_cardinality(x, c);
constraint c[0] = 2;
constraint c[1] = 1;
constraint x[1] <= x[2];
constraint x[2] <= x[3];
constraint x[3] <= x[4];
solve satisfy;
