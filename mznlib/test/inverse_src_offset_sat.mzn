% Provenance model for test/models/inverse_offset_sat.fzn (M7-T28, D-0151 section 2).
% Index sets that are not 1..n: f over 0..3 takes values in 10..13, the index set of g,
% and g over 10..13 takes values in 0..3. The flattener passes 1-based arrays, so the
% first indices travel as the two integer arguments of baguette_inverse.
% MUST-EMIT: baguette_inverse
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: inverse_offset_sat
include "globals.mzn";
array [0..3] of var 10..13: f;
array [10..13] of var 0..3: g;
constraint inverse(f, g);
constraint f[0] = 12 /\ g[10] != 1 /\ f[3] > f[2];
solve satisfy;
