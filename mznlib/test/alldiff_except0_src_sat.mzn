% Provenance model for test/models/alldiff_except0_sat.fzn (M18-coverage-T7, D-0233).
% alldifferent_except_0 reaches mznlib/fzn_alldifferent_except.mzn: one
% baguette_bool_lin_le per non-zero value over the indicators x[i] = v, at most one true.
% MUST-EMIT: baguette_bool_lin_le
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: alldiff_except0_sat
include "globals.mzn";
array [1..5] of var 0..3: x;
constraint alldifferent_except_0(x);
constraint sum(x) = 6;
constraint x[1] = 0 /\ x[2] >= 2 /\ x[5] != 0;
constraint x[3] < x[4];
solve satisfy;
