% Provenance model for test/models/alldiff_except0_sat.fzn (M18-coverage-T7, D-0233).
% alldifferent_except_0 needs no mznlib file: std's fzn_alldifferent_except writes
% global_cardinality(xs, dom_array(xs) diff {0}, 0, 1) when every variable is bounded, and
% mznlib/fzn_global_cardinality_low_up.mzn routes that to baguette's gcc. This model pins it.
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_ne_reif
% SOLVES-AS: alldiff_except0_sat
include "globals.mzn";
array [1..5] of var 0..3: x;
constraint alldifferent_except_0(x);
constraint sum(x) = 6;
constraint x[1] = 0 /\ x[2] >= 2 /\ x[5] != 0;
constraint x[3] < x[4];
solve satisfy;
