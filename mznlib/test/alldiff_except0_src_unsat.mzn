% Provenance model for test/models/alldiff_except0_unsat.fzn (M18-coverage-T7, D-0233).
% Four of five variables are kept off 0 and three values are left for them: pigeonhole on
% the non-zero values, over the at-most-one rows (see alldiff_except0_src_sat.mzn).
% MUST-EMIT: baguette_bool_lin_le
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: alldiff_except0_unsat
include "globals.mzn";
array [1..5] of var 0..3: x;
constraint alldifferent_except_0(x);
constraint forall (i in 1..4) (x[i] != 0);
solve satisfy;
