% M18-coverage-T14 / D-0255: a cover with a REPEATED value, variable counts (std's count
% decomposition since D-0247). Both counts are the same tally, so c = [2,2] with x = [1,1]
% is a solution (Gecode: SAT, c = [2,2]). std's implied row |x| >= sum(c) said 2 >= 4 and
% made this UNSAT (4c5df61); the row is no longer posted under a repeated value.
% MUST-EMIT: int_eq_reif
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: gccvar_dupcover_src_sat
include "globals.mzn";
array [1..2] of var 1..2: x;
array [1..2] of var 0..2: c;
constraint global_cardinality(x, [1, 1], c);
constraint c[1] >= 2;
solve satisfy;
