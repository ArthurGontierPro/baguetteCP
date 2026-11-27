% M18-coverage-T14 / D-0255: the optimum is decided by the implied row between the counts.
% With c1 >= 2 and c2 >= 1 over four x, c3 is at most 4 - 2 - 1 = 1 (Gecode: optimum 1).
% Dropping the row from the .opb makes veripb 3.0.2 reject the optimality proof.
% MUST-EMIT: int_lin_le
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: gccvar_sum_src_opt
include "globals.mzn";
array [1..4] of var 1..3: x;
array [1..3] of var 0..4: c;
constraint global_cardinality(x, [1, 2, 3], c);
constraint c[1] >= 2 /\ c[2] >= 1;
solve maximize c[3];
