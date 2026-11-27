% M18-coverage-T14 / D-0255: variable counts whose lower bounds sum past |x| (2 + 2 + 1 > 4).
% No single value's count row sees it; std's implied row |x| >= sum(counts), which the
% variable-count route keeps (D-0247, D-0255), refutes it at the root (Gecode: UNSAT).
% Dropping that row from the .opb makes veripb 3.0.2 reject the proof (D-0255 section 4).
% MUST-EMIT: int_lin_le
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: gccvar_sum_src_unsat
include "globals.mzn";
array [1..4] of var 1..3: x;
array [1..3] of var 0..4: c;
constraint global_cardinality(x, [1, 2, 3], c);
constraint c[1] >= 2 /\ c[2] >= 2 /\ c[3] >= 1;
solve satisfy;
