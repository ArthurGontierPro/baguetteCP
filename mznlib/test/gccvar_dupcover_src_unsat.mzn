% M18-coverage-T14 / D-0255: the twin of gccvar_dupcover_src_sat. Both counts are the same
% tally of the value 1, so c[1] >= 2 and c[2] <= 1 cannot hold together (Gecode: UNSAT).
% Without the implied row this is the per-value rows' answer, so the sat twin's fix did not
% drop the counting itself.
% MUST-EMIT: int_eq_reif
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: gccvar_dupcover_src_unsat
include "globals.mzn";
array [1..2] of var 1..2: x;
array [1..2] of var 0..2: c;
constraint global_cardinality(x, [1, 1], c);
constraint c[1] >= 2 /\ c[2] <= 1;
solve satisfy;
