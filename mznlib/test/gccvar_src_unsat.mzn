% M18-coverage-T14 / D-0247: global_cardinality whose counts are VARIABLES reaches std's
% count decomposition, which reads holes. No x may equal w, so the value w has no taker,
% yet every count is at least 1: UNSAT for every w, by holes punched under a decision.
% MUST-EMIT: int_eq_reif
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: gccvar_src_unsat
include "globals.mzn";
array [1..3] of var 1..3: x;
var 1..3: w;
array [1..3] of var 1..3: n;
constraint forall (i in 1..3) (x[i] != w);
constraint global_cardinality(x, [1, 2, 3], n);
solve satisfy;
