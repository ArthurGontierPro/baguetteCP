% M18-coverage-T14 / D-0247: global_cardinality whose counts are VARIABLES reaches std's
% count decomposition, which reads holes. The first branch (w = 2) punches 2 out of x[1..3],
% which bounds the shared count c[1] = c[2] through the holes; the optimum is c = 2.
% MUST-EMIT: int_eq_reif
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: gccvar_src_opt
include "globals.mzn";
array [1..4] of var 1..4: x;
var 1..4: w;
array [1..2] of var 0..4: c;
constraint forall (i in 1..3) (x[i] != w);
constraint x[4] != 3;
constraint global_cardinality(x, [2, 3], c);
constraint c[1] = c[2];
solve :: int_search([w] ++ x, input_order, indomain_median) maximize c[1];
