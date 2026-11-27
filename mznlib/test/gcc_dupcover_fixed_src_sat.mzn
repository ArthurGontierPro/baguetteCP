% M22-review-bugs / D-0260: fixed counts over a cover that repeats the value 1 with the
% same count twice, so the merged cover keeps [1, 2] and the two constant counts need no
% tie. Gecode: SAT (two of x are 1, one is 2).
% MUST-EMIT: baguette_global_cardinality
% SOLVES-AS: gcc_dupcover_fixed_src_sat
include "globals.mzn";
array [1..3] of var 0..3: x;
constraint global_cardinality(x, [1, 2, 1], [2, 1, 2]);
solve satisfy;
