% M22-review-bugs / D-0260: the closed form with variable counts over a cover that repeats
% the value 1, the count b serving both the second 1 and the value 2: a = b counts the 1s,
% b counts the 2s, so the three x split evenly between 1 and 2. Gecode: UNSAT. The merge
% ties a to b (int_lin_eq([1, -1], [a, b], 0)).
% MUST-EMIT: baguette_global_cardinality
% SOLVES-AS: gcc_dupcover_closed_src_unsat
include "globals.mzn";
array [1..3] of var 1..2: x;
var 0..3: a;
var 0..3: b;
constraint global_cardinality_closed(x, [1, 1, 2], [a, b, b]);
solve satisfy;
