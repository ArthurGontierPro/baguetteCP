% M22-review-bugs / D-0260: the closed form with variable counts over a cover that repeats
% the value 1, whose second count is the CONSTANT 2: the merge ties the variable a to 2
% (int_lin_eq([1], [a], 2)). Gecode: SAT, with a = 2 and b = 1.
% MUST-EMIT: baguette_global_cardinality
% SOLVES-AS: gcc_dupcover_closed_src_sat
include "globals.mzn";
array [1..3] of var 1..2: x;
var 0..3: a;
var 0..3: b;
constraint global_cardinality_closed(x, [1, 2, 1], [a, b, 2]);
solve satisfy;
