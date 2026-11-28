% M22-review-bugs / D-0260: fixed counts over a cover that repeats the value 1 with two
% DIFFERENT counts, 1 and 2: one tally cannot be both. Gecode: UNSAT. The merge ties the
% two constants with the false row int_lin_eq([], [], 1), so the model is UNSAT at the
% root.
% MUST-EMIT: baguette_global_cardinality
% SOLVES-AS: gcc_dupcover_fixed_src_unsat
include "globals.mzn";
array [1..2] of var 0..3: x;
constraint global_cardinality(x, [1, 1], [1, 2]);
solve satisfy;
