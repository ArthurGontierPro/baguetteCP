% Provenance model for test/models/gcc_repeat_sat.fzn (M7-T29, D-0146).
% The equality x[1] = x[2] makes MiniZinc UNIFY the two cells, so the gcc call names one
% variable twice -- community-detection's shape (D-0121). Its tally must count it twice:
% value 1 occurs exactly once, so the repeated variable cannot be 1 and the only
% solution is x = [2, 2, 1]. A front end that counted it once would also accept
% x = [1, 1, 2]; one that refused it would print nothing.
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: gcc_repeat_sat
include "globals.mzn";
array [1..3] of var 1..2: x;
constraint x[1] = x[2];
constraint global_cardinality(x, [1, 2], [1, 2]);
solve satisfy;
