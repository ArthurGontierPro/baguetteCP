% Provenance model for test/models/gcc_repeat_unsat.fzn (M7-T29, D-0146).
% The same unified pair, with each of the values 1 and 2 to occur exactly once among
% three cells: the counts sum to 2 over three cells, so no assignment exists. Counted
% once, the repeated variable would let x = [1, 1, 2] through as a "solution".
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: gcc_repeat_unsat
include "globals.mzn";
array [1..3] of var 1..2: x;
constraint x[1] = x[2];
constraint global_cardinality(x, [1, 2], [1, 1]);
solve satisfy;
