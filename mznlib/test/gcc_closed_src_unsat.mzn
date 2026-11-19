% Provenance model for test/models/gcc_closed_unsat.fzn (M7-T28, D-0146).
% Three variables closed over the cover {1, 3}, and neither count may exceed 1: the
% implied row sum(c) = 3 refutes it at the root against c's bounds, and gcc.ml's rule A
% would on its own (three variables confined to a capacity of two).
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: gcc_closed_unsat
include "globals.mzn";
array [1..3] of var 0..4: x;
array [1..2] of var 0..1: c;
constraint global_cardinality_closed(x, [1, 3], c);
solve satisfy;
