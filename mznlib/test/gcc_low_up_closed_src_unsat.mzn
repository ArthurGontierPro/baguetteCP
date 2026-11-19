% Provenance model for test/models/gcc_low_up_closed_unsat.fzn (M7-T28, D-0146).
% Four variables closed over {2, 4, 6} with at most one of each: the par check std
% makes (|x| in sum(lbound)..sum(ubound), 4 in 0..3) would refuse this at flattening,
% so the model has three variables, which must then take 2, 4 and 6 once each, and
% their sum is forbidden to be 12. (Forcing two of them EQUAL would put the same
% variable twice in the gcc call once MiniZinc unifies them, which is M7-T29's case
% and has its own models.)
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: gcc_low_up_closed_unsat
include "globals.mzn";
array [1..3] of var 1..7: x;
constraint global_cardinality_low_up_closed(x, [2, 4, 6], [0, 0, 0], [1, 1, 1]);
constraint sum(x) != 12;
solve satisfy;
