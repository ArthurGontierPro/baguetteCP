% Provenance model for test/models/gcc_low_up_closed_sat.fzn (M7-T28, D-0146).
% global_cardinality_low_up_closed must reach mznlib/fzn_global_cardinality_low_up_closed.mzn:
% ONE baguette_global_cardinality call over counts declared on their own bounds, x
% restricted to the cover {1, 3, 5}, and the implied row over the counts.
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: gcc_low_up_closed_sat
include "globals.mzn";
array [1..5] of var 0..6: x;
constraint global_cardinality_low_up_closed(x, [1, 3, 5], [1, 1, 1], [2, 2, 2]);
constraint x[1] > x[2];
constraint x[2] > x[3];
constraint x[4] < x[5];
solve satisfy;
