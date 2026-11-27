% M18-coverage-T14 / D-0255: the twin of gcc_low_up_closed_dupcover_src_sat. The closed cover
% forces all three x to 1, a tally of 3 above both copies' upper bound 2 (Gecode: UNSAT), so
% the repeated cover still counts.
% MUST-EMIT: baguette_global_cardinality
% SOLVES-AS: gcc_low_up_closed_dupcover_src_unsat
include "globals.mzn";
array [1..3] of var 1..2: x;
constraint global_cardinality_closed(x, [1, 1], [2, 2], [2, 2]);
solve satisfy;
