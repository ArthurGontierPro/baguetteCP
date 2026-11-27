% M18-coverage-T14 / D-0255: global_cardinality_low_up_closed over a cover with a REPEATED
% value. x = [1,1] takes the value 1 twice, within [2,2] for both copies (Gecode: SAT).
% std's par check |x| in sum(lbound)..sum(ubound) said 2 in 4..4 and made this UNSAT
% (in mznlib since D-0146); it is no longer posted under a repeated value.
% MUST-EMIT: baguette_global_cardinality
% SOLVES-AS: gcc_low_up_closed_dupcover_src_sat
include "globals.mzn";
array [1..2] of var 1..2: x;
constraint global_cardinality_closed(x, [1, 1], [2, 2], [2, 2]);
solve satisfy;
