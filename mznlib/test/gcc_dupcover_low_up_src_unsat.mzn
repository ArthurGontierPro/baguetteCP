% M22-review-bugs / D-0260: the UNSAT twin of gcc_dupcover_low_up_src_sat (D-0260's dense
% grid, case 2143). x0 four times, so the tally of 1 is 0 or 4, and the copies' bounds
% [0,2], [1,3], [0,2], [0,3] meet in 1..2. Gecode: UNSAT. Before D-0260 the answer was
% right and veripb REJECTED the proof.
% MUST-EMIT: baguette_global_cardinality
% SOLVES-AS: gcc_dupcover_low_up_src_unsat
include "globals.mzn";
var 0..3: x0;
constraint global_cardinality([x0,x0,x0,x0],[1,1,1,1],[0,1,0,0],[2,3,2,3]);
solve satisfy;
