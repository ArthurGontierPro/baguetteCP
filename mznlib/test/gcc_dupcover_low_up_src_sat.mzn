% M22-review-bugs / D-0260: global_cardinality_low_up over a cover that repeats the value 2
% five times, over an array that repeats x3 (the fuzz lane's shape, found again by
% D-0260's dense grid, case 1823). Gecode: SAT. Before D-0260 baguette answered SAT and
% veripb REJECTED the proof: gcc.ml's memo of HIGH rows is keyed on the cover value, so
% one count's pruning was justified by another count's row.
% MUST-EMIT: baguette_global_cardinality
% SOLVES-AS: gcc_dupcover_low_up_src_sat
include "globals.mzn";
var 0..3: x0; var 0..3: x1; var 3..3: x2; var 0..3: x3;
constraint global_cardinality([x3,x1,x2,x3],[2,2,2,2,2],[1,0,0,0,1],[3,1,2,1,2]);
solve satisfy;
