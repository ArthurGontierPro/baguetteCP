% Provenance model for test/models/sort_unsat.fzn (M18-coverage-T6, D-0240).
% std's sort pinned through baguette (read sort_src_sat.mzn). ys[3] >= 3 and ys increasing
% put two values of xs at 3 or more; of the two others at least one is among xs[1..3], so at
% least 1, and sum(xs) >= 7 > 6. No solution.
% MUST-EMIT: all_different_int
include "globals.mzn";
array [1..4] of var 0..4: xs;
array [1..4] of var 0..4: ys;
constraint sort(xs, ys);
constraint ys[3] >= 3;
constraint xs[1] >= 1 /\ xs[2] >= 1 /\ xs[3] >= 1;
constraint sum(xs) <= 6;
solve satisfy;
output ["xs = \(xs);\n"];
