% Provenance model for test/models/diffn_sat.fzn (M18-coverage-T2, D-0213).
% A 4x3 strip holding a 2x2, a 2x1, a 1x3 and a 1x2 (area 4 + 2 + 3 + 2 = 11 of 12):
% the 1x3 is a full column, and the search order puts the 2x2 first at its left.
% MUST-EMIT: baguette_cumulative
% SOLVES-AS: diffn_sat
include "globals.mzn";
array [1..4] of var 0..3: x;
array [1..4] of var 0..2: y;
constraint forall (i in 1..4) (x[i] + [2, 2, 1, 1][i] <= 4 /\ y[i] + [2, 1, 3, 2][i] <= 3);
constraint diffn(x, y, [2, 2, 1, 1], [2, 1, 3, 2]);
solve :: int_search(x ++ y, input_order, indomain_min, complete) satisfy;
