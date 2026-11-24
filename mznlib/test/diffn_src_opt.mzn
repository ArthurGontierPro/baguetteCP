% Provenance model for test/models/diffn_opt.fzn (M18-coverage-T2, D-0213).
% Strip packing: five rectangles in a strip of height 3, minimise the right edge.
% Area 2 + 3 + 3 + 4 + 2 = 14 gives 5 by the x-projection (ceil(14 / 3)); the
% optimum is 5.
% MUST-EMIT: baguette_cumulative
% SOLVES-AS: diffn_opt
include "globals.mzn";
array [1..5] of int: w = [1, 3, 1, 2, 2];
array [1..5] of int: h = [2, 1, 3, 2, 1];
array [1..5] of var 0..6: x;
array [1..5] of var 0..2: y;
var 0..7: e;
constraint forall (i in 1..5) (x[i] + w[i] <= e /\ y[i] + h[i] <= 3);
constraint diffn(x, y, w, h);
solve minimize e;
