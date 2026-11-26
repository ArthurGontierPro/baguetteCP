% Provenance model for test/models/diffn_nonstrict_sat.fzn (M18-coverage-T2, D-0213).
% diffn_nonstrict with variable sizes: three rectangles in a 3x3 box, the third of
% width w in 0..2.  Its lower bound 0 keeps it out of both projections (a zero side
% may overlap anything), the other two are projected; w = 0 is forced by area.
% MUST-EMIT: baguette_cumulative
% SOLVES-AS: diffn_nonstrict_sat
include "globals.mzn";
array [1..3] of var 0..2: x;
array [1..3] of var 0..2: y;
var 0..2: w;
constraint x[1] + 2 <= 3 /\ x[2] + 1 <= 3 /\ x[3] + w <= 3;
constraint y[1] + 3 <= 3 /\ y[2] + 3 <= 3 /\ y[3] + 1 <= 3;
constraint diffn_nonstrict(x, y, [2, 1, w], [3, 3, 1]);
solve maximize w;
