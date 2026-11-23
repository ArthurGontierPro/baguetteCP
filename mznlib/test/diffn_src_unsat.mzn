% Provenance model for test/models/diffn_unsat.fzn (M18-coverage-T2, D-0213).
% Four 3x3 squares in a 5x5 box: area 36 > 25.  Every square's x-interval contains
% x = 2 whatever its position, so the x-projection's capacity row at 2 reads 12 > 5
% at the root; the pairwise rows alone need search to see it.
% MUST-EMIT: baguette_cumulative
% MUST-EMIT: int_lin_le_reif
% SOLVES-AS: diffn_unsat
include "globals.mzn";
array [1..4] of var 0..2: x;
array [1..4] of var 0..2: y;
constraint diffn(x, y, [3, 3, 3, 3], [3, 3, 3, 3]);
solve satisfy;
