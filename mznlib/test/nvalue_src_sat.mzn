% Provenance model for test/models/nvalue_sat.fzn (M18-coverage-T7, D-0233).
% Six variables over 1..5 with exactly two distinct values, x[3] pinned to 4, x[1] kept in
% {2, 4} and apart from x[2], and a sum that leaves several answers (4 and 2, or 4 and 1).
% MUST-EMIT: baguette_bool_lin_eq
% MUST-NOT-EMIT: bool2int
% SOLVES-AS: nvalue_sat
include "globals.mzn";
array [1..6] of var 1..5: x;
var 0..6: n;
constraint nvalue(n, x);
constraint n = 2;
constraint x[1] != 3 /\ x[1] >= 2 /\ x[1] <= 4;
constraint x[2] != x[1];
constraint x[3] = 4;
constraint sum(x) = 18;
solve satisfy;
