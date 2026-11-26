% Provenance model for test/models/nvalue_unsat.fzn (M18-coverage-T7, D-0233).
% Four variables pairwise different (int_ne, no global) cannot take at most three values.
% MUST-EMIT: baguette_bool_lin_eq
% MUST-NOT-EMIT: bool2int
% SOLVES-AS: nvalue_unsat
include "globals.mzn";
array [1..4] of var 1..5: x;
var 0..4: n;
constraint nvalue(n, x);
constraint n <= 3;
constraint forall (i, j in 1..4 where i < j) (x[i] != x[j]);
solve satisfy;
