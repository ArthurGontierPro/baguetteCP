% Provenance model for test/models/inverse_sat.fzn (M7-T28, D-0151 section 2).
% Two permutations of 1..5 that are each other's inverse, with a few side constraints
% so the search has to use the channel: f has no fixed point, g[2] = 4, f[1] < f[5].
% The call must reach mznlib/fzn_inverse.mzn: one baguette_inverse, none of std's
% reified equalities.
% MUST-EMIT: baguette_inverse
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: inverse_sat
include "globals.mzn";
array [1..5] of var 1..5: f;
array [1..5] of var 1..5: g;
constraint inverse(f, g);
constraint forall (i in 1..5) (f[i] != i);
constraint g[2] = 4;
constraint f[1] < f[5];
solve satisfy;
