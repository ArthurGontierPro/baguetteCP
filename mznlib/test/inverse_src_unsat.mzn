% Provenance model for test/models/inverse_unsat.fzn (M7-T28, D-0151 section 2).
% A permutation f of 1..5 and its inverse g, with f[1], f[2] and f[3] all at most 2: a
% pigeonhole. The channel alone does not see it -- it leaves g[1] and g[2] in 1..3 and
% g[3], g[4], g[5] in 4..5, three into two again -- so the refutation needs either the
% search or all_different's counting over f or g.
% MUST-EMIT: baguette_inverse
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: inverse_unsat
include "globals.mzn";
array [1..5] of var 1..5: f;
array [1..5] of var 1..5: g;
constraint inverse(f, g);
constraint forall (i in 1..3) (f[i] <= 2);
solve satisfy;
