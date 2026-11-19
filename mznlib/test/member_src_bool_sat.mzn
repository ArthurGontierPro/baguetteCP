% Provenance model for test/models/member_bool_sat.fzn (M7-T28, D-0159).
% member over var bool, routed through mznlib/fzn_member_bool.mzn: q is one of p, q
% excludes p[2], and p[1] and p[3] differ. Largest-first, p = [1, 1, 0] forces q = 0
% (q -> not p[2]), which only p[3] holds; the search then has to look further.
% MUST-EMIT: baguette_member_bool
% MUST-NOT-EMIT: bool_eq_reif
% SOLVES-AS: member_bool_sat
include "globals.mzn";
array [1..3] of var bool: p;
var bool: q;
constraint member(p, q);
constraint q -> not p[2];
constraint p[1] != p[3];
solve :: bool_search(p ++ [q], input_order, indomain_max) satisfy;
