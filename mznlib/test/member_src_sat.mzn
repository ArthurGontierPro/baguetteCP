% Provenance model for test/models/member_sat.fzn (M7-T28, D-0159).
% Four distinct values of 1..6 avoiding 3, y one of the last two (it differs from the
% first two), and x[1] + x[2] + y = 12. The call must reach mznlib/fzn_member_int.mzn:
% one baguette_member, none of std's reified equalities.
% MUST-EMIT: baguette_member
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: member_sat
include "globals.mzn";
array [1..4] of var 1..6: x;
var 1..6: y;
constraint member(x, y);
constraint all_different(x);
constraint forall (i in 1..4) (x[i] != 3);
constraint y != x[1] /\ y != x[2];
constraint x[1] + x[2] + y = 12;
solve satisfy;
