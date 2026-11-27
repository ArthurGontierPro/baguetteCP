% Provenance model for test/models/all_equal_reif_sat.fzn (M18-coverage-T7, D-0233).
% Sliding windows of three that must NOT be all equal (harmony's shape) and one reified
% all_equal in a disjunction: each reified all_equal is the chain of D-0233, one equality per
% element after the first, and an array_bool_and over them.
% MUST-EMIT: array_bool_and
% SOLVES-AS: all_equal_reif_sat
include "globals.mzn";
array [1..6] of var 1..3: x;
constraint forall (t in 1..4) (not all_equal(x[t..t + 2]));
constraint all_equal([x[1], x[3], x[5]]) \/ x[2] = x[6];
constraint x[1] != x[2];
constraint sum(x) = 13;
solve satisfy;
