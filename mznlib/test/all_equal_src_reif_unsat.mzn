% Provenance model for test/models/all_equal_reif_unsat.fzn (M18-coverage-T7, D-0233).
% Two windows of three that must not be all equal, and an implication whose premise
% x[1] = x[2] holds: it forces all four equal, which the windows forbid.
% MUST-EMIT: array_bool_and
% SOLVES-AS: all_equal_reif_unsat
include "globals.mzn";
array [1..4] of var 1..2: x;
constraint forall (t in 1..2) (not all_equal(x[t..t + 2]));
constraint all_equal([x[1], x[2]]) \/ all_equal([x[3], x[4]]) -> all_equal(x);
constraint x[1] = x[2];
solve satisfy;
