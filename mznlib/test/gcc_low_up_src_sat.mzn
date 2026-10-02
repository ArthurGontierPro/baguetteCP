% Provenance model for test/models/gcc_low_up_sat.fzn (M6-T13, D-0087).
% global_cardinality_low_up must reach mznlib/fzn_global_cardinality_low_up.mzn and
% flatten to ONE baguette_global_cardinality call with the counts declared on their
% own bounds (1..2, 0..1, and the constant 2), not to std's count-sum decomposition.
% check_mznlib.sh reads the three directives below.  The committed .fzn is named
% differently from this file on purpose: it was WRITTEN BY HAND as the flattener would
% emit it (no MiniZinc on the machine that wrote it), so a byte comparison against it
% would test the X_INTRODUCED_ numbering, not the library.
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: gcc_low_up_sat
include "globals.mzn";
array [1..4] of var 1..3: x;
constraint global_cardinality_low_up(x, [1, 2, 3], [1, 0, 2], [2, 1, 2]);
constraint x[1] <= x[2];
constraint x[2] <= x[3];
constraint x[3] <= x[4];
constraint sum(x) >= 9;
solve satisfy;
