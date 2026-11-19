% Provenance model for test/models/regular_unsat.fzn (M7-T28, D-0146).
% A 3x3 nonogram whose clues disagree: the rows ask for one run of two in every line
% (six filled cells) and the columns for a single filled cell each (three). Every call
% must reach mznlib/fzn_regular.mzn; the refutation is the regular propagators' own.
% MUST-EMIT: baguette_regular
% MUST-NOT-EMIT: array_int_element
% SOLVES-AS: regular_unsat
include "globals.mzn";
array [1..3, 1..3] of var 1..2: g;
constraint forall (i in 1..3) (regular([g[i, j] | j in 1..3], "1* 2 2 1*"));
constraint forall (j in 1..3) (regular([g[i, j] | i in 1..3], "1* 2 1*"));
solve satisfy;
