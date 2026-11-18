% Provenance model for test/models/regular_sat.fzn (M7-T28, D-0146).
% A 4x4 nonogram, one `regular` per row and per column, each written as MiniZinc's
% regular expression over {1 = empty, 2 = filled} (which std compiles to a DFA and hands
% to fzn_regular). Every call must reach mznlib/fzn_regular.mzn: eight baguette_regular
% calls, none of std's array_int_element state chains.
% MUST-EMIT: baguette_regular
% MUST-NOT-EMIT: array_int_element
% SOLVES-AS: regular_sat
include "globals.mzn";
array [1..4, 1..4] of var 1..2: g;
constraint regular([g[1, j] | j in 1..4], "1* 2 2 1*");
constraint regular([g[2, j] | j in 1..4], "1* 2 1+ 2 1*");
constraint regular([g[3, j] | j in 1..4], "1* 2 2 2 1*");
constraint regular([g[4, j] | j in 1..4], "1* 2 1*");
constraint regular([g[i, 1] | i in 1..4], "1* 2 1+ 2 1*");
constraint regular([g[i, 2] | i in 1..4], "1* 2 2 2 1*");
constraint regular([g[i, 3] | i in 1..4], "1* 2 2 1*");
constraint regular([g[i, 4] | i in 1..4], "1* 2 1*");
solve satisfy;
