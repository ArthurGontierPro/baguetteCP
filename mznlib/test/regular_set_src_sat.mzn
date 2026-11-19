% Provenance model for test/models/regular_set_sat.fzn (M7-T28, D-0146).
% The SET-alphabet form: S = 3..5 does not start at 1, so std's regular calls
% fzn_regular_set, which mznlib/fzn_regular_set.mzn keeps whole. The table sends the
% symbol 4 to the fail state from every state, so 4 is a run of the hull that no edge
% carries and the propagator removes it at the root; the declarations are narrowed
% from 1..7 to the hull 3..5 by the library. The automaton alternates 3 and 5 from 3,
% so the word is forced: [3, 5, 3, 5, 3].
% MUST-EMIT: baguette_regular
% MUST-NOT-EMIT: array_int_element
% SOLVES-AS: regular_set_sat
include "globals.mzn";
array [1..5] of var 1..7: x;
constraint regular(x, 2, 3..5, array2d(1..2, 3..5, [2, 0, 0, 0, 0, 1]), 1, {1, 2});
solve satisfy;
