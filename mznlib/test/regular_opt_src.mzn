% Provenance model for test/models/regular_opt.fzn (M7-T28, D-0146).
% A six-day roster, 1 = off, 2 = day, 3 = night, under the rule "a night is followed by
% a day off" (state 2 is "the last shift was a night"; from it only 1 is allowed).
% Maximising the sum of the codes needs search and a bound proof below the root: the
% best word is 2 2 2 2 2 3, worth 13 (ending on a night costs nothing).
% MUST-EMIT: baguette_regular
% MUST-NOT-EMIT: array_int_element
% SOLVES-AS: regular_opt
include "globals.mzn";
array [1..6] of var 1..3: x;
var 6..18: total = sum(x);
constraint regular(x, 2, 3, [|1, 1, 2 | 1, 0, 0|], 1, {1, 2});
solve maximize total;
