% Provenance model for test/models/search_string_sat.fzn (M7-T15).
% MiniZinc 1.x string-valued search annotation, mapped by mznlib/compat_mzn1.mzn
% onto the 2.x annotations of the same names. The .fzn must carry
% int_search(..., first_fail, indomain_split, complete) -- the strategies the
% model asked for, not a fallback.
% Unique solution: a = [1, 2, 3].
include "globals.mzn";
array [1..3] of var 1..4: a;
constraint all_different(a);
constraint sum(a) = 6;
constraint a[1] < a[2];
constraint a[2] < a[3];
solve :: int_search(a, "first_fail", "indomain_split", "complete") satisfy;
