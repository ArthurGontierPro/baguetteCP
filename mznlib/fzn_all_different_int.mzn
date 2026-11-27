%-----------------------------------------------------------------------------%
% all_different_int stays whole.
%
% std/fzn_all_different_int.mzn decomposes to |x|*(|x|-1)/2 disequalities.  That
% throws away lib/core/prop/alldiff.ml -- DOMAIN consistency in two stages: Hall
% intervals on the bounds with the multi-row Hall justification (M4-T1, D-0061),
% then a maximum matching that prunes values (M4-T2) -- and replaces one
% propagator by a quadratic number of int_ne propagators, each of whose prunings
% also has to be proved.
%
% The bodyless declaration below is what makes MiniZinc emit the call verbatim;
% the wrapper is what globals.mzn reaches.
%-----------------------------------------------------------------------------%

predicate all_different_int(array [int] of var int: x);

predicate fzn_all_different_int(array [int] of var int: x) = all_different_int(x);
