% Provenance model for test/models/sort_sat.fzn (M18-coverage-T6, D-0240).
% std's sort pinned through baguette: a permutation p with all_different(p), increasing(ys)
% as int_lin_le rows, and ys[p[i]] = xs[i] as array_var_int_element, which
% mznlib/redefinitions.mzn writes as one (p[i] = k) -> (ys[k] = xs[i]) per pair. No instance of
% the sixteen Challenge editions reaches the solver with a var sort (D-0240 section 1); this
% model keeps the route covered. The sum leaves ys = [1, 3, 3, 5], a multiset with a repeat,
% and xs = [5, 3, 1, 3] is its only arrangement with xs[1] = 5 and xs[2] = xs[4].
% MUST-EMIT: all_different_int
% SOLVES-AS: sort_sat
include "globals.mzn";
array [1..4] of var 0..6: xs;
array [1..4] of var 0..6: ys;
constraint sort(xs, ys);
constraint ys[1] = 1 /\ ys[4] = 5;
constraint ys[2] = ys[3];
constraint xs[1] = 5;
constraint xs[2] = xs[4];
constraint sum(xs) = 12;
solve satisfy;
output ["xs = \(xs);\nys = \(ys);\n"];
