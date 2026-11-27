% Provenance model for test/models/argsort_opt.fzn (M18-coverage-T6, D-0240).
% std's arg_sort pinned through baguette: all_different(p) and, per adjacent pair,
% xs[p[j]] <= xs[p[j + 1]] with the tie broken by p[j] < p[j + 1], each xs[p[j]] an
% array_var_int_element. No instance of the sixteen Challenge editions reaches the solver with
% a var arg_sort (D-0240 section 1). Minimise the weighted positions of the sorted order over
% inputs that may tie.
% MUST-EMIT: all_different_int
% SOLVES-AS: argsort_opt
include "globals.mzn";
array [1..4] of var 1..3: xs;
array [1..4] of var 1..4: p = arg_sort(xs);
constraint xs[1] >= xs[4];
constraint xs[2] != xs[3];
var int: obj = 4 * p[1] + 3 * p[2] + 2 * p[3] + p[4] + xs[1] + xs[2];
solve minimize obj;
output ["xs = \(xs);\np = \(p);\nobj = \(obj);\n"];
