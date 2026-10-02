% Provenance model for test/models/maxmin_min_unsat.fzn (M4-T9, D-0095): std's
% `minimum', kept whole, under search, UNSATISFIABLE.  The selectors are written as
% reified comparisons, which MiniZinc lowers to int_lin_le_reif / int_le_reif.
% MUST-EMIT: array_int_minimum
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: maxmin_min_unsat
include "globals.mzn";
var 0..4: m;
var 0..4: a;
var 0..4: b;
var bool: p;
var bool: q;
constraint minimum(m, [a, b]);
constraint a = b;
constraint p <-> (m + 1 <= a);
constraint q <-> (m + 1 <= b);
constraint p \/ q;
solve :: int_search([p, q, m, a, b], input_order, indomain_min, complete) satisfy;
