% Provenance model for test/models/maxmin_int_max_sat.fzn (M4-T9, D-0095).
% The two-element `max(a, b)' / `min(a, b)' reach redefinitions.mzn's int_max / int_min,
% which are now array_int_maximum / array_int_minimum over [a, b] -- one call each, and
% none of the reified equalities the old decomposition emitted.
% MUST-EMIT: array_int_maximum
% MUST-EMIT: array_int_minimum
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: maxmin_int_max_sat
var 0..4: a;
var 0..4: b;
var 3..4: hi;
var 1..4: lo;
constraint hi = max(a, b);
constraint lo = min(a, b);
constraint b <= a;
solve :: int_search([a, b], input_order, indomain_min, complete) satisfy;
output ["a = \(a);\nb = \(b);\nhi = \(hi);\nlo = \(lo);\n"];
