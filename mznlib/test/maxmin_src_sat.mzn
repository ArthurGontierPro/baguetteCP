% Provenance model for test/models/maxmin_sat.fzn (M4-T9, D-0095).
% std's `maximum' must reach mznlib/redefinitions-2.0.mzn's BODYLESS array_int_maximum
% and flatten to ONE array_int_maximum call, not to std's chain of int_max auxiliaries
% and the reified equalities those used to decompose into.  The committed .fzn was
% written by hand (no MiniZinc on the machine that wrote it), so it is checked by the
% directives below rather than byte for byte.
% MUST-EMIT: array_int_maximum
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: maxmin_sat
include "globals.mzn";
var 4..5: m;
var 0..5: a;
var 0..5: b;
var 0..3: c;
constraint maximum(m, [a, b, c]);
constraint b <= a;
constraint a + b + c <= 6;
solve :: int_search([a, b, c, m], input_order, indomain_min, complete) satisfy;
output ["m = \(m);\na = \(a);\nb = \(b);\nc = \(c);\n"];
