% Provenance model for test/models/argmin_bool_unsat.fzn (M18-coverage-T6, D-0240).
% std's arg_min over var bool pinned through baguette, asked to be at least t, a variable in
% 3..4 (so that the flattener cannot settle it): the first false position is then 3 or 4, so
% c[1] and c[2] are true, which c[1] != c[2] forbids; and c all true puts arg_min at the
% FIRST position, 1, which the bound forbids too. No solution.
% MUST-EMIT: array_int_minimum
include "globals.mzn";
array [1..4] of var bool: c;
var 1..4: i = arg_min(c);
var 3..4: t;
constraint i >= t;
constraint c[1] != c[2];
solve satisfy;
output ["c = \(c);\ni = \(i);\n"];
