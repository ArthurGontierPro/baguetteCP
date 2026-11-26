% Provenance model for test/models/nvalue_opt.fzn (M18-coverage-T7, D-0233).
% Colour a 5-cycle plus one chord with as few colours as nvalue counts: the odd cycle needs 3.
% MUST-EMIT: baguette_bool_lin_eq
% MUST-NOT-EMIT: bool2int
% SOLVES-AS: nvalue_opt
include "globals.mzn";
array [1..5] of var 1..4: c;
constraint forall (i in 1..5) (c[i] != c[i mod 5 + 1]);
constraint c[1] != c[3];
var int: k = nvalue(c);
solve minimize k;
output ["c = \(c);\nk = \(k);\n"];
