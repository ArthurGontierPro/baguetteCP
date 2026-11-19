% Provenance model for test/models/member_unsat.fzn (M7-T28, D-0159).
% Three odd values (each over {1, 3, 5}) and y = x[1] + x[2], which is even, one of them:
% a parity argument no propagator states. The root removes y's even values (the hole-only
% exclusions, made ahead), the bounds of the sum then leave y in {3, 5}, and the search
% refutes the rest through selector deaths across the declared holes -- the shape the
% bound-form rows exist for.
% MUST-EMIT: baguette_member
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: member_unsat
include "globals.mzn";
array [1..3] of var {1, 3, 5}: x;
var 1..6: y;
constraint member(x, y);
constraint y = x[1] + x[2];
solve satisfy;
