% Provenance model for test/models/lex_bool_sat.fzn (M18-coverage-T5, D-0239).
% Boolean rows: x <lex y with one cell shared by both rows (p, at the second position) and
% a constant in y; y <=lex z with z one cell longer; at least three of x set and z with at
% most two, so the first strict position is pushed late.
% MUST-EMIT: baguette_bool_lin_le
% MUST-NOT-EMIT: int_lin_le_reif
% SOLVES-AS: lex_bool_sat
include "globals.mzn";
array [1..4] of var bool: x;
array [1..3] of var bool: w;
var bool: p;
array [1..4] of var bool: y = [w[1], p, true, w[2]];
array [1..5] of var bool: z;
constraint x[2] = p;
constraint lex_less(x, y);
constraint lex_lesseq(y, z);
constraint sum(i in 1..4) (bool2int(x[i])) >= 3;
constraint sum(i in 1..5) (bool2int(z[i])) <= 3;
constraint w[3] \/ z[5];
solve satisfy;
