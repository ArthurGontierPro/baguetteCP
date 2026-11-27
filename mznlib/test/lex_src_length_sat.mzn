% Provenance model for test/models/lex_length_sat.fzn (M18-coverage-T5, D-0239).
% Arrays of different lengths: x (three cells) <lex y (two cells) holds only through a
% strict position, since x is the longer; x <=lex z (z of four cells) may tie on all three.
% MUST-NOT-EMIT: int_lin_le_reif
% SOLVES-AS: lex_length_sat
include "globals.mzn";
array [1..3] of var 0..2: x;
array [1..2] of var 0..2: y;
array [1..4] of var 0..2: z;
constraint lex_less(x, y);
constraint lex_lesseq(x, [z[i] | i in 1..3]) /\ lex_greater(z, x);
constraint x[1] = y[1] /\ x[2] >= y[2] - 1;
constraint z[1] = x[1] /\ z[2] = x[2] /\ z[3] = x[3];
constraint sum(x) >= 3;
solve satisfy;
