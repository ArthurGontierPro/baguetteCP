% Provenance model for test/models/lex_lesseq_sat.fzn (M18-coverage-T5, D-0239).
% Two rows over 0..3 with x <=lex y, x[1] >= y[1] (so the first column ties) and x's sum
% above y's, which forces the first strict position past the second column.
% MUST-EMIT: int_lin_le
% MUST-NOT-EMIT: int_lin_le_reif
% SOLVES-AS: lex_lesseq_sat
include "globals.mzn";
array [1..4] of var 0..3: x;
array [1..4] of var 0..3: y;
constraint lex_lesseq(x, y);
constraint x[1] >= y[1];
constraint x[2] >= 1 /\ y[2] <= 1;
constraint sum(x) > sum(y) + 1;
solve satisfy;
