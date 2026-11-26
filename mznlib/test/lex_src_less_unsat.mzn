% Provenance model for test/models/lex_less_unsat.fzn (M18-coverage-T5, D-0239).
% x <lex y and y <=lex x over 0..2 cannot both hold: refuted by search over the flags.
% MUST-NOT-EMIT: int_lin_le_reif
% SOLVES-AS: lex_less_unsat
include "globals.mzn";
array [1..3] of var 0..2: x;
array [1..3] of var 0..2: y;
constraint lex_less(x, y);
constraint lex_lesseq(y, x);
solve satisfy;
