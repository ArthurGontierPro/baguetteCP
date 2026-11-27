% Provenance model for test/models/lex_chain_opt.fzn (M18-coverage-T5, D-0239).
% A 3 x 3 matrix over 1..4 given by its rows, whose COLUMNS increase strictly through
% lex_chain_less (std writes it as lex_less between consecutive columns), a first row >=lex
% the third read backwards, distinct row sums, and an objective that pulls the total down.
% MUST-NOT-EMIT: int_lin_le_reif
% SOLVES-AS: lex_chain_opt
include "globals.mzn";
array [1..3] of var 1..4: r1;
array [1..3] of var 1..4: r2;
array [1..3] of var 1..4: r3;
constraint lex_chain_less(array2d(1..3, 1..3, r1 ++ r2 ++ r3));
constraint lex_greatereq(r1, [r3[4 - j] | j in 1..3]);
constraint all_different([sum(r1), sum(r2), sum(r3)]);
constraint r3[3] >= 2;
solve minimize sum(r1) + sum(r2) + sum(r3);
