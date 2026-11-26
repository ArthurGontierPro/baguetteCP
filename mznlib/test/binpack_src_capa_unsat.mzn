% Provenance model for test/models/binpack_capa_unsat.fzn (M18-coverage-T4, D-0220).
% Three items of weight 3 into two bins of capacity 4 and 5: the total fits (9 <= 9), no
% packing does, so the refutation needs the rows of both bins.
% MUST-EMIT: baguette_bool_lin_le
% MUST-NOT-EMIT: bool2int
% SOLVES-AS: binpack_capa_unsat
include "globals.mzn";
array [1..3] of var 1..2: x;
constraint bin_packing_capa([4, 5], x, [3, 3, 3]);
solve satisfy;
