% Provenance model for test/models/gcc_closed_sat.fzn (M7-T28, D-0146).
% global_cardinality_closed must reach mznlib/fzn_global_cardinality_closed.mzn: ONE
% baguette_global_cardinality call, the domain restriction applied to the declarations
% (the cover {1, 2, 4} has a gap, so x becomes a set domain), and the implied row
% sum(c) = 4 -- not std's int_eq_reif decomposition.
% MUST-EMIT: baguette_global_cardinality
% MUST-NOT-EMIT: int_eq_reif
% SOLVES-AS: gcc_closed_sat
include "globals.mzn";
array [1..4] of var 0..5: x;
array [1..3] of var 0..4: c;
constraint global_cardinality_closed(x, [1, 2, 4], c);
constraint c[1] = 2;
constraint x[1] < x[2];
constraint x[3] >= x[4] + 1;
solve satisfy;
