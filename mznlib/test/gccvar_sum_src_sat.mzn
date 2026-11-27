% M18-coverage-T14 / D-0255: the satisfiable scene where the implied row between the counts is
% LOAD-BEARING. c1 >= y, c2 >= z, y + z >= 3 gives each count a lower bound of 1 only, so the
% decisions x1 = 3, x2 = 3 are open; the row then caps c1 + c2 at 2, which empties y + z >= 3.
% That conflict is learned and the search goes on to x = [3,2,2,1] (Gecode: the same).
% Dropping the row from the .opb makes veripb 3.0.2 reject a later line of the proof.
% MUST-EMIT: int_lin_le
% MUST-NOT-EMIT: baguette_global_cardinality
% SOLVES-AS: gccvar_sum_src_sat
include "globals.mzn";
array [1..4] of var 1..3: x;
array [1..3] of var 0..4: c;
var 0..2: y;
var 0..2: z;
constraint global_cardinality(x, [1, 2, 3], c);
constraint c[1] >= y /\ c[2] >= z /\ y + z >= 3;
solve :: int_search(x, input_order, indomain_max) satisfy;
