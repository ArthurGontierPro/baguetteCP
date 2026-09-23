% Provenance model for test/models/gcc_shim_unsat.fzn (M7-T15).
% Five variables over three values cannot have equal counts. UNSAT, and not by
% an arithmetic MiniZinc can do at flatten time.
include "globals.mzn";
array [1..5] of var 0..2: x;
array [0..2] of var 0..2: c;
constraint global_cardinality(x, c);
constraint c[0] = c[1];
constraint c[1] = c[2];
solve satisfy;
