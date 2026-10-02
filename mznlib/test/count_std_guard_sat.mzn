% Guard for D-0097 (M7-T23): the counting family is NOT routed to gcc.
% mznlib/ shadows no fzn_count_eq, so a constant-value count, exactly, at_most and
% at_least all reach std's decomposition -- the int_eq_reif sum -- and never
% baguette_global_cardinality.  D-0097 measured the route on the corpus and withdrew
% it: gcc's rows are bounds-level, so a one-value cover loses the decomposition's
% interior-value pruning and gains no cross-value reasoning.  A row that re-adds
% the route must re-measure first, and flip these directives when it does.
% No committed artefact: check_mznlib.sh only checks that it flattens and the
% directives hold.
% MUST-EMIT: int_eq_reif
% MUST-NOT-EMIT: baguette_global_cardinality
include "globals.mzn";
array [1..4] of var 1..3: x;
var 0..4: n;
constraint count(x, 2, n);
constraint n >= 2;
constraint exactly(1, x, 3);
constraint at_most(1, x, 1);
constraint at_least(1, x, 2);
solve satisfy;
