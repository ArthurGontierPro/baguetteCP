% The fallback (M4-T10, D-0096 section 5): a VARIABLE resource is not linear over the
% order encoding, so mznlib/fzn_cumulative.mzn must hand it to std's time-indexed
% decomposition and emit no baguette_cumulative call at all.
% MUST-NOT-EMIT: baguette_cumulative
% MUST-EMIT: int_le_reif
include "globals.mzn";
var 0..3: a;
var 0..3: b;
var 1..2: ra;
constraint cumulative([a, b], [2, 2], [ra, 1], 2);
solve satisfy;
