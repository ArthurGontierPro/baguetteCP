% Provenance model for test/models/cumulative_sat.fzn (M4-T10, D-0096). cumulative with
% fixed durations, resources and capacity must reach mznlib/fzn_cumulative.mzn and
% flatten to ONE baguette_cumulative call, not to std's time-indexed decomposition
% (whose `s <= t /\ t < s + d` reifications are what int_le_reif marks). The committed
% .fzn was written by hand in the flattener's shape, so check_mznlib.sh reads the
% directives below rather than comparing bytes.
% MUST-EMIT: baguette_cumulative
% MUST-NOT-EMIT: int_le_reif
% SOLVES-AS: cumulative_sat
include "globals.mzn";
var 0..2: s0;
var 0..4: s1;
var 0..4: s2;
var 0..3: s3;
var 0..3: s4;
constraint cumulative([s0, s1, s2, s3, s4], [3, 1, 1, 2, 2], [1, 1, 2, 1, 1], 2);
solve :: int_search([s3, s4, s2, s1, s0], input_order, indomain_max, complete) satisfy;
