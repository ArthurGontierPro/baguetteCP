% Provenance model for test/models/disjunctive_sat.fzn (M4-T10, D-0096): disjunctive with
% fixed durations must reach mznlib/fzn_disjunctive.mzn and flatten to ONE
% baguette_cumulative call at capacity 1, not to std's pairwise disjunctions.
% MUST-EMIT: baguette_cumulative
% MUST-NOT-EMIT: bool_clause
% SOLVES-AS: disjunctive_sat
include "globals.mzn";
var 1..5: t0;
var 1..7: t1;
var 1..3: t2;
var 4..5: t3;
var 1..2: t4;
constraint disjunctive([t0, t1, t2, t3, t4], [2, 1, 2, 1, 1]);
solve :: int_search([t1, t2, t3, t4, t0], input_order, indomain_min, complete) satisfy;
