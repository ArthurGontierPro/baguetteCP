% Provenance model for test/models/table_bool_sat.fzn (M18-coverage-T1, D-0206).
% An exactly-two-of-four table over var bool, with a[1] -> a[4] and not a[2].
% MUST-EMIT: baguette_table_bool
% SOLVES-AS: table_bool_sat
include "globals.mzn";
array [1..4] of var bool: a;
constraint table(a, [| true, true, false, false | true, false, true, false
                     | true, false, false, true | false, true, true, false
                     | false, true, false, true | false, false, true, true |]);
constraint a[1] -> a[4];
constraint not a[2];
solve satisfy;
