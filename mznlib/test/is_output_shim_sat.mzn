% Provenance model for test/models/is_output_shim_sat.fzn (M7-T15).
% Flattened with baguette's mznlib, which declares `is_output' as an inert
% annotation -- see mznlib/compat_mzn1.mzn. The point of the test is the
% output_var/output_array annotations the .fzn carries: `a' is annotated
% is_output and `z' is not, and the shim being inert means BOTH are printed.
% That is the documented deviation, pinned here so it cannot drift silently.
% Unique solution: a = [1, 2, 3], z = 2.
include "globals.mzn";
array [1..3] of var 1..4: a :: is_output;
var 1..4: z;
constraint all_different(a);
constraint sum(a) = 6;
constraint a[1] < a[2];
constraint a[2] < a[3];
constraint z + a[1] = 3;
solve satisfy;
