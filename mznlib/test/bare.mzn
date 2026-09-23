% The model that includes NOTHING.
%
% redefinitions.mzn is pulled into every model, so every BODY in it has to
% type-check in every model -- including one that never includes globals.mzn
% and never mentions the predicate whose body needs it. The first version of
% mznlib/compat_mzn1.mzn got this wrong: its global_cardinality bridge called
% the standard three-argument predicate without including the file that
% declares it, and the resulting type error was reported against the library,
% turning twelve unrelated instances from flattening to FLATTEN-FAIL. The
% repo's own gate cannot see that -- it consumes FlatZinc, not MiniZinc -- so
% this model and check_mznlib.sh are where it is caught instead.
var 1..3: x;
constraint x > 1;
solve satisfy;
