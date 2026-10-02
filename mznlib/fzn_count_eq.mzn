%-----------------------------------------------------------------------------%
% The counting family reaches the gcc propagator (M7-T23, D-0097).
%
% ONE FILE ROUTES THE WHOLE FAMILY, because std funnels it through this one
% predicate (MiniZinc 2.10.1, read on the node):
%
%   count(xs, v, n), count_eq(xs, v, n)          -> fzn_count_eq(xs, v, n)
%   count_eq(xs, v, n) with v, n par             -> fzn_count_eq_par -> fzn_count_eq
%   the function count(xs, v) / count_eq(xs, v)  -> var 0..|xs|: n,
%                                                   fzn_count_eq(xs, v, n)
%   count_leq/geq/lt/gt/neq(xs, v, n)            -> z = count(xs, v), z OP n
%   exactly(n, xs, v), at_most(..), at_least(..) -> n OP count(xs, v)
%
% So shadowing fzn_count_eq here, and nothing else, routes every one of them,
% and leaves each wrapper's own argument handling (enum2int, array1d, the
% relational side `z OP n') exactly as std defines it.  Separate fzn_exactly_int
% / fzn_at_most_int / fzn_count_leq files would restate those bodies and could
% only drift from them.  NOTE the direction std gives the relational forms,
% which is not the one their names suggest: count_leq(xs, v, n) is `n <= count',
% and count_geq is `n >= count'.  Delegating rather than restating is also what
% keeps this file from getting that backwards.
%
% A CONSTANT value is a one-value cover: `global_cardinality(xs, [v], [n])'.
% fzn_global_cardinality (mznlib's) bounds n to 0..|xs| -- the tally's own
% range, nothing assumed -- and hands it to the bodyless
% baguette_global_cardinality, which lib/core/prop/gcc.ml receives with its own
% counting justification (D-0078).  A par n arrives as a constant count, which
% the front end takes as a view (D-0082).
%
% A VARIABLE value has no cover at flatten time, and gcc's cover is an array of
% constants (SPEC 2.1), so that case keeps std's decomposition, restated
% verbatim from std/fzn_count_eq.mzn.  `is_fixed' is decided at flatten time,
% so a value that MiniZinc has fixed by the time the call is flattened takes the
% gcc branch.  The _reif forms are not shadowed: a reified gcc is not something
% baguette has, and they stay std's.
%
% WHAT THE FRONT END REFUSES that std's decomposition accepted: the same
% variable twice in xs (lib/flatzinc/compile.ml post_global_cardinality says
% why).  MiniZinc cannot compare variable identities at flatten time, so this
% file cannot route around it; D-0097 records how often the corpus hits it.
%
% THE INCLUDE IS LOAD-BEARING (M7-T15's trap): fzn_global_cardinality is
% declared in mznlib's fzn_global_cardinality.mzn, and a body naming an
% undeclared predicate is a type error reported against EVERY model.
%-----------------------------------------------------------------------------%

include "fzn_global_cardinality.mzn";

predicate fzn_count_eq(array [int] of var int: xs, var int: value, var int: n) =
  if is_fixed(value) then
    fzn_global_cardinality(xs, [fix(value)], [n])
  else
    n = sum (i in index_set(xs)) (xs[i] == value)
  endif;
