%-----------------------------------------------------------------------------%
% global_cardinality_low_up stays whole too (M6-T13, D-0087).
%
% std/fzn_global_cardinality_low_up.mzn decomposes into one `count' sum per cover
% value, ranged against [lbound[i], ubound[i]] -- the same per-value rows
% fzn_global_cardinality.mzn's header explains are no substitute for gcc's
% interval-capacity rule (D-0078).  So this file does what that one does: it states
% each count as a variable and hands the call to the bodyless
% `baguette_global_cardinality', which lib/core/prop/gcc.ml receives.
%
% EACH COUNT IS DECLARED ON ITS OWN BOUNDS, max(0, lbound[i])..min(|x|, ubound[i]).
% That is the low_up constraint itself, not a heuristic: count i must lie in
% [lbound[i], ubound[i]] by the predicate's meaning, and in [0, |x|] by being a tally
% over |x| variables, so the declaration is exactly the intersection and nothing is
% lost or assumed.  An empty intersection is an empty domain, which MiniZinc reports
% as an unsatisfiable model -- the right answer.  Equal bounds give a one-value count,
% which MiniZinc writes as a constant; the front end takes a constant count as a VIEW
% (D-0082), measured identical to a variable fixed at the root.
%
% `array [int]', not `array [index_set(cover)]': the comprehension below is 1-based,
% and std's global_cardinality_low_up hands this predicate array1d(cover), so the two
% agree there -- but a model that calls the fzn_ predicate directly with a cover not
% indexed from 1 would otherwise be an index-set mismatch error.  The front end checks
% only that cover and counts have the same length.  (This one word differs from the
% text M7-T18's request carried; the reason is the sentence above.)
%
% THE INCLUDE IS LOAD-BEARING: `baguette_global_cardinality' is declared in
% fzn_global_cardinality.mzn (mznlib's, which the solver's library path finds before
% std's), and a body that names an undeclared predicate is a type error.
%
% UNFLATTENED-UNTESTED at the time of writing: the machine this was written on has no
% MiniZinc.  mznlib/test/gcc_low_up_src_{sat,unsat}.mzn are its provenance models and
% mznlib/test/check_mznlib.sh asserts they flatten to a `baguette_global_cardinality'
% call with no `int_eq_reif' decomposition and solve as test/expected/gcc_low_up_*.out
% say.  Run it on a node with a flattener:
%   MZN=/path/to/minizinc mznlib/test/check_mznlib.sh
%-----------------------------------------------------------------------------%

include "fzn_global_cardinality.mzn";

predicate fzn_global_cardinality_low_up(
  array [int] of var int: x,
  array [int] of int: cover,
  array [int] of int: lbound,
  array [int] of int: ubound,
) =
  let {
    array [int] of var int: c = [
      let { var max(0, lbound[i])..min(length(x), ubound[i]): ci } in ci
    | i in index_set(cover)
    ];
  } in baguette_global_cardinality(x, cover, c);
