%-----------------------------------------------------------------------------%
% global_cardinality_closed stays whole, and says what closing the cover implies
% (M7-T28, D-0146).
%
% std/fzn_global_cardinality_closed.mzn in 2.10.1 is ALREADY one call away from gcc:
% it restricts every xs[i] to the cover and calls global_cardinality, which reaches
% fzn_global_cardinality, which mznlib/fzn_global_cardinality.mzn keeps whole
% (lib/core/prop/gcc.ml, D-0078).  D-0122 counted this global as decomposed because
% its census reads the model's SOURCE; the flattened .fzn never held a decomposition.
% Measured on 2.10.1 (D-0146, step 1).
%
% So this file is not a route that was missing.  It does two things std does not:
%
%   1. It PINS the route.  A std that decomposed the closed form again would
%      otherwise reach baguette as int_eq_reif sums without a line of this
%      repository changing.
%   2. It states the one consequence of a CLOSED cover that gcc.ml does not derive:
%      every xs[i] lands on exactly one cover value, so the counts sum to |xs|.  That
%      is the decomposition MiniZinc 1.x shipped, and it is a linear row, so the
%      Linear propagator carries it with its own justification.  It holds only when
%      the cover has no repeated value (a repeated value counts the same x twice),
%      and the guard below says so rather than assuming it.
%
% The domain restriction is std's, word for word: MiniZinc applies it to the
% declaration, and a cover with gaps becomes a declared set domain, whose holes the
% front end posts as one Ne instance each (M7-T11, D-0072).
%-----------------------------------------------------------------------------%

include "fzn_global_cardinality.mzn";
include "global_cardinality.mzn";

predicate fzn_global_cardinality_closed(
  array [int] of var int: xs,
  array [int] of int: cover,
  array [int] of var int: count,
) =
  forall (i in index_set(xs)) (xs[i] in {d | d in cover})
  /\ global_cardinality(xs, cover, count)
  /\ if card({d | d in cover}) = length(cover) then sum(count) = length(xs) else true endif;
