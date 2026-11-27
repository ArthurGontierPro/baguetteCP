%-----------------------------------------------------------------------------%
% global_cardinality_low_up_closed stays whole (M7-T28, D-0146).
%
% std/fzn_global_cardinality_low_up_closed.mzn in 2.10.1 restricts every xs[i] to the
% cover, calls global_cardinality_low_up -- which reaches the mznlib route of
% fzn_global_cardinality_low_up.mzn, i.e. lib/core/prop/gcc.ml -- and checks the par
% condition |xs| in sum(lbound)..sum(ubound).  As for the closed three-argument form
% (fzn_global_cardinality_closed.mzn says it at length), the route was never missing.
%
% What this file adds is the same as there: the route pinned, and the implied row.
% The counts are declared HERE, on the bounds fzn_global_cardinality_low_up.mzn
% would give them (max(0, lbound[i])..min(|xs|, ubound[i]), the intersection of the
% predicate's meaning with a tally's range), so that the closed cover's consequence
% sum(c) = |xs| can be stated over them.  Under a cover with a repeated value the sum
% would be wrong and is not posted, and neither is std's par check, which sums the
% repeat's bounds twice: global_cardinality_closed(x, [1,1], [2,2], [2,2]) with
% x = [1,1] holds (Gecode agrees), and the check 2 in 4..4 made it UNSAT. That wrong
% answer was in this file since D-0146; std 2.10.1 and Chuffed give it too (D-0255,
% models mznlib/test/gcc_low_up_closed_dupcover_src_*).
%-----------------------------------------------------------------------------%

include "fzn_global_cardinality.mzn";

predicate fzn_global_cardinality_low_up_closed(
  array [int] of var int: xs,
  array [int] of int: cover,
  array [int] of int: lbound,
  array [int] of int: ubound,
) =
  let {
    array [int] of var int: c = [
      let { var max(0, lbound[i])..min(length(xs), ubound[i]): ci } in ci
    | i in index_set(cover)
    ];
  } in forall (i in index_set(xs)) (xs[i] in {d | d in array2set(cover)})
    /\ baguette_global_cardinality(xs, cover, c)
    /\ if card(array2set(cover)) = length(cover) then length(xs) in sum(lbound)..sum(ubound) else true endif
    /\ if card(array2set(cover)) = length(cover) then sum(c) = length(xs) else true endif;
