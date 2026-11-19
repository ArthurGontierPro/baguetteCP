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
% would be wrong and is not posted; the par check std makes is kept either way.
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
    /\ length(xs) in sum(lbound)..sum(ubound)
    /\ if card(array2set(cover)) = length(cover) then sum(c) = length(xs) else true endif;
