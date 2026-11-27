% M18-coverage-T7 (docs/DECISIONS.md D-0233, which chose the three cheap globals' shapes
% by measurement on the 105 Challenge instances that call them): alldifferent_except_0,
% and all_different(xs, S), as AT MOST ONE indicator per value outside the exception set.
%
% MiniZinc 2.10.1's std/fzn_alldifferent_except.mzn writes, when every variable is
% bounded,
%   global_cardinality(xs, A, [0 | v in A], [1 | v in A])   A = dom_array(xs) diff except
% which mznlib/fzn_global_cardinality_low_up.mzn routes to baguette's gcc with one 0..1
% count variable per value. Here the same constraint is written per value v of A as
%   baguette_bool_lin_le([1, ...], [xs[i] = v | i where v in dom(xs[i])], 1)
% an int_lin_le over the indicators `xs[i] = v` themselves (docs/SPEC.md 2.1; the builtin
% D-0220 added for bin packing, Booleans read as 0..1 with no bool2int copy). It is the
% shape Chuffed's own library gives the same std call (bool_sum_le over the same
% indicators), and it measured better than the gcc route on the Challenge instances that
% call alldifferent_except_0 (D-0233 section 3): the indicators are std's int_eq_reif
% Booleans, shared by common-subexpression elimination with the rest of the model, and the
% learned constraints are written over them.
%
% WHY THIS IS THE DEFINITION. Two variables can share a value only if that value is in the
% exception set: for v outside it, at most one xs[i] takes v, which is the row. A value no
% two domains hold needs no row. The unbounded case keeps std's pairwise text.

predicate baguette_bool_lin_le(array [int] of int: a, array [int] of var bool: x, int: c);

predicate fzn_alldifferent_except(array [int] of var int: xs, set of int: except) =
  if forall (i in index_set(xs)) (has_bounds(xs[i])) then
    forall (v in dom_array(xs) diff except) (
      let {
        array [int] of int: is = [i | i in index_set(xs) where v in dom(xs[i])];
      } in
      if length(is) <= 1 then true else baguette_bool_lin_le([1 | i in is], [xs[i] = v | i in is], 1) endif
    )
  else
    forall (i, j in index_set(xs) where i < j) ((xs[i] in except /\ xs[j] in except) \/ xs[i] != xs[j])
  endif;
