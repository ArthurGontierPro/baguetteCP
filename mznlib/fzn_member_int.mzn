% M7-T28 (docs/DECISIONS.md D-0151 section 3, D-0159): member, kept whole.
%
% MiniZinc 2.10.1's std/fzn_member_int.mzn is `exists (i in index_set(x)) (x[i] == y)`,
% which reached the solver as n int_eq_reif and a clause. Here the n Booleans stay -- they
% are the SELECTORS lib/core/prop/member.ml reasons over, introduced by this `let` as
% regular's state flags are -- and the relation is ONE call, `baguette_member(x, y, b)`.
% A constant array is a domain restriction, which the flattener does better than any
% propagator. lib/core/prop/member.ml's header states the rows.

predicate baguette_member(
  array [int] of var int: x,
  var int: y,
  array [int] of var bool: b,
);

predicate fzn_member_int(array [int] of var int: x, var int: y) =
  if length(x) = 0 then
    false
  elseif is_fixed(x) then
    y in { fix(x[i]) | i in index_set(x) }
  else
    let {
      array [index_set(x)] of var bool: b;
    } in baguette_member(array1d(x), y, array1d(b))
  endif;
