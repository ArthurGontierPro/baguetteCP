% M7-T28 (docs/DECISIONS.md D-0159): member over Booleans, kept whole.
%
% std's fzn_member_bool is fzn_member_int's decomposition over var bool. A Boolean is the
% integer 0..1 to baguette (D-0007), so this is the same relation and the same propagator
% under a second spelling, `baguette_member_bool(x, y, b)`; see fzn_member_int.mzn.

predicate baguette_member_bool(
  array [int] of var bool: x,
  var bool: y,
  array [int] of var bool: b,
);

predicate fzn_member_bool(array [int] of var bool: x, var bool: y) =
  if length(x) = 0 then
    false
  else
    let {
      array [index_set(x)] of var bool: b;
    } in baguette_member_bool(array1d(x), y, array1d(b))
  endif;
