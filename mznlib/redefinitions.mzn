%-----------------------------------------------------------------------------%
% baguette solver library -- redefinitions.mzn
%
% baguette accepts the FlatZinc subset docs/SPEC.md 2.1 fixes, and
% lib/flatzinc/builder.ml's `implemented` list is the normative copy of it:
%
%   int_lin_le int_lin_eq int_lin_ne int_le int_lt int_eq int_ne
%   bool_clause array_bool_or array_bool_and bool2int bool_eq bool_not
%   int_lin_le_reif int_le_reif int_eq_reif int_ne_reif
%   int_abs int_times int_div
%   all_different_int array_int_element
%
% Anything else MiniZinc would emit is given a body HERE, so that it decomposes
% into that subset rather than reaching the front end and being refused.  A
% builtin left undefined is not silently dropped: the front end names it and
% exits non-zero (SPEC 2.1, normative), which is the behaviour we want for the
% ones this file cannot express (float, int_pow with a variable exponent).
%
% The converse direction lives in fzn_all_different_int.mzn: a constraint
% baguette DOES have a propagator for must survive flattening intact, because
% the propagator and its justification are the point.
%
% std/redefinitions.mzn is a two-line comment, so shadowing it costs nothing.
% The versioned std/redefinitions-2.*.mzn files are NOT shadowed: they already
% map the _nonshifted and 2d_nonshifted element forms, array_int_maximum /
% array_int_minimum, bool_clause_reif and int_pow_fixed onto the builtins this
% file defines.
%-----------------------------------------------------------------------------%

% var set of int -> array of var bool.  baguette has no set variables at all,
% so this is the only way a model carrying them can flatten.
include "nosets.mzn";

%-----------------------------------------------------------------------------%
% Integer arithmetic
%-----------------------------------------------------------------------------%

predicate int_plus(var int: x, var int: y, var int: z) = x + y = z;

predicate int_max(var int: x, var int: y, var int: z) =
  z >= x /\ z >= y /\ (z = x \/ z = y);

predicate int_min(var int: x, var int: y, var int: z) =
  z <= x /\ z <= y /\ (z = x \/ z = y);

% x = y*q + z with q = x div y, truncating toward zero -- which is exactly what
% baguette's int_div does (SPEC 2.1, "Integer division, modulo and absolute
% value"), so the remainder takes the sign of the dividend for free.
% |y*q| <= |x| and |z| < |y| <= |x| bound both auxiliaries by x's magnitude;
% they are declared with that bound because baguette refuses a `var int` with
% no domain rather than defaulting it to a machine word.
predicate int_mod(var int: x, var int: y, var int: z) =
  let {
    int: bx = max(abs(lb(x)), abs(ub(x)));
    var -bx..bx: q;
    var -bx..bx: t;
  } in
    int_div(x, y, q) /\ int_times(y, q, t) /\ x = t + z;

%-----------------------------------------------------------------------------%
% Reified integer relations
%
% int_lin_le_reif, int_le_reif, int_eq_reif and int_ne_reif are native (M3-T4,
% D-0057).  The remaining reified forms reduce to them.
%-----------------------------------------------------------------------------%

predicate int_lt_reif(var int: x, var int: y, var bool: b) =
  int_lin_le_reif([1, -1], [x, y], -1, b);

predicate int_lin_eq_reif(
  array [int] of int: as,
  array [int] of var int: xs,
  int: y,
  var bool: b,
) =
  let { var bool: p; var bool: q } in
    int_lin_le_reif(as, xs, y, p) /\
    int_lin_le_reif([-a | a in as], xs, -y, q) /\
    array_bool_and([p, q], b);

predicate int_lin_ne_reif(
  array [int] of int: as,
  array [int] of var int: xs,
  int: y,
  var bool: b,
) = let { var bool: nb } in int_lin_eq_reif(as, xs, y, nb) /\ bool_not(nb, b);

%-----------------------------------------------------------------------------%
% Boolean relations
%
% Written as explicit bool_clause rows rather than as MiniZinc connectives, so
% that the flattener cannot route them back through a reified form this file is
% in the middle of defining.
%-----------------------------------------------------------------------------%

predicate bool_and(var bool: x, var bool: y, var bool: b) =
  array_bool_and([x, y], b);

predicate bool_or(var bool: x, var bool: y, var bool: b) =
  array_bool_or([x, y], b);

predicate bool_le(var bool: x, var bool: y) = bool_clause([y], [x]);

predicate bool_lt(var bool: x, var bool: y) =
  bool_clause([], [x]) /\ bool_clause([y], []);

% b <-> (x = y)
predicate bool_eq_reif(var bool: x, var bool: y, var bool: b) =
  bool_clause([y], [b, x]) /\
  bool_clause([x], [b, y]) /\
  bool_clause([b, x, y], []) /\
  bool_clause([b], [x, y]);

% b <-> (x != y)
predicate bool_xor(var bool: x, var bool: y, var bool: b) =
  bool_clause([x, y], [b]) /\
  bool_clause([], [b, x, y]) /\
  bool_clause([b, y], [x]) /\
  bool_clause([b, x], [y]);

% b <-> (x -> y)
predicate bool_le_reif(var bool: x, var bool: y, var bool: b) =
  bool_clause([y], [b, x]) /\ bool_clause([b, x], []) /\ bool_clause([b], [y]);

% b <-> (not x /\ y)
predicate bool_lt_reif(var bool: x, var bool: y, var bool: b) =
  bool_clause([], [b, x]) /\ bool_clause([y], [b]) /\ bool_clause([b, x], [y]);

predicate bool_lin_le(array [int] of int: as, array [int] of var bool: xs, int: y) =
  int_lin_le(as, [bool2int(xs[i]) | i in index_set(xs)], y);

predicate bool_lin_eq(array [int] of int: as, array [int] of var bool: xs, var int: y) =
  int_lin_eq(as ++ [-1], [bool2int(xs[i]) | i in index_set(xs)] ++ [y], 0);

% An odd number of the xs hold.  k is the number of *pairs* that do.
predicate array_bool_xor(array [int] of var bool: xs) =
  let {
    int: n = card(index_set(xs));
    var 0..(n div 2): k;
  } in sum (i in index_set(xs)) (bool2int(xs[i])) = 2 * k + 1;

%-----------------------------------------------------------------------------%
% Element
%
% array_int_element -- constant array, variable index -- is native and DOMAIN
% consistent, with the index as a view rather than an auxiliary (M4-T3,
% D-0058).  The variable-array forms have no propagator, so they decompose;
% array_bool_element is routed THROUGH the native one rather than decomposed,
% because its array is constant.
%-----------------------------------------------------------------------------%

predicate array_bool_element(var int: idx, array [int] of bool: xs, var bool: y) =
  array_int_element(
    idx,
    array1d(index_set(xs), [bool2int(xs[i]) | i in index_set(xs)]),
    bool2int(y),
  );

predicate array_var_int_element(var int: idx, array [int] of var int: xs, var int: y) =
  let { set of int: is = index_set(xs) } in
    idx >= min(is) /\
    idx <= max(is) /\
    forall (i in is) ((idx = i) -> (xs[i] = y));

predicate array_var_bool_element(
  var int: idx,
  array [int] of var bool: xs,
  var bool: y,
) =
  let { set of int: is = index_set(xs) } in
    idx >= min(is) /\
    idx <= max(is) /\
    forall (i in is) ((idx = i) -> (xs[i] = y));

%-----------------------------------------------------------------------------%
% Membership in a constant set
%
% The gaps, not the members: a set with few holes costs one int_ne per hole
% instead of one int_eq_reif per member.  The comparison picks whichever side
% is smaller, so neither a dense range nor a sparse set degrades.
%-----------------------------------------------------------------------------%

predicate set_in(var int: x, set of int: s) =
  if card(s) = 0 then
    false
  else
    x >= min(s) /\
    x <= max(s) /\
    forall (v in (min(s)..max(s)) diff s) (x != v)
  endif;

predicate set_in_reif(var int: x, set of int: s, var bool: b) =
  if card(s) = 0 then
    b = false
  elseif card(min(s)..max(s)) - card(s) <= card(s) then
    array_bool_and(
      [x >= min(s), x <= max(s)] ++ [x != v | v in (min(s)..max(s)) diff s],
      b,
    )
  else
    array_bool_or([x = v | v in s], b)
  endif;
