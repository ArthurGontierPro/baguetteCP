% M18-coverage-T7 (docs/DECISIONS.md D-0233): nvalue without the bool2int copies.
%
% MiniZinc 2.10.1's std/fzn_nvalue.mzn is
%   n == sum (j in lb_array(xs)..ub_array(xs)) (exists (i in index_set(xs)) (xs[i] = j))
% Flattened, each (variable, value) pair costs an int_eq_reif (the INDICATOR `xs[i] = j`,
% a Boolean shared by common-subexpression elimination with any other part of the model
% that says the same), each value an array_bool_or (the Boolean `value j is taken`) AND a
% bool2int (a second, 0..1 integer copy of that Boolean, its two rows and its own
% propagator), and the sum one int_lin_eq over the copies.
%
% Here the same rows are written without the copy, as bin packing does (D-0220): one
% `baguette_bool_lin_eq([1, ...], [taken_j | ...], n)`, an int_lin_eq whose terms are the
% value Booleans themselves, read as 0..1 (docs/SPEC.md 2.1). The values summed over are
% those some xs[i] can take (std sums over the whole hull and lets the flattener drop the
% values no domain holds; the sum is the same).
%
% n is also restricted to 0 .. min(length(xs), the number of those values), the bounds of
% the sum. std's flattening finds them by itself, because there n is the variable its own
% int_lin_eq DEFINES; here nothing defines it and, without the line, n would keep its
% declared domain. The restriction excludes no solution: n counts distinct values of xs.

predicate baguette_bool_lin_eq(array [int] of int: a, array [int] of var bool: x, var int: y);

predicate fzn_nvalue(var int: n, array [int] of var int: xs) =
  if length(xs) = 0 then
    n = 0
  else
    let {
      set of int: I = index_set(xs);
      array [int] of int: vs = [j | j in lb_array(xs)..ub_array(xs) where exists (i in I) (j in dom(xs[i]))];
    } in
    n >= 0 /\ n <= min(length(xs), length(vs))
      /\ baguette_bool_lin_eq(
        [1 | j in vs],
        [exists (i in I where vs[k] in dom(xs[i])) (xs[i] = vs[k]) | k in index_set(vs)],
        n
      )
  endif;
