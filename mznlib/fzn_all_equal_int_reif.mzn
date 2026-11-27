% M18-coverage-T7 (docs/DECISIONS.md D-0233): the reified all_equal as a CHAIN of
% equalities.
%
% MiniZinc 2.10.1's std/fzn_all_equal_int_reif.mzn is
%   b <-> forall (i, j in index_set(xs) where i < j) (xs[i] = xs[j])
% n (n - 1) / 2 reified equalities. Equality is transitive, so the n - 1 equalities of
% every element with the first one say the same thing:
%   b <-> forall (i in index_set(xs) where i > first) (xs[i] = xs[first])
% Fewer rows (3 instead of 6 for four elements, 2 instead of 3 for three), the same
% solutions, and a STRONGER negation: with b false the decomposition is one clause over
% the negated equalities, and with xs[1] = xs[2] known true the pairwise clause still has
% two open literals (xs[1] = xs[3], xs[2] = xs[3]) where the chain's has one (xs[3] =
% xs[1]), which unit propagation then sets false.
%
% The unreified all_equal keeps std's text: at the top level the flattener ALIASES the
% variables of an equality between two variables, so pairwise or chained, nothing reaches
% the solver but the shared variable.

predicate fzn_all_equal_int_reif(array [int] of var int: xs, var bool: b) =
  let {
    int: f = min(index_set(xs));
  } in
  b <-> forall (i in index_set(xs) where i > f) (xs[i] = xs[f]);
