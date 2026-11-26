% M18-coverage-T6 (docs/DECISIONS.md D-0240): arg_max over var int as array_int_maximum plus two
% reified bound rows per position, in place of std's scaled copies.
%
% MiniZinc 2.10.1's std/fzn_arg_max_int.mzn is
%   w[j] = n * xs[j] + (u - j),  Mx = max(w),  (idx != j) = (Mx > w[j])
% one variable per position whose hull is n times the hull of xs[j], and a maximum over
% them. The tie is broken by the (u - j) term: the FIRST position of the maximum wins.
% Over a wide xs the copies are what the encoding pays for (tower: hulls of 0..1134 become
% 0..17000, and Mx 0..332916, so every w and Mx is a bits variable).
%
% Here the maximum is taken over xs itself, m = max(xs), which baguette keeps whole
% (array_int_maximum, D-0095), and the index is tied to it by two implications per position:
%   idx = j  ->  xs[j] >= m      (xs[j] <= m is the maximum's own row, so xs[j] = m)
%   idx > j  ->  xs[j] <  m      (no earlier position reaches the maximum: the first wins)
% Together they say exactly std's predicate: idx is a position of the maximum and none
% before it is. Their contrapositives are the propagation std's equivalence gives:
% hi(xs[j]) < lo(m) removes j from idx, and lo(xs[j]) >= hi(m) bounds idx above by j.
% m's hull is xs's, so no variable wider than the input is introduced.

predicate fzn_maximum_arg_int(array [int] of var int: xs, var int: idx) =
  let {
    int: l = min(index_set(xs));
    int: u = max(index_set(xs));
    var lb_array(xs)..ub_array(xs): m = max(xs);
  } in
  idx >= l /\ idx <= u
    /\ forall (j in l..u) ((idx = j -> xs[j] >= m) /\ (idx > j -> xs[j] < m));
