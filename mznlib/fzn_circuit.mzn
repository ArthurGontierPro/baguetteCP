% M18-coverage-T3 (docs/DECISIONS.md D-0217): circuit, kept whole.
%
% MiniZinc 2.10.1's std/fzn_circuit.mzn is all_different(xs), all_different(order),
% xs[i] != i, order[l] = 1 and `order[xs[i]] = if order[i] = n then 1 else order[i] + 1`,
% one array_var_int_element per node that std decomposes further into reified equalities.
% Nothing in it reasons about a chain of fixed arcs.
%
% Here all_different(xs) stays (native, lib/core/prop/alldiff.ml), and so do the domain
% restrictions xs[i] in S and xs[i] != i (the flattener writes them as declared holes);
% the no-subtour reasoning is ONE call, `baguette_circuit(xs, pos, l)`, reaching
% lib/core/prop/circuit.ml:
%
%   - l = min(S), the ROOT, whose position is the constant 0;
%   - pos, one POSITION var 1..n-1 per node other than the root, introduced by this
%     `let` (as table's selectors are). The .opb defines the constraint by Miller, Tucker
%     and Zemlin's rows `xs[u] = v -> pos[v] = pos[u] + 1` (v not the root) and
%     `xs[u] = l -> pos[u] = n - 1`; lib/core/prop/circuit.ml's header states them.
%
% A circuit over one node is false (xs[l] != l), as std's.

include "all_different.mzn";

predicate baguette_circuit(
  array [int] of var int: xs,
  array [int] of var int: pos,
  int: root,
);

predicate fzn_circuit(array [int] of var int: x) =
  let {
    array [int] of var int: xs = array1d(x);
    set of int: S = index_set(x);
    int: l = if card(S) = 0 then 1 else min(S) endif;
    int: u = if card(S) = 0 then 0 else max(S) endif;
    int: n = card(S);
    array [l + 1..u] of var 1..n - 1: pos;
  } in
  if n = 0 then
    true
  elseif n = 1 then
    false
  else
    all_different(x)
      /\ forall (i in S) (x[i] in S /\ x[i] != i)
      /\ baguette_circuit(
        [x[i] | i in S],
        [pos[i] | i in l + 1..u],
        l,
      )
  endif;
