%-----------------------------------------------------------------------------%
% regular stays whole (M7-T28, D-0146).
%
% std/fzn_regular.mzn decomposes the DFA into n + 1 state variables a[i] in 1..Q and
% a[i+1] = d[a[i], xs[i]] per letter: an array_int_element on a computed index per
% layer, which propagates bounds of a state number and nothing of the automaton's
% structure.  D-0122 measured it on the Challenge editions: 0 complete of 94 attempted
% instances, 70 of them timing out without a single solution.
%
% Kept whole, it reaches lib/core/prop/regular.ml, the layered-graph filtering, which is
% DOMAIN consistent and justifies every pruning as one rup (D-0146 section 3).  What the
% library hands it:
%
%   - the transition table FLATTENED row-major over the symbol range smin..smin+w-1
%     (here 1..S), 0 meaning fail;
%   - the accepting states as an array;
%   - (n + 1) * Q STATE FLAGS, var bool, introduced here: s[i * Q + q] is "after i
%     letters the automaton is in q".  They are the propagator's own store variables:
%     a state that dies is a flag fixed to 0, a trail entry with a reason like any
%     other, which is how a death reaches the proof without the propagator writing a
%     line (regular.ml's header).  They are not output and never need search: once
%     the letters are fixed the propagator fixes every flag.
%
% The domain restriction is std's (xs[i] in 1..S, "in case it's a var"): it narrows the
% declarations, so the order encoding of a letter is no wider than the alphabet.  The
% empty word is std's case too: accepted iff q0 is final, a par test.
%-----------------------------------------------------------------------------%

predicate baguette_regular(
  array [int] of var int: x,
  int: Q,
  int: smin,
  array [int] of int: d,
  int: q0,
  array [int] of int: F,
  array [int] of var bool: s,
);

predicate fzn_regular(
  array [int] of var int: xs,
  int: Q,
  int: S,
  array [int, int] of int: d,
  int: q0,
  set of int: F,
) =
  if length(xs) = 0 then
    q0 in F
  else
    let {
      array [1..(length(xs) + 1) * Q] of var bool: s;
    } in forall (i in index_set(xs)) (xs[i] in 1..S)
      /\ baguette_regular(array1d(xs), Q, 1, [d[q, v] | q in 1..Q, v in 1..S], q0, [f | f in F], s)
  endif;
