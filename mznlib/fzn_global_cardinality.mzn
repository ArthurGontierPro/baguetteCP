%-----------------------------------------------------------------------------%
% global_cardinality stays whole when its counts are fixed (variable counts go to
% std's decomposition since D-0247, see the second header below).
%
% std/fzn_global_cardinality.mzn decomposes to one reified equality per variable
% per cover value, channelled to 0/1 and summed against the count.  That throws
% away lib/core/prop/gcc.ml, and what it throws away is not a constant factor:
% the decomposition's rows are ONE PER VALUE, and gcc's interval-capacity rule
% is a sum ACROSS values.  No amount of propagation over the per-value rows
% separately reaches an inference that no single one of them mentions.  D-0078
% measures both sides.
%
% M7-T15 (D-0076) bridged MiniZinc 1.x's two-argument spelling onto the
% three-argument predicate and let std decompose it, and said in as many words
% why that was right AT THE TIME: baguette had no propagator for the call to be
% kept whole for.  It has one now, and compat_mzn1.mzn's bridge therefore lands
% here instead -- the same bridge, a different destination.
%
% The bodyless declaration is what makes MiniZinc emit the call verbatim.  Note
% that it is the fzn_ name that is declared, not the globals.mzn one: std's
% global_cardinality reaches fzn_global_cardinality itself, so shadowing the
% inner predicate keeps the outer one's argument handling (cover as an array of
% par int, the open form) exactly as std defines it.
%
% THE COUNTS NEED A DECLARED DOMAIN, and that is why this file has a body at all.
%
% std's `global_cardinality' takes `array [int] of var int: counts', and a model that
% passes it a freshly introduced array gets variables with NO domain.  Under the
% decomposition that did not matter: the `sum(bool2int(...)) = counts[i]' rows let
% MiniZinc infer 0..length(x) and the declaration came out bounded.  Keep the global
% whole and those rows are gone, so the count arrives at the front end as `var int' and
% is REFUSED -- docs/SPEC.md 2.1 requires a finite declared domain, and that refusal is
% right.  MEASURED on 2008_debruijn_binary, which is the instance this whole bridge
% exists for.
%
% So `fzn_global_cardinality' states the bound the decomposition used to imply and hands
% the constraint to `baguette_global_cardinality', which is the bodyless one.  The bounds
% are not a heuristic: a tally over |x| variables is between 0 and |x| by definition, so
% nothing is lost and nothing is assumed.  Since D-0247 only fixed counts reach that
% call, where the bounds are a par check; variable counts get their bounds again from
% std's count rows.
%
% THE FRONT END REFUSES two shapes rather than mis-counting them, each with a
% source position (lib/flatzinc/compile.ml's post_global_cardinality says why): a
% cover and counts of different lengths, and the same variable twice in the array.
% The second is a guard: Builder.split_gcc_repeats replaces every repeat by a copy
% tied with int_eq before compile.ml sees the model (M7-T29, D-0146).  A count that
% is a literal constant was a third refusal until M7-T18 made it the count VIEW
% (D-0082).

% VARIABLE COUNTS GO TO STD'S DECOMPOSITION (M18-coverage-T14, D-0247 [AUTONOME]).
%
% When some count is a variable, this file now hands the call to std's own
% decomposition (one `count' per cover value, plus std's implied row
% length(x) >= sum(counts)), and keeps lib/core/prop/gcc.ml for the calls whose
% counts are all fixed. Measured over the 40 Challenge instances (2014-2026 lists,
% flattened by MiniZinc 2.10.1) that reach this branch, 300 s: with proof three more
% complete and verified (mondoku 10-10-6 and 12-12-8, and oocsp_racks 100_r1 whose
% check now ends), 11 wins and 3 losses against main by the Challenge order;
% without proof two more complete, 15 wins and 1 loss. No complete answer is lost.
% What the native propagator misses with variable counts is the propagation BETWEEN
% counts: the implied row alone closes mondoku (D-0247 section 3), and on warehouse
% and peaceable queens the per-value rows are also cheaper per node than gcc's
% interval rule over 3 000 variables. Native plus the rows was measured too: it
% completes the same instances and scores below this route (1 win, 14 losses).
%
% The closed forms stay native (fzn_global_cardinality_closed.mzn calls the bodyless
% predicate itself): they already state sum(counts) = |x|, the row that decides
% mondoku, and blocks-world, the one Challenge family that uses them, did not move.
% global_cardinality_low_up's counts are declared on constant bounds and stay native
% too; that route was not measured (D-0247 section 6).
%
% To revert: restore the body below to its first two lines (the bounds and the
% baguette_global_cardinality call) for every call.
%-----------------------------------------------------------------------------%

include "count.mzn";

predicate baguette_global_cardinality(
  array [int] of var int: x,
  array [int] of int: cover,
  array [int] of var int: counts,
);

predicate fzn_global_cardinality(
  array [int] of var int: x,
  array [int] of int: cover,
  array [int] of var int: counts,
) =
  if forall (i in index_set(counts)) (is_fixed(counts[i])) then
    forall (i in index_set(counts)) (counts[i] >= 0 /\ counts[i] <= length(x))
    /\ baguette_global_cardinality(x, cover, counts)
  else
    forall (i in index_set(cover)) (count(x, cover[i], counts[i]))
    /\ length(x) >= sum(counts)
  endif;
