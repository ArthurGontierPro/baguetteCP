%-----------------------------------------------------------------------------%
% baguette solver library -- compat_mzn1.mzn
%
% SHIMS, not features.  Nothing here changes what baguette solves or how a
% constraint is decomposed; every definition below exists only so that a model
% written against MiniZinc 1.x type-checks under 2.10.  MiniZinc Challenge
% archives from 2008-2010 use two constructs the 2.x standard library dropped,
% and every solver that wants to run those archives has to supply them.  We do
% it here rather than patching the corpus, because the corpus is the subject of
% the measurement and must not be edited (M7-T15).
%
% Keep decompositions in redefinitions.mzn.  Keep compatibility here.
%-----------------------------------------------------------------------------%

%-----------------------------------------------------------------------------%
% `is_output'  (16 instances, 2009-2010)
%
%   var int: objective :: is_output = ...;
%   array [1..n, 1..n] of var 0..1: a :: is_output;
%
% In MiniZinc 1.x this annotation marked a declaration as belonging to the
% solution output; the models carrying it have no `output' item and relied on
% it entirely.  2.x replaced it with `add_to_output' (and its `output(x)'
% spelling), which has exactly the 1.x meaning: if ANY declaration carries it,
% only the declarations that carry it are printed.
%
% We CANNOT alias onto it.  Both `ann: is_output = add_to_output;' (a par of
% type ann) and `annotation is_output = add_to_output;' (an annotation with a
% body) were measured on 2.10.1: the first type-checks but is inert -- the
% compiler recognises `add_to_output' by the identifier written at the
% declaration site, not by the value it denotes -- and the second is rejected
% outright, leaving `is_output' undefined.  So a bare declaration is the only
% thing available.
%
% THE DEVIATION THIS LEAVES, stated rather than hidden: with `is_output' inert
% and no `output' item, MiniZinc falls back to its default, which prints EVERY
% top-level variable.  That is a SUPERSET of what the model asked for.  The
% annotated variables are all printed, with correct values, in well-formed
% FlatZinc output format; some unannotated ones are printed alongside them.
% The deviation is in the safe direction -- we never drop a variable the model
% asked for, which is the failure that would be silent.  test/models/
% is_output_shim.fzn pins the solver end of this.
%-----------------------------------------------------------------------------%

annotation is_output;

%-----------------------------------------------------------------------------%
% String-valued search annotations  (8 instances, 2008)
%
%   solve :: int_search(s, "input_order", "indomain_min", "complete") satisfy;
%
% 1.x took the three strategies as strings; 2.x takes them as annotations, so
% the 1.x call has no matching signature and the model is a type error before
% any constraint is seen.  These eight failures are NOT a missing global and
% nothing here is decomposed: the mapping is string -> the identically named
% 2.x annotation, and the search baguette then runs is the one the model asked
% for (M7-T9 supplies smallest/largest/indomain_split; an annotation baguette
% does not implement is its own, separate refusal, downstream of flattening).
%
% An unrecognised string is an assertion failure naming it, not a silent
% fallback to input_order -- a search strategy quietly replaced by a different
% one would make every measurement taken over these instances meaningless.
%
% Only `int_search' is given the 1.x form.  The whole corpus was grepped: no
% `bool_search' or `set_search' call in it uses strings, and a shim with no
% caller is a liability, not a courtesy.
%-----------------------------------------------------------------------------%

function ann: baguette_varsel(string: s) =
  if s = "input_order" then
    input_order
  elseif s = "first_fail" then
    first_fail
  elseif s = "anti_first_fail" then
    anti_first_fail
  elseif s = "smallest" then
    smallest
  elseif s = "largest" then
    largest
  elseif s = "occurrence" then
    occurrence
  elseif s = "most_constrained" then
    most_constrained
  elseif s = "max_regret" then
    max_regret
  elseif s = "dom_w_deg" then
    dom_w_deg
  elseif s = "impact" then
    impact
  else
    assert(
      false,
      "baguette mznlib: unknown MiniZinc 1.x variable selection strategy \"" ++
        s ++
        "\"",
      input_order,
    )
  endif;

function ann: baguette_valsel(string: s) =
  if s = "indomain" then
    indomain
  elseif s = "indomain_min" then
    indomain_min
  elseif s = "indomain_max" then
    indomain_max
  elseif s = "indomain_middle" then
    indomain_middle
  elseif s = "indomain_median" then
    indomain_median
  elseif s = "indomain_random" then
    indomain_random
  elseif s = "indomain_split" then
    indomain_split
  elseif s = "indomain_reverse_split" then
    indomain_reverse_split
  elseif s = "indomain_interval" then
    indomain_interval
  elseif s = "outdomain_min" then
    outdomain_min
  elseif s = "outdomain_max" then
    outdomain_max
  elseif s = "outdomain_median" then
    outdomain_median
  elseif s = "outdomain_random" then
    outdomain_random
  else
    assert(
      false,
      "baguette mznlib: unknown MiniZinc 1.x value choice strategy \"" ++ s ++
        "\"",
      indomain_min,
    )
  endif;

% 1.x's exploration strategies other than "complete" (bbs, lds, credit, ...)
% have no 2.x annotation at all, so they are refused by name rather than
% silently completed.
function ann: baguette_explore(string: s) =
  if s = "complete" then
    complete
  else
    assert(
      false,
      "baguette mznlib: MiniZinc 1.x exploration strategy \"" ++ s ++
        "\" has no MiniZinc 2 equivalent",
      complete,
    )
  endif;

function ann: int_search(
  array [$X] of var int: x,
  string: select,
  string: choice,
  string: explore,
) =
  int_search(
    array1d(x),
    baguette_varsel(select),
    baguette_valsel(choice),
    baguette_explore(explore),
  );

%-----------------------------------------------------------------------------%
% `global_cardinality(x, counts)'  (1 instance, 2008_debruijn_binary)
%
% The two-argument form 1.x carried: the cover is implicit, and is the index
% set of `counts'.  2.x keeps only the three-argument form, so this is a
% SIGNATURE BRIDGE onto the standard library's own predicate -- we spell the
% implicit cover out and hand the call straight to std.
%
% It is therefore not us shattering a global: whatever std decomposes
% `global_cardinality' into, it would have decomposed the 1.x call into as
% well, and baguette has no global_cardinality propagator for the call to be
% kept whole FOR.  That propagator is the better answer and belongs on the
% roadmap; until it exists there is nothing to protect here, and refusing the
% bridge would only keep the instance from reaching the solver at all.
%
% The include is NOT optional and is not decoration. redefinitions.mzn is
% included into EVERY model, so every body in it must type-check in every
% model -- including the models that never mention global_cardinality and
% never include globals.mzn, which is most of them. Without the line below the
% bridge's own body cannot resolve the three-argument predicate and the type
% error is reported against the library, killing twelve instances that have
% nothing to do with cardinality. Measured, not feared: that is exactly what
% the first version of this file did.
%-----------------------------------------------------------------------------%

include "global_cardinality.mzn";

predicate global_cardinality(
  array [$X] of var int: x,
  array [int] of var int: counts,
) =
  global_cardinality(
    array1d(x),
    array1d(index_set(counts), [i | i in index_set(counts)]),
    counts,
  );
