(* Reasons: WHICH FACTS justify a pruning, as declarative data.

   A pruning answers two questions, and since D-0026 (which settled D-0003, "what does
   higher-order explanation mean here?") two types answer them. This module is the
   first; [Explanation] is the second.

     - A *reason* -- which facts justify this pruning -- is declarative data over a
       variable scope, materialised into [Lit.t]s in exactly one place ([lits] below).
       It is not a thunk graph and not a closure per pruning. Laziness lives in *when*
       it is materialised, never in a captured environment.
     - A *justification* -- how the checker is convinced -- stays the reified
       cutting-planes expression in lib/core/explanation.ml: [Combine] with a divisor,
       [Weaken], [Model_row], [Term] recursing. That higher-order content is what D-0026
       calls its (a)-claim, and this module does not touch it.

   D-0026's worked example: for `2x + 3y <= 10` with `y >= 2` deriving `x <= 2`, the
   *reason* is the fact `y >= 2`; the *justification* is "add 3 times that fact to the
   row, then divide by 2".

   ---------------------------------------------------------------------------
   Why one fact type covers every propagator in lib/
   ---------------------------------------------------------------------------

   Every literal a reason needs is a BOUND FACT, `x >= v` or `x <= v`, so one shape,
   [{name; value; decl}] in a direction, covers every propagator, and the rule that drops
   a fact at its declared bound lives once, in [lit_of_fact]. The evidence, from before
   this module, when [Store.entry] carried a [unit -> Lit.t list] thunk: its five
   producers all produced bound facts.

     - [Linear.facts_of_snaps]  -- [Lit.ge]/[Lit.le] at a term's current bound, dropped
                                   when that bound is still the declared one;
     - [Ne.fixed_facts]/[moved_bound_fact] -- the same, twice, for a fixed variable;
     - [Bool2int.ge_fact]/[le_fact]        -- the same, with the same drop;
     - [Bool_clause.falsity_fact] -- [Lit.negate] of a clause literal, which for a
                                     `var bool` (declared over [0, 1], D-0007) is
                                     exactly [Lit.le name 0] or [Lit.ge name 1];
     - [Store.no_facts] -- the empty list, i.e. [none] here.

   Three of them carried their own copy of the "drop it at the declared bound" rule. The
   rule is not cosmetic: at the declared bound the order encoding's statement is the
   constant true (docs/PROOF-FORMAT.md section 3, [Encoding.ge]'s [Holds]), there is no
   literal to name, and a false disjunct in a trace line's tail is not a weakening -- it
   is a wrong line. Having it in one place is the point of "materialised in exactly one
   place"; having it in three was how [Bool_clause] came to carry a comment explaining
   that it is the one that must *not* drop (it never can: a `var bool`'s literal is false
   only because a bound moved).

   ---------------------------------------------------------------------------
   Non-narrowable, and what that rules out
   ---------------------------------------------------------------------------

   A fact freezes its [value] at the moment the propagator read it. It is NOT "whatever
   bound this variable has when someone asks", which is GCS's [Narrowable*] shape and
   the exact opposite of invariant I-X6: a reason materialised later must render the
   derivation as of the moment of the pruning, not as of now. There is deliberately no
   constructor here that names a variable without its value, and [lits] takes no store:
   it *cannot* read live state, so the I-X6 obligation on this half is discharged by the
   type rather than by a reviewer noticing. (The [Explanation] half still needs the
   discipline, because a [Deferred] thunk can close over anything; see I-X6 and
   [Linear.snapshot_source].)

   [name] is the FlatZinc identifier, frozen the same way -- nothing renames a variable,
   and a reason must be spellable without holding the store.

   ---------------------------------------------------------------------------
   A reason may be MATERIALISED LATER, from the trail's history (D-0124, M7-T27 (a))
   ---------------------------------------------------------------------------

   [t] has two arms. [Facts] is the list above, built at the push. [Later] is a function
   that builds that same list on demand -- and the discipline that keeps the paragraph
   above true is that the function reads a [Store.history], the trail as it stood at a
   FIXED position (the pruning's own), never the live store. I-T1 freezes every trail
   position below an entry for as long as that entry is on the trail, and
   [Store.check_history] refuses a materialisation after they have been unwound, so a
   [Later] reason renders the derivation as of the moment of the pruning exactly as a
   [Facts] one does, and nothing that may have changed since is readable through it.

   Why it exists: a [Linear] pruning's reason is one fact per OTHER term of its row, and
   on the Challenge rows D-0123 measured when it located the memory wall (4 000 to 8 000
   terms, about two prunings per effective run) building those eagerly held 15 M
   facts and as many snapshot records on the trail after four search nodes, 1.2 GB per
   node. D-0026's "not a closure per pruning" was written against a closure over the LIVE
   store (GCS's [Narrowable*], and I-X6's own failure mode); a closure over a frozen
   history is laziness in WHEN the reason is materialised, which is what D-0026 asked for,
   with the captured environment a snapshot by construction rather than by copying.
   Nothing here memoises: a reason is asked for once by the trace and once per cut by
   analysis, and what a memo would keep is exactly the per-term list this arm exists not
   to keep. [empty] is carried so that [is_empty], which analysis asks per node, stays
   O(1); [Store.check_agreement] checks it against the materialisation under
   BAGUETTE_DEBUG. *)

module Lit = Baguette_proof.Lit

(* One bound a propagator read. [decl] is the variable's *declared* bound in the same
   direction, which is what decides whether the fact has a literal at all. *)
type fact =
  | At_least of { name : string; value : int; decl : int } (* x >= value *)
  | At_most of { name : string; value : int; decl : int }
(* x <= value *)

(* A reason is the facts, in the order the propagator read them. Order is preserved
   through [lits] and no duplicate is dropped: what a trace line's tail contains, and in
   what order, is an artefact this project diffs byte for byte. *)
type t = Facts of fact list | Later of later
and later = { compute : unit -> fact list; empty : bool }

(* How many times a [Later] has been materialised since start-up. It is kept because the
   memo of the decision closure (lib/core/analysis.ml, [dependency_levels], M7-T27 (a3))
   is justified by this count moving; D-0124's addenda first measured it by hand. Read by
   the CLI under --stats and pinned by test_analysis.ml, which asks the same conflict
   twice and requires the second ask not to move it. A process-wide counter and not a
   per-store one, as [Store.history] reads are: a count, not state. *)
let materialisations = ref 0

(* THE one place a stored reason becomes the facts it stands for. A [Later] reads its
   history here and nowhere else, and raises ([Store.check_history]) if that history has
   been unwound. *)
let facts = function
  | Facts l -> l
  | Later l ->
      incr materialisations;
      l.compute ()

let of_facts l = Facts l

(* "This change rests on no facts at all."

   Never a default argument: there is one mutator per bound, and a caller with no facts
   writes [none] and is seen doing it. That is what folding I-P5 (every bound move
   carries the facts its trace line negates) into I-P4 (every change carries an
   explanation) buys. When [Store.set_lo] meant "no facts" silently and
   [set_lo_with_facts] was the opt-in, [int_ne] pruned factlessly from M1-T9 to M1-T17.
   [none] is the honest answer in exactly two places: a search decision (nothing derived
   it -- its literal enters the proof negated, in the branch nogood, D-0018/D-0037) and
   a test that is not exercising the proof. *)
let none : fact list = []
let is_empty = function Facts l -> l = [] | Later l -> l.empty
let at_least ~name ~decl value = At_least { name; value; decl }
let at_most ~name ~decl value = At_most { name; value; decl }

(* [x >= value] and [x <= value] together: a variable fixed at [value]. Negated by
   [Trace] they are [Encoding.ne_clause_lits]'s two halves, i.e. "x <> value". *)
let fixed_at ~name ~decl_lo ~decl_hi value =
  [ at_least ~name ~decl:decl_lo value; at_most ~name ~decl:decl_hi value ]

(* The fact that the *bound relevant to a coefficient's sign* currently sits where it
   does: [coeff >= 0] reads lo and states [x >= value], [coeff < 0] reads hi and states
   [x <= value]. This is D-0013's own case split, shared by every linear-shaped
   propagator so that the reason and the row's arithmetic cannot disagree about which
   bound was read. *)
let bound_for_coeff ~coeff ~name ~decl_lo ~decl_hi value =
  if coeff >= 0 then at_least ~name ~decl:decl_lo value
  else at_most ~name ~decl:decl_hi value

(* --------------------------------------------------------------- materialisation *)

(* THE one place a reason becomes literals.

   [None] is "this fact has no literal": the bound is still the declared one, so the
   encoding states it as the constant true. Every caller that used to make this test for
   itself is now a caller of this function. *)
let lit_of_fact = function
  | At_least { name; value; decl } ->
      if value > decl then Some (Lit.ge name value) else None
  | At_most { name; value; decl } ->
      if value < decl then Some (Lit.le name value) else None

let lits_of_facts (l : fact list) = List.filter_map lit_of_fact l
let lits r = lits_of_facts (facts r)

(* --------------------------------------------------------------- the scope *)

(* The variable scope: every identifier this reason names, in order, without
   duplicates. Includes the variables whose fact does not materialise, because the
   scope is a property of what the propagator *read*, not of what the encoding happens
   to have a literal for.

   [Store.apply]'s agreement check (the two halves of D-0026 must name the same variables)
   reads this, and conflict analysis walks a reason's variables without materialising a
   single literal -- which is why this is here and not derived from [lits]. *)
let owners r =
  let t = facts r in
  let seen = Hashtbl.create 8 in
  List.filter_map
    (fun f ->
      let n = match f with At_least { name; _ } | At_most { name; _ } -> name in
      if Hashtbl.mem seen n then None
      else (
        Hashtbl.add seen n ();
        Some n))
    t

(* Per-fact accessors, for the agreement check: which variable, and which of its two
   bounds. Kept here rather than pattern-matched at the call site so that a third
   direction, if one is ever added, is a compile error in one place. *)
let fact_owner = function At_least { name; _ } | At_most { name; _ } -> name
let fact_is_lower = function At_least _ -> true | At_most _ -> false

(* The value the fact freezes. The conclusion check in [Store.apply] reads it, the one
   consumer that compares a fact against a *number* rather than only asking which
   variable and which direction it is about (M2-L0). *)
let fact_value = function At_least { value; _ } | At_most { value; _ } -> value

let fact_to_string = function
  | At_least { name; value; decl } ->
      Printf.sprintf "%s>=%d%s" name value (if value > decl then "" else "[decl]")
  | At_most { name; value; decl } ->
      Printf.sprintf "%s<=%d%s" name value (if value < decl then "" else "[decl]")

let to_string_facts (t : fact list) =
  match t with [] -> "-" | _ -> String.concat " " (List.map fact_to_string t)

let to_string r = to_string_facts (facts r)

(* --------------------------------------------------------------- the one channel *)

(* What a propagator hands over when it changes a domain: the reason AND the
   justification, together, in one value.

   One value carrying both makes a pruning without its facts a type error: there is no
   mutator that takes a justification alone, and [none] has to be written out. This is
   D-0026's "I-P4 and I-P5 collapse into one obligation". They were two: I-P4, every
   change carries an [Explanation.t], was enforced ([Store.apply] took one
   positionally); I-P5, every bound-moving mutator takes [~facts], was not (the facts
   were an extra argument on an opt-in sibling function, and the plain mutator silently
   meant [no_facts]).

   The two halves are separate *types* rather than one, because they answer D-0026's
   two different questions about the same pruning, and they are one *value* because a
   pruning has exactly one of each and nothing may pair them up later from two places.

   ---------------------------------------------------------------------------
   [concludes]: WHAT this pruning derived (D-0043)
   ---------------------------------------------------------------------------

   The third field answers the question the other two do not. [reason] says which facts
   were read and [justification] says how the checker is convinced, but neither says
   *what was derived*: an [Explanation.Combine] records a derivation whose content the
   checker recomputes, so a [pol] truncated to derive something strictly weaker than the
   bound the propagator actually set is accepted, silently (M1-T51 measured exactly
   that). [concludes] is that missing claim, and it is a [fact] because a bound claim is
   already this module's vocabulary -- D-0043 chose [reason.ml] over [explanation.ml] for
   that reason and so that no new [Explanation] constructor is spent on it.

   THE SPELLING, and why it is this one:

     - a **required record field** carrying an **optional value**, not an optional
       labelled argument with a default. [none] above is the precedent and the argument
       is the same one: a defaulted [?concludes] would let a pruning silently conclude
       nothing, which is [set_lo] silently meaning [no_facts] all over again -- the exact
       shape D-0026 removed when I-P5 collapsed into I-P4. A caller that concludes
       nothing writes [~concludes:None] and is seen doing it. It cost 13 call sites in
       [lib/] and 46 in [test/], which is the price of the property.

       THE COST IS THE PROPERTY, so relaxing this into a defaulted [?concludes] NEEDS A
       DECISION RECORD ARGUING THE POINT, not a cleanup commit. It will look like
       ceremony -- 59 call sites writing out a value most of them could have inferred --
       and it is the move D-0026 already reversed once, when a default that meant "no
       facts" turned into prunings that justified nothing. A default here would mean "no
       claim", and M1-T51 measured what an unstated claim costs: a [pol] truncated to
       derive something strictly weaker than the bound the propagator set is ACCEPTED,
       silently.
     - a [fact option] and not a [fact], because the [None] is principled rather than a
       coverage gap, and the partition is one the solver already draws:

         * a **pruning that moved a bound** concludes that bound -- [Some];
         * a **decision** concludes nothing ([None]): D-0037 settled that a decision is
           an assumption and not a derived bound, and nothing in the proof establishes
           it ([Justify.emit] refuses one outright). [Store.apply] enforces this
           direction rather than trusting it;
         * a **conflict** concludes falsity, not a bound -- [None]. It has no trail entry
           and no claim clause; its line is the nogood;
         * a **value removal** that punches an interior hole concludes `x <> v`, which is
           a two-literal clause over the order encoding ([Trace.hole_clause]) and NOT a
           bound fact -- [None]. This is the one [None] that is about the *type* rather
           than about the solver's own split, and it is stated here so that a reader
           does not take it for an omission: making it [Some] would need a disequality
           constructor, i.e. a decision record of its own.

   Where the value comes from: the bound the propagator is about to hand the store
   mutator, with the same [decl] it would use for a reason fact in that direction.
   [Store.apply] checks that agreement exactly -- same variable, same direction, same
   number -- which is what D-0043 says replaces M2-T8's looser "...or the fact has a
   support" arm for the conclusion half. *)
type justified = { reason : t; justification : Explanation.t; concludes : fact option }

let because ~concludes reason justification =
  { reason = Facts reason; justification; concludes }

(* The same channel with the reason's facts built on demand (D-0124, see the header's
   "materialised later"). [compute] must read
   a [Store.history] taken at the push and nothing live (see the module header); [empty]
   must equal [compute () = []], which [Store.check_agreement] asserts under
   BAGUETTE_DEBUG. [~empty] is required rather than defaulted for the reason [~concludes]
   is: a caller states what it knows and is seen doing it. *)
let because_later ~concludes ~empty compute justification =
  { reason = Later { compute; empty }; justification; concludes }
