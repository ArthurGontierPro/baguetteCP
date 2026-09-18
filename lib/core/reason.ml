(* Reasons: WHICH FACTS justify a pruning, as declarative data.

   docs/DECISIONS.md D-0026 resolved D-0003 by layering two questions that had been
   answered by one type. This module is the first half; [Explanation] is the second.

     - A *reason* -- which facts justify this pruning -- is declarative data over a
       variable scope, materialised into [Lit.t]s in exactly one place ([lits] below).
       It is not a thunk graph and not a closure per pruning. Laziness lives in *when*
       it is materialised, never in a captured environment.
     - A *justification* -- how the checker is convinced -- stays the reified
       cutting-planes expression in lib/core/explanation.ml: [Combine] with a divisor,
       [Weaken], [Model_row], [Term] recursing. That higher-order content is D-0026's
       (a)-claim and is untouched by this module.

   D-0026's worked example: for `2x + 3y <= 10` with `y >= 2` deriving `x <= 2`, the
   *reason* is the fact `y >= 2`; the *justification* is "add 3 times that fact to the
   row, then divide by 2".

   ---------------------------------------------------------------------------
   Why one fact type covers every propagator in lib/
   ---------------------------------------------------------------------------

   Before this module there were five producers of the [unit -> Lit.t list] thunk that
   [Store.entry] used to carry, and *every literal any of them produced was a bound
   fact*:

     - [Linear.facts_of_snaps]  -- [Lit.ge]/[Lit.le] at a term's current bound, dropped
                                   when that bound is still the declared one;
     - [Ne.fixed_facts]/[moved_bound_fact] -- the same, twice, for a fixed variable;
     - [Bool2int.ge_fact]/[le_fact]        -- the same, with the same drop;
     - [Bool_clause.falsity_fact] -- [Lit.negate] of a clause literal, which for a
                                     `var bool` (declared over [0, 1], D-0007) is
                                     exactly [Lit.le name 0] or [Lit.ge name 1];
     - [Store.no_facts] -- the empty list, i.e. [none] here.

   So there is one shape, [{name; value; decl}] in a direction, and three copies of the
   "drop it at the declared bound" rule collapse into [lit_of_fact]. That rule is not
   cosmetic: at the declared bound the order encoding's statement is the constant true
   (docs/PROOF-FORMAT.md section 3, [Encoding.ge]'s [Holds]), there is no literal to
   name, and a false disjunct in a trace line's tail is not a weakening -- it is a
   wrong line. Having it in one place is the point of "materialised in exactly one
   place"; having it in three was how [Bool_clause] came to carry a comment explaining
   that it is the one that must *not* drop (it never can: a `var bool`'s literal is
   false only because a bound moved).

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
   and a reason must be spellable without holding the store. *)

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
type t = fact list

(* "This change rests on no facts at all."

   Not a default argument anywhere -- that is the whole of what I-P5 collapsing into
   I-P4 buys. [Store.set_lo] used to mean [no_facts] silently and [set_lo_with_facts]
   was the opt-in, which is how [int_ne] pruned factlessly from M1-T9 to M1-T17 and how
   [Store.remove] stayed factless until M1-T17 gave it a sibling. Now there is one
   mutator per bound and a caller with no facts has to write [none] and be seen doing
   it. It is the honest answer in exactly two places: a search decision (nothing derived
   it -- its literal enters the proof negated, in the branch nogood, D-0018/D-0037) and
   a test that is not exercising the proof. *)
let none : t = []
let is_empty (t : t) = t = []
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

let lits (t : t) = List.filter_map lit_of_fact t

(* --------------------------------------------------------------- the scope *)

(* The variable scope: every identifier this reason names, in order, without
   duplicates. Includes the variables whose fact does not materialise, because the
   scope is a property of what the propagator *read*, not of what the encoding happens
   to have a literal for.

   [Store.apply]'s D-0026 agreement check reads this, and M2-T3's conflict analysis is
   meant to walk a reason's variables without materialising a single literal -- which is
   why this is here and not derived from [lits]. *)
let owners (t : t) =
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

(* The value the fact freezes. Added by M2-L0 for the conclusion check in [Store.apply],
   which is the first consumer that needs to compare a fact against a *number* rather
   than only ask which variable and which direction it is about. *)
let fact_value = function At_least { value; _ } | At_most { value; _ } -> value

let fact_to_string = function
  | At_least { name; value; decl } ->
      Printf.sprintf "%s>=%d%s" name value (if value > decl then "" else "[decl]")
  | At_most { name; value; decl } ->
      Printf.sprintf "%s<=%d%s" name value (if value < decl then "" else "[decl]")

let to_string (t : t) =
  match t with [] -> "-" | _ -> String.concat " " (List.map fact_to_string t)

(* --------------------------------------------------------------- the one channel *)

(* What a propagator hands over when it changes a domain: the reason AND the
   justification, together, in one value.

   This is D-0026's "I-P4 and I-P5 collapse into one obligation". They were two:
   I-P4 said every change carries an [Explanation.t] (enforced -- [Store.apply] took
   one positionally), and I-P5 said every bound-moving mutator takes [~facts]
   (unenforced -- the facts were an extra argument on an opt-in sibling function, and
   the plain mutator silently meant [no_facts]). One value carrying both makes the
   second half a type error: there is no mutator that takes a justification alone, and
   [none] has to be written out.

   The two halves are separate *types* rather than one, because they answer D-0026's
   two different questions about the same pruning, and they are one *value* because a
   pruning has exactly one of each and nothing may pair them up later from two places.

   ---------------------------------------------------------------------------
   [concludes]: WHAT this pruning derived -- docs/DECISIONS.md D-0043
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

let because ~concludes reason justification = { reason; justification; concludes }
