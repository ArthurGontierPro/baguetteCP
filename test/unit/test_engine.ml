(* Unit tests for the propagation engine (lib/core/engine.ml) and depth-first search
   with a proof (lib/core/search.ml) -- M1-T10.

   Follows test_justify.ml's shape: cheap unit checks, plus real invocations of veripb
   for the tests that matter (I-X1: every emitted rule is accepted by VeriPB). Tests 1
   through 3 exercise the solver side directly against [Store]/[Engine]/[Search]; test
   4 is the one the task calls out as the one that matters -- a real search, both SAT
   and UNSAT, each forced to backtrack at least once, checked end to end by the real
   checker. Test 5 checks the proof-audit invariant (I-X2). *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Explanation = Baguette_core.Explanation
module Reason = Baguette_core.Reason
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Ne = Baguette_core.Ne
module Engine = Baguette_core.Engine
module Justify = Baguette_core.Justify
module Search = Baguette_core.Search
module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

(* M1-T53: the inner heap guard; see mem_guard.ml for what it cannot see. *)
let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* ------------------------------------------------------------------- helpers *)

let mk_store bounds =
  let names = Array.of_list (List.map (fun (n, _, _) -> n) bounds) in
  let domains = Array.of_list (List.map (fun (_, lo, hi) -> Domain.make lo hi) bounds) in
  Store.create ~names ~domains

let var i = Var.of_int i

let pack_linear id (lin : Linear.t) : Propagator.instance =
  Propagator.pack ~id (module Linear : Propagator.S with type t = Linear.t) lin

let pack_ne id (ne : Ne.t) : Propagator.instance =
  Propagator.pack ~id (module Ne : Propagator.S with type t = Ne.t) ne

(* M1-T31 made [Linear.make]'s [~row_id] required, and the propagation-only tests
   below build no encoding, open no writer and render no explanation -- there is no
   .opb for a row id to be an id *of*. [unrendered_row ()] says exactly that, rather
   than threading a plausible-looking id through a test that would never look at it:
   the values are distinct so that two instances in one test stay two instances
   (D-0011), and if one of these tests ever did emit a proof it would cite an id the
   .opb does not have and be rejected, which is the right way round. The scenes that
   DO emit a proof ([sat_scene]/[unsat_scene]) use the encoding's own ids. *)
let next_unrendered_row = ref 900

let unrendered_row () =
  incr next_unrendered_row;
  !next_unrendered_row

(* ===================================================================== *)
(* 1. Engine fixpoint (I-P2), and that a conflict returns a usable        *)
(*    explanation.                                                       *)
(* ===================================================================== *)

(* x1 in [0,5], x2 in [3,5], x1 + x2 <= 3: propagation must tighten x1's hi to 0
   (the only way the row can hold once x2 >= 3). *)
let test_fixpoint_tightens_and_settles () =
  let store = mk_store [ ("x1", 0, 5); ("x2", 3, 5) ] in
  let lin = Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 3 in
  let engine = Engine.create [ pack_linear 0 lin ] in
  (match Engine.propagate engine store with
  | Engine.Conflict _ ->
      incr failures;
      Printf.printf "FAIL fixpoint: unexpected conflict\n"
  | Engine.Fixpoint ->
      check "fixpoint: x1's hi is tightened to 0" (Domain.hi (Store.get store (var 0)) = 0));
  (* I-P2, tested directly: propagating again from the same fixpoint changes nothing. *)
  let trail_before = Store.trail_length store in
  (match Engine.propagate engine store with
  | Engine.Conflict _ ->
      incr failures;
      Printf.printf "FAIL fixpoint: second propagate call conflicted\n"
  | Engine.Fixpoint -> ());
  check "I-P2: propagating again at a fixpoint changes nothing"
    (Store.trail_length store = trail_before)

(* x1, x2 declared [0,5] (so D-0010's chain is non-trivial: x2's lower bound of 4 is
   not the *declared* bound, it is a pruning this test applies by hand, exactly
   test_justify.ml's [setup_int_lin_le] pattern), x1 + x2 <= 3: infeasible once x2 is
   pushed to >= 4, a conflict carrying a usable (forceable) explanation whose chain
   actually mentions the literals that witness x2's bound. *)
let test_conflict_carries_explanation () =
  let store = mk_store [ ("x1", 0, 5); ("x2", 0, 5) ] in
  let lin = Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 3 in
  (match
     Store.set_lo store (var 1) 4
       (Reason.because ~concludes:None Reason.none (Explanation.model_row 1))
   with
  | Store.Conflict _ -> failwith "test_conflict_carries_explanation: setup failed"
  | Store.Changed | Store.Unchanged -> ());
  let engine = Engine.create [ pack_linear 0 lin ] in
  match Engine.propagate engine store with
  | Engine.Fixpoint ->
      incr failures;
      Printf.printf "FAIL conflict: expected Conflict, got Fixpoint\n"
  | Engine.Conflict c ->
      let forced = Explanation.force c.Store.c_why in
      check "conflict: explanation forces without raising"
        (match forced with Explanation.Deferred _ -> false | _ -> true);
      check "conflict: explanation mentions the literals witnessing the pruned bound"
        (Explanation.lits forced <> [])

(* Only watchers of a changed variable are woken: two independent constraints over
   disjoint variables, propagating one must not need to re-run the other to reach a
   quiescent fixpoint (I-P2 again, from the other side -- nothing is left to say
   after the first pass either way, whether or not the watch table filters). This
   mainly guards against "propagate everyone every round" silently still being
   correct but doing needless work; the trail length settling either way is the part
   that has to hold regardless, so that is what is checked. *)
let test_independent_constraints_reach_fixpoint () =
  let store = mk_store [ ("x1", 0, 5); ("x2", 3, 5); ("y1", 0, 5); ("y2", 3, 5) ] in
  let lin_x =
    Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 3
  in
  let lin_y =
    Linear.make ~row_id:(unrendered_row ()) store [ (1, var 2); (1, var 3) ] 3
  in
  let engine = Engine.create [ pack_linear 0 lin_x; pack_linear 1 lin_y ] in
  (match Engine.propagate engine store with
  | Engine.Conflict _ ->
      incr failures;
      Printf.printf "FAIL independent: unexpected conflict\n"
  | Engine.Fixpoint ->
      check "independent: x1 tightened" (Domain.hi (Store.get store (var 0)) = 0);
      check "independent: y1 tightened" (Domain.hi (Store.get store (var 2)) = 0));
  let trail_before = Store.trail_length store in
  ignore (Engine.propagate engine store);
  check "independent: settled, no further changes on re-propagation"
    (Store.trail_length store = trail_before)

(* ===================================================================== *)
(* 1c. M2-T7: the trail names the propagator that made each change, and  *)
(*     the engine reads that stamp back.                                 *)
(*                                                                       *)
(* These exist because an id that is threaded but never read changes no   *)
(* behaviour at all, and this codebase's signature failure is a check     *)
(* that cannot see its own subject fail (M1-T45's dead `if true || ...`,  *)
(* M1-T50's deliberately wrong decision literal). So two of the four      *)
(* tests below PERFORM the mis-attribution rather than reasoning about    *)
(* it: one propagator claims another's id, one prunes a variable it never *)
(* declared, and each must be refused.                                   *)
(* ===================================================================== *)

(* Two rows over disjoint variables, each with one variable already fixed by its
   declaration so that each row has exactly one pruning to make. The trail then has one
   entry per instance and every entry must name its own. *)
let test_attribution_names_the_right_instance () =
  let store = mk_store [ ("x1", 0, 5); ("x2", 3, 3); ("y1", 0, 5); ("y2", 3, 3) ] in
  let row_x =
    Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 3
  in
  let row_y =
    Linear.make ~row_id:(unrendered_row ()) store [ (1, var 2); (1, var 3) ] 3
  in
  let engine = Engine.create [ pack_linear 0 row_x; pack_linear 1 row_y ] in
  (match Engine.propagate engine store with
  | Engine.Conflict _ -> failwith "attribution: unexpected conflict"
  | Engine.Fixpoint -> ());
  check "attribution: both rows pruned, so there is something to attribute"
    (Store.trail_length store = 2);
  let owner name =
    let found = ref None in
    for i = 0 to Store.trail_length store - 1 do
      let e = Store.trail_entry store i in
      if Store.name store e.Store.var = name then found := Some e.Store.prop
    done;
    !found
  in
  check "attribution: x1's pruning names the instance holding x1's row"
    (owner "x1" = Some 0);
  check "attribution: y1's pruning names the instance holding y1's row"
    (owner "y1" = Some 1);
  (* The check that would still pass if [prop] were a constant: it must not. *)
  check "attribution: the two prunings are attributed differently"
    (owner "x1" <> owner "y1")

(* A conflict is where M2-T3's resolution starts, so it must name its constraint too.
   Instance 0 is a row with nothing to say, so the conflict comes from instance 1 and a
   stamp of "whoever ran first" or a hardcoded 0 would be visible here. *)
let test_conflict_names_its_propagator () =
  let store = mk_store [ ("z", 0, 5); ("x1", 0, 5); ("x2", 0, 5) ] in
  let quiet = Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0) ] 5 in
  let doomed =
    Linear.make ~row_id:(unrendered_row ()) store [ (1, var 1); (1, var 2) ] 3
  in
  (match
     Store.set_lo store (var 2) 4
       (Reason.because ~concludes:None Reason.none (Explanation.model_row 1))
   with
  | Store.Conflict _ -> failwith "conflict-id: setup failed"
  | Store.Changed | Store.Unchanged -> ());
  let engine = Engine.create [ pack_linear 0 quiet; pack_linear 1 doomed ] in
  match Engine.propagate engine store with
  | Engine.Fixpoint ->
      incr failures;
      Printf.printf "FAIL conflict-id: expected a Conflict\n"
  | Engine.Conflict c ->
      check "conflict: the conflict names the instance that reported it"
        (c.Store.c_prop = 1);
      check "conflict: and still carries its explanation"
        (Explanation.lits (Explanation.force c.Store.c_why) <> [])

(* THE BREAK, performed rather than argued: a propagator that does the real work of a
   linear row while claiming, through [Store.with_running], to be a different instance.
   [Store.with_running] is public -- the engine needs it -- so this back door exists, and
   the whole value of [Engine.check_attribution] is that walking through it is refused
   instead of yielding a trail that credits instance 1 with instance 0's pruning.
   Without that check this scene answers correctly, verifies, and says nothing at all. *)
module Steals_credit = struct
  type t = Linear.t

  let name = "steals_credit"
  let consistency = Propagator.Bounds
  let vars t = Linear.vars t
  let propagate t store = Store.with_running store 1 (fun () -> Linear.propagate t store)
end

let contains msg needle =
  let n = String.length needle and m = String.length msg in
  let rec at i = i + n <= m && (String.sub msg i n = needle || at (i + 1)) in
  at 0

let test_stolen_credit_is_refused () =
  let store = mk_store [ ("x1", 0, 5); ("x2", 3, 3) ] in
  let lin = Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 3 in
  let thief =
    Propagator.pack ~id:0
      (module Steals_credit : Propagator.S with type t = Steals_credit.t)
      lin
  in
  let other =
    pack_linear 1 (Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0) ] 5)
  in
  let engine = Engine.create [ thief; other ] in
  let caught =
    match Engine.propagate engine store with
    | _ -> None
    | exception Engine.Mis_attributed msg -> Some msg
  in
  check "M2-T7: a prune attributed to another instance is refused" (Option.is_some caught);
  check "M2-T7: and the refusal names the variable whose attribution is wrong"
    (match caught with Some msg -> contains msg "x1" | None -> false)

(* The second arm: a stamp that IS the running instance's own id, but on a variable that
   instance never declared. That is not a threading bug, it is a scope bug -- I-P1's
   soundness is stated about a propagator's OWN constraint, so a prune outside its
   declared variables has no I-P1 to appeal to, and the variable would also be starved of
   wakes (M2-T5). [vars] under-reports here in the most ordinary way there is: a row
   whose second variable was forgotten. *)
module Under_declared = struct
  type t = Linear.t

  let name = "under_declared"
  let consistency = Propagator.Bounds

  (* Deliberately WRONG: the row is over x1 and x2 and prunes x1, but only x2 is
     declared. *)
  let vars t = match Linear.vars t with [] -> [] | _ :: rest -> rest
  let propagate t store = Linear.propagate t store
end

let test_undeclared_variable_is_refused () =
  let store = mk_store [ ("x1", 0, 5); ("x2", 3, 3) ] in
  let lin = Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 3 in
  let inst =
    Propagator.pack ~id:0
      (module Under_declared : Propagator.S with type t = Under_declared.t)
      lin
  in
  let engine = Engine.create [ inst ] in
  let caught =
    match Engine.propagate engine store with
    | _ -> false
    | exception Engine.Mis_attributed _ -> true
  in
  check "M2-T7: a prune of an undeclared variable is refused" caught

(* ===================================================================== *)
(* 1b. M1-T24: the trail-cursor walk wakes watchers in exactly the order  *)
(*     the old whole-trail walk did.                                     *)
(*                                                                       *)
(* [Engine.watchers_of_new_entries] used to call [Store.trail_entries],   *)
(* which builds the entire trail as a fresh newest-first list, and then   *)
(* kept only its first [trail_length - since] elements. It now walks the  *)
(* positions [since .. trail_length - 1] by index via [Store.trail_entry] *)
(* instead, allocating nothing proportional to the whole trail.           *)
(*                                                                       *)
(* The *set* of woken propagators is the part correctness needs, but the  *)
(* ORDER is what [propagate] enqueues in, and the enqueue order fixes the *)
(* propagation order, which fixes the search tree, which fixes the        *)
(* emitted proof text. So "same set" is not good enough to call this a    *)
(* pure perf change: the order has to be identical too. Rather than argue *)
(* that from the code, [reference_watchers] below is the OLD algorithm    *)
(* written out verbatim, and the test asserts the two lists are equal --  *)
(* so if anyone later "simplifies" the walk into the natural oldest-first *)
(* direction (which reverses the result), this goes red and says so.      *)
(* ===================================================================== *)

(* The pre-M1-T24 implementation, kept here as the oracle. Do not "tidy" this into
   the new one; its whole job is to be the independent second opinion. *)
let reference_watchers (t : Engine.t) store ~since =
  let len = Store.trail_length store in
  let n_new = len - since in
  if n_new <= 0 then []
  else
    let entries = Store.trail_entries store in
    let acc = ref [] in
    List.iteri
      (fun i (e : Store.entry) ->
        if i < n_new then
          match Hashtbl.find_opt t.Engine.watchers e.var with
          | None -> ()
          | Some ids -> acc := List.rev_append ids !acc)
      entries;
    !acc

let test_wake_order_is_unchanged () =
  let store =
    mk_store [ ("x0", 0, 100); ("x1", 0, 100); ("x2", 0, 100); ("x3", 0, 100) ]
  in
  (* Overlapping pairs, so the interesting variables carry several watchers each and a
     per-entry ordering is actually observable: x0 -> {0,2}, x1 -> {0,1},
     x2 -> {1,2,3}, x3 -> {3}. The rows are slack (each variable is <= 100 and the
     bound is 500), so nothing here prunes -- this test is about the wake-up
     bookkeeping, not about propagation. *)
  let row a b =
    Linear.make ~row_id:(unrendered_row ()) store [ (1, var a); (1, var b) ] 500
  in
  let engine =
    Engine.create
      [
        pack_linear 0 (row 0 1);
        pack_linear 1 (row 1 2);
        pack_linear 2 (row 0 2);
        pack_linear 3 (row 2 3);
      ]
  in
  let bump v n =
    match
      Store.set_lo store (var v) n
        (Reason.because ~concludes:None Reason.none (Explanation.model_row 1))
    with
    | Store.Conflict _ -> failwith "wake order: setup conflicted"
    | Store.Changed | Store.Unchanged -> ()
  in
  let since_empty = Store.trail_length store in
  check "wake order: nothing pushed since the cursor wakes nobody"
    (Engine.watchers_of_new_entries engine store ~since:since_empty = []);
  bump 2 5;
  bump 0 7;
  (* A cursor part-way along the trail, which is the only case [propagate] ever uses:
     entries below [since] must not be looked at, and the walk must not start at 0. *)
  let since_mid = Store.trail_length store in
  bump 1 9;
  bump 2 11;
  bump 3 13;
  let got_mid = Engine.watchers_of_new_entries engine store ~since:since_mid in
  let got_all = Engine.watchers_of_new_entries engine store ~since:since_empty in
  check "wake order: a mid-trail cursor reproduces the old walk exactly"
    (got_mid = reference_watchers engine store ~since:since_mid);
  check "wake order: a from-zero cursor reproduces the old walk exactly"
    (got_all = reference_watchers engine store ~since:since_empty);
  (* Guard against the above passing vacuously: both walks returning [] would satisfy
     equality while testing nothing. This is the project's recurring failure mode (see
     WORKLOG: "the instance chosen to test a thing could not see the thing break"). *)
  check "wake order: the mid-trail walk actually woke somebody" (got_mid <> []);
  check "wake order: the mid-trail cursor is a strict suffix, not the whole trail"
    (List.length got_mid < List.length got_all);
  (* And the direction really is observable on this instance: were the walk to run
     oldest-first instead, the answer would be the reverse of this one. If that ever
     stops being true the test above has gone blind. *)
  check "wake order: this instance can see a reversed walk" (got_all <> List.rev got_all)

(* ===================================================================== *)
(* 1c. M2-T5: trigger masking, and the I-P2 re-run check that is the      *)
(*     only instrument able to tell a safe mask from an unsafe one.       *)
(*                                                                       *)
(* The hazard, stated once: an over-aggressive mask starves a propagator  *)
(* of a wake it needed. Nothing raises. The proof still verifies, because *)
(* every line that WAS written was derived correctly -- the missing       *)
(* pruning simply has no line. The search just prunes less, and in the    *)
(* worst case prints an assignment violating a constraint nobody woke to  *)
(* check. So "the 29 models still pass" is not evidence about the mask;   *)
(* it is evidence that those 29 models do not depend on the wakes it      *)
(* removes. (They do not. Measured: across the whole model suite the mask *)
(* drops ZERO wakes, because no model ever punches an interior hole.)     *)
(*                                                                       *)
(* What IS evidence is I-P2: at a real fixpoint no propagator has         *)
(* anything left to say, so a starved propagator shows up as one that     *)
(* still prunes when re-run. The scenes below are built so that the       *)
(* engine's mask is wrong on purpose in one of them, and assert that      *)
(* [Engine.check_fixpoint] catches exactly that -- with the matching      *)
(* correctly-masked scene next to it, so a check that raised on           *)
(* everything would not pass either.                                     *)
(* ===================================================================== *)

(* Two test-local propagators. They are here rather than taken from lib/core/prop/
   because the tree has no hole-sensitive propagator yet: [linear] and [bool2int] read
   only [Domain.lo]/[Domain.hi], [bool_clause] lives on 0/1 variables where interior
   holes cannot exist, and [ne] prunes off fixedness. That absence is precisely why the
   model suite cannot exercise this mask, and precisely why the scene has to be built
   here. [Eq_dom] is a fair stand-in: domain-consistent equality is an ordinary
   propagator and reads exactly what [all_different] and [element] will read in M4.

   Both prune with a placeholder [Model_row] justification and [Reason.none]. Since
   M2-T8 (D-0026) that is one value and the empty reason is written out rather than
   defaulted, which is what makes it *visible* that these two do not record what they
   read. It is fine only because nothing here writes a proof (see I-P5: a bound-moving
   prune with an empty reason would write a trace line with an empty tail, an
   unconditional claim). No [Engine] test below emits proof rules from these two. *)

let no_facts_placeholder =
  Reason.because ~concludes:None Reason.none (Explanation.model_row 1)

module Punch = struct
  type t = { px : Var.t; pv : int }

  let name = "punch"

  (* [Value]: it names the value it removes and claims nothing about the rest. Keeps
     [wake_on_any], which is what we want -- the mask under test is the OTHER one's. *)
  let consistency = Propagator.Value
  let vars p = [ p.px ]

  let propagate p store =
    match Store.remove store p.px p.pv no_facts_placeholder with
    | Store.Conflict e -> Propagator.Conflict e
    | Store.Changed | Store.Unchanged -> Propagator.Fixpoint
end

module Eq_dom = struct
  type t = { ex : Var.t; ey : Var.t }

  let name = "eq_dom"

  (* Domain consistent, and genuinely hole-reading: it consults [Domain.mem] on one
     variable for every value of the other. A hole punched in the middle of [ex] must
     be mirrored into [ey], which is a pruning no bounds reasoning can find. *)
  let consistency = Propagator.Domain
  let vars p = [ p.ex; p.ey ]

  (* Remove from [b] every value absent from [a]. The list is materialised before the
     removals so the iteration is not walking a domain being mutated under it. *)
  let mirror store a b =
    let da = Store.get store a in
    let gone =
      List.filter (fun v -> not (Domain.mem da v)) (Domain.to_list (Store.get store b))
    in
    List.fold_left
      (fun acc v ->
        match acc with
        | Propagator.Conflict _ -> acc
        | Propagator.Fixpoint -> (
            match Store.remove store b v no_facts_placeholder with
            | Store.Conflict e -> Propagator.Conflict e
            | Store.Changed | Store.Unchanged -> Propagator.Fixpoint))
      Propagator.Fixpoint gone

  let propagate p store =
    match mirror store p.ex p.ey with
    | Propagator.Conflict e -> Propagator.Conflict e
    | Propagator.Fixpoint -> mirror store p.ey p.ex
end

let pack_punch id p =
  Propagator.pack ~id (module Punch : Propagator.S with type t = Punch.t) p

let pack_eq_dom id p =
  Propagator.pack ~id (module Eq_dom : Propagator.S with type t = Eq_dom.t) p

(* x, y in 0..4 with x = y (domain consistent), and a propagator that removes the value
   2 from x -- an INTERIOR removal, so a [Domain.Holes] change that moves no bound.
   [Eq_dom] is instance 0 so that it runs before [Punch] on the seeding pass and can
   only learn about the hole by being woken by it. Domains are five values wide: this
   machine is shared and no test here needs a wide domain. *)
let hole_scene ?trigger () =
  let store = mk_store [ ("x", 0, 4); ("y", 0, 4) ] in
  let insts =
    [
      pack_eq_dom 0 { Eq_dom.ex = var 0; ey = var 1 };
      pack_punch 1 { Punch.px = var 0; pv = 2 };
    ]
  in
  (store, Engine.create ?trigger insts)

let raises_not_at_fixpoint engine store =
  match Engine.check_fixpoint engine store with
  | () -> None
  | exception Engine.Not_at_fixpoint msg -> Some msg

let contains msg sub =
  let n = String.length sub and h = String.length msg in
  let rec go i = i + n <= h && (String.sub msg i n = sub || go (i + 1)) in
  go 0

(* (a) The mask set correctly: [Eq_dom] declares [Domain] consistency, so the default
   derivation gives it [wake_on_any], it is woken by the hole, and the fixpoint is a
   real one. *)
let test_hole_wake_delivered () =
  let store, engine = hole_scene () in
  Engine.reset_stats ();
  (match Engine.propagate engine store with
  | Engine.Conflict _ ->
      incr failures;
      Printf.printf "FAIL hole wake: unexpected conflict\n"
  | Engine.Fixpoint -> ());
  let _, _, masked = Engine.stats () in
  check "hole wake: a Domain-consistency propagator IS woken by an interior hole"
    (not (Domain.mem (Store.get store (var 1)) 2));
  check "hole wake: nothing was masked in this scene" (masked = 0);
  check "hole wake: the fixpoint survives the I-P2 re-run check"
    (raises_not_at_fixpoint engine store = None)

(* (b) The same scene with the mask deliberately wrong: [Eq_dom] is forced to
   bounds-only, which starves it of the one wake it needs.

   This is the break the task asks be made on purpose and watched go red. Note what
   does NOT happen: no exception, no conflict, no wrong-looking domain unless you know
   to look at y. [Engine.propagate] cheerfully reports a fixpoint. The only thing that
   notices is the I-P2 re-run. *)
let starved_message msg =
  (* Printed on a PASS, deliberately: this is what the instrument says when it fires,
     and the next person to see it will be seeing it for real. *)
  Printf.printf "     (what it says: %s)\n"
    (String.concat " " (String.split_on_char '\n' msg));
  check "starved: the message names the propagator that still had work"
    (contains msg "eq_dom" && contains msg "I-P2")

let test_hole_wake_starved_is_caught () =
  let store, engine = hole_scene ~trigger:(fun _ -> Engine.wake_on_bounds) () in
  Engine.reset_stats ();
  (* Which of the two paths this takes depends on BAGUETTE_DEBUG, and both are the same
     instrument. With it OFF (the default), [propagate] returns a fixpoint it should not
     have and the test re-runs the check by hand -- which is the interesting shape,
     because it can also inspect the damage. With it ON, [propagate] runs the check
     itself and refuses to return at all; the suite has to stay green under
     BAGUETTE_DEBUG=1, so that case is a pass here, not an uncaught exception.

     M2-T10 adds a THIRD path, under BAGUETTE_CONSISTENCY, and it is worth saying what it
     means rather than just accommodating it. This scene starves [eq_dom] -- which
     declares [Domain] -- of the wake it needs, so at the fixpoint [propagate] reports,
     y = 2 has no support and a domain-consistent propagator would have removed it. That
     is a violation of the DECLARED LEVEL, which is a different statement from I-P2's
     "someone still has something to say", reached by a different route: I-P2 re-runs the
     propagator, the oracle enumerates. This lane was not written for M2-T10 and M2-T10
     did not know about it; the consistency oracle simply fires on it, which is the best
     evidence available that it catches a starved propagator it was not built against.
     See [Engine.check_consistency] and test/unit/test_consistency.ml. *)
  match Engine.propagate engine store with
  | exception Engine.Weaker_than_declared v ->
      let _, _, masked = Engine.stats () in
      check "starved: the mask really did drop a wake" (masked > 0);
      check
        "starved: under BAGUETTE_CONSISTENCY the M2-T10 oracle refuses the \
         fixpoint,          naming the unsupported value"
        (v.Engine.vi_var_name = "y" && v.Engine.vi_value = 2
        && v.Engine.vi_declared = Propagator.Domain)
  | exception Engine.Not_at_fixpoint msg ->
      let _, _, masked = Engine.stats () in
      check "starved: the mask really did drop a wake" (masked > 0);
      check "starved: under BAGUETTE_DEBUG, propagate itself refuses the fixpoint" true;
      starved_message msg
  | Engine.Conflict _ ->
      incr failures;
      Printf.printf "FAIL starved: unexpected conflict\n"
  | Engine.Fixpoint -> (
      let _, _, masked = Engine.stats () in
      check "starved: the mask really did drop a wake" (masked > 0);
      (* The symptom, and the reason a green model suite proves nothing here: the solver
         lost a pruning and said "fixpoint" anyway. *)
      check "starved: propagate reports a fixpoint at which y has NOT lost the value"
        (Domain.mem (Store.get store (var 1)) 2);
      match raises_not_at_fixpoint engine store with
      | None ->
          incr failures;
          Printf.printf
            "FAIL starved: the I-P2 re-run check did NOT catch a starved propagator. \
             That check is this round's only instrument for an unsound wake mask; if it \
             cannot see this, it cannot see anything.\n"
      | Some msg ->
          check "starved: the I-P2 re-run check catches it" true;
          starved_message msg)

(* (c) The mask firing on a REAL propagator, and being safe when it does. [Linear]
   declares [Bounds] and reads only [Domain.lo]/[Domain.hi], so dropping its wake for
   an interior hole must cost nothing -- and the I-P2 re-run is what says "must cost
   nothing" out loud rather than in a comment. *)
let test_bounds_propagator_masked_safely () =
  let store = mk_store [ ("x", 0, 4); ("y", 0, 4) ] in
  let lin = Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 8 in
  let engine =
    Engine.create [ pack_linear 0 lin; pack_punch 1 { Punch.px = var 0; pv = 2 } ]
  in
  Engine.reset_stats ();
  (match Engine.propagate engine store with
  | Engine.Conflict _ ->
      incr failures;
      Printf.printf "FAIL masked-safely: unexpected conflict\n"
  | Engine.Fixpoint -> ());
  let _, _, masked = Engine.stats () in
  check "masked-safely: a Bounds propagator's wake for an interior hole is dropped"
    (masked > 0);
  check "masked-safely: and dropping it leaves a genuine fixpoint (I-P2)"
    (raises_not_at_fixpoint engine store = None);
  check "masked-safely: the hole itself was still punched"
    (not (Domain.mem (Store.get store (var 0)) 2))

(* The derivation itself, spelled out, so that a later edit to
   [trigger_of_consistency] that quietly masks [Domain] or [Value] propagators has to
   change a test that says why that would be wrong. *)
let test_trigger_derivation () =
  let t = Engine.trigger_of_consistency in
  check "trigger: Bounds consistency wakes on bound moves only"
    (t Propagator.Bounds = Engine.wake_on_bounds);
  check "trigger: Domain consistency wakes on everything"
    (t Propagator.Domain = Engine.wake_on_any);
  check "trigger: Value consistency wakes on everything -- int_ne reads Domain.mem"
    (t Propagator.Value = Engine.wake_on_any);
  check "trigger: Checking consistency wakes on everything"
    (t Propagator.Checking = Engine.wake_on_any);
  check "trigger: a bounds-only mask does not drop bound moves"
    (Engine.wakes_on Engine.wake_on_bounds (Domain.Bound { lo = Some 3; hi = None }));
  check "trigger: a bounds-only mask drops interior holes"
    (not (Engine.wakes_on Engine.wake_on_bounds (Domain.Holes [ 2 ])));
  check "trigger: nobody is woken by NoChange"
    (not (Engine.wakes_on Engine.wake_on_any Domain.NoChange))

(* The I-P2 re-run check applied to the plain linear scenes of test 1: it must be quiet
   on a fixpoint that really is one. Without this, "the check catches the starved
   scene" would be consistent with a check that raises on everything. *)
let test_check_fixpoint_is_quiet_on_real_fixpoints () =
  let store = mk_store [ ("x1", 0, 5); ("x2", 3, 5) ] in
  let lin = Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 3 in
  let engine = Engine.create [ pack_linear 0 lin ] in
  (match Engine.propagate engine store with
  | Engine.Conflict _ -> ()
  | Engine.Fixpoint -> ());
  check "I-P2 check: quiet on a linear fixpoint"
    (raises_not_at_fixpoint engine store = None)

(* ===================================================================== *)
(* Shared model builders for the search tests (2, 3, 4).                 *)
(*                                                                       *)
(* SAT model: x1, x2, x3 in [0,1], x1 = x2, x1+x2+x3 = 2. First-fail ties *)
(* on all three at level 0 (all size 2); index order picks x1.           *)
(* indomain_min tries x1=0 first: forces x2=0 (equality), which forces   *)
(* x3=2 -- out of [0,1] -- a conflict on the FIRST branch. Backtracking  *)
(* to x1=1 forces x2=1, x3=0: a real solution. Exactly one decision      *)
(* level, exactly one backtrack, deliberately -- this is the case the    *)
(* task asks be exercised, not a search deep enough to bury the point.   *)
(*                                                                       *)
(* UNSAT model: x1, x2 in [0,1], x1 = x2, x1+x2 = 1 -- two equal 0/1     *)
(* variables cannot sum to an odd number, so both branches of the same   *)
(* single decision fail, and the combined (decision-free) nogood is the  *)
(* proof's contradiction.                                               *)
(* ===================================================================== *)

let sat_domains = [ ("x1", 0, 1); ("x2", 0, 1); ("x3", 0, 1) ]

(* [x = y] and [sum terms = rhs], each as a pair of Linear.t (<=, >=) -- exactly
   docs/DECISIONS.md D-0011's shape, built directly against [Linear] rather than
   through [Lin_eq]/[Int_eq] (lib/core/prop/**, owned by another session actively
   editing it this round) so this test does not depend on files outside this task's
   ownership.

   M1-T31: each half now takes the id of the .opb row it justifies against, because
   [Linear.make]'s [~row_id] is required. The ids are the ones
   [Encoding.add_equality] just handed back and not invented, so the scene builders
   below have to post the encoding first -- which is why they return it. They used to
   build the store and the encoding in two unrelated functions, with the propagator
   instances naming no row at all and falling back on an ambient one that these tests
   asserted was never consulted. *)
let eq_pair store a b ~le_id ~ge_id =
  ( Linear.make ~row_id:le_id store [ (1, a); (-1, b) ] 0,
    Linear.make ~row_id:ge_id store [ (-1, a); (1, b) ] 0 )

let sum_eq_pair store terms rhs ~le_id ~ge_id =
  ( Linear.make ~row_id:le_id store terms rhs,
    Linear.make ~row_id:ge_id store (List.map (fun (c, x) -> (-c, x)) terms) (-rhs) )

(* [Encoding.add_equality] returns [(geq, leq)] -- see [Lin_eq.make]'s header, which
   pairs them the same way round. *)
let sat_scene () =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) sat_domains;
  let ge_a, le_a =
    Encoding.add_equality e [ (1, Lit.ge "x1" 1); (-1, Lit.ge "x2" 1) ] 0
  in
  let ge_b, le_b =
    Encoding.add_equality e
      [ (1, Lit.ge "x1" 1); (1, Lit.ge "x2" 1); (1, Lit.ge "x3" 1) ]
      2
  in
  let store = mk_store sat_domains in
  let x1, x2, x3 = (var 0, var 1, var 2) in
  let le1, ge1 = eq_pair store x1 x2 ~le_id:le_a ~ge_id:ge_a in
  let le2, ge2 =
    sum_eq_pair store [ (1, x1); (1, x2); (1, x3) ] 2 ~le_id:le_b ~ge_id:ge_b
  in
  let engine =
    Engine.create
      [ pack_linear 0 le1; pack_linear 1 ge1; pack_linear 2 le2; pack_linear 3 ge2 ]
  in
  (store, engine, e)

let sat_check (assignment : Search.assignment) =
  let v i = List.assoc (var i) assignment in
  v 0 = v 1 && v 0 + v 1 + v 2 = 2

let unsat_domains = [ ("x1", 0, 1); ("x2", 0, 1) ]

let unsat_scene () =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) unsat_domains;
  let ge_a, le_a =
    Encoding.add_equality e [ (1, Lit.ge "x1" 1); (-1, Lit.ge "x2" 1) ] 0
  in
  let ge_b, le_b = Encoding.add_equality e [ (1, Lit.ge "x1" 1); (1, Lit.ge "x2" 1) ] 1 in
  let store = mk_store unsat_domains in
  let x1, x2 = (var 0, var 1) in
  let le1, ge1 = eq_pair store x1 x2 ~le_id:le_a ~ge_id:ge_a in
  let le2, ge2 = sum_eq_pair store [ (1, x1); (1, x2) ] 1 ~le_id:le_b ~ge_id:ge_b in
  let engine =
    Engine.create
      [ pack_linear 0 le1; pack_linear 1 ge1; pack_linear 2 le2; pack_linear 3 ge2 ]
  in
  (store, engine, e)

(* M1-T31: a [ctx] has no ambient row any more, so there is no [~model_id] thunk here
   to assert is never consulted. Every explanation names its own row. *)
let mk_ctx writer encoding = Justify.create ~writer ~encoding

(* ===================================================================== *)
(* 2 and 3. Search functional behaviour: SAT with I-S1's independent      *)
(* check, UNSAT with I-S2/I-S3.                                          *)
(* ===================================================================== *)

let scratch_writer () =
  let path = Filename.temp_file "baguette_engine" ".pbp" in
  let oc = open_out path in
  (path, oc)

let test_search_finds_and_verifies_a_solution () =
  let store, engine, encoding = sat_scene () in
  let path, oc = scratch_writer () in
  let writer = Writer.create ~comments:false ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let entry_level = Store.level store in
  let outcome = Search.solve ~engine ~store ~ctx ~check:sat_check () in
  close_out oc;
  Sys.remove path;
  (match outcome with
  | Search.Unsat ->
      incr failures;
      Printf.printf "FAIL search: expected Sat, got Unsat\n"
  | Search.Sat assignment ->
      check "search: solution independently satisfies every constraint (I-S1)"
        (sat_check assignment));
  check "search: decision level restored on return (I-S3)"
    (Store.level store = entry_level)

let test_search_exhausts_and_reports_unsat () =
  let store, engine, encoding = unsat_scene () in
  let path, oc = scratch_writer () in
  let writer = Writer.create ~comments:false ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let entry_level = Store.level store in
  let outcome = Search.solve ~engine ~store ~ctx ~check:(fun _ -> true) () in
  close_out oc;
  Sys.remove path;
  check "search: exhausts and reports UNSAT (I-S2)"
    (match outcome with Search.Unsat -> true | Search.Sat _ -> false);
  check "search: decision level restored on return (I-S3)"
    (Store.level store = entry_level)

(* ===================================================================== *)
(* 5. BAGUETTE_PROOF_AUDIT: an empty live set at conclusion (I-X2).       *)
(*                                                                       *)
(* [Writer.create ~audit:true] is used throughout this file rather than  *)
(* relying on the environment variable -- [Writer.audit_enabled] is only *)
(* consulted when the optional argument is *omitted*, so passing the     *)
(* flag explicitly exercises exactly the same audit machinery            *)
(* BAGUETTE_PROOF_AUDIT=1 would, deterministically. Both the SAT and the *)
(* UNSAT proof above already run under it (a raised [Writer.Audit_failed] *)
(* would have shown up as an uncaught exception there); this test makes  *)
(* the "empty live set at conclusion" check explicit and independent of  *)
(* whether [Search.solve] happened to raise. *)
(* ===================================================================== *)

let test_audit_empty_at_conclusion () =
  let run build_scene check =
    let store, engine, encoding = build_scene () in
    let path, oc = scratch_writer () in
    let writer = Writer.create ~comments:false ~audit:true oc in
    Encoding.start_proof encoding writer;
    let ctx = mk_ctx writer encoding in
    let live_before_conclusion = ref (-1) in
    (* [Search.solve] calls [Writer.conclusion] itself, which is also where the audit
       check runs; capture live_count from inside by wrapping conclusion is not
       possible without touching Writer, so instead this reruns the same recipe
       [Search.solve] uses up to (but not including) conclusion is not exposed either.
       What *is* directly observable: [Writer.conclusion] would have raised
       [Writer.Audit_failed] if the live set were non-empty, and it did not -- so
       check that no exception escaped, and separately confirm the writer's live
       count really is zero right after, which is the same thing the audit itself
       asserted internally. *)
    let outcome = Search.solve ~engine ~store ~ctx ~check () in
    live_before_conclusion := Writer.live_count writer;
    close_out oc;
    Sys.remove path;
    (outcome, !live_before_conclusion)
  in
  let _, live_sat = run sat_scene sat_check in
  check "audit: SAT proof's live set is empty at conclusion (I-X2)" (live_sat = 0);
  let _, live_unsat = run unsat_scene (fun _ -> true) in
  check "audit: UNSAT proof's live set is empty at conclusion (I-X2)" (live_unsat = 0)

(* ===================================================================== *)
(* 4. veripb accepts the proof of a real search -- SAT and UNSAT, each    *)
(*    with a backtrack. This is the check that matters.                  *)
(* ===================================================================== *)

(* Which checker to run: lib/proof/checker.ml, shared with scripts/checker.sh.
   Every test module open-coded this search, and every copy resolved it differently --
   so a project-wide choice of checker lived in nine places and could silently mean a
   build nobody intended (M1-T18). [None] is a FAILURE at every
   call site below, never a skip. *)
let veripb_path () = Baguette_proof.Checker.find ()

let run_veripb ~name ~build =
  match veripb_path () with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- invariant I-X1 was NOT checked. Install it (see \
         docs/PROOF-FORMAT.md) and re-run; do not treat this as a pass.\n"
        name
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_engine_veripb" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp = build dir in
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      let out =
        let ic = open_in_bin log in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      in
      if rc = 0 then Printf.printf "ok   %s (I-X1)\n" name
      else (
        incr failures;
        Printf.printf "FAIL %s: veripb rejected the proof (I-X1)\n%s\n" name out;
        Printf.printf "  model: %s\n  proof: %s\n" opb pbp);
      List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; log ];
      try Sys.rmdir dir with _ -> ())

let build_search_sat_proof dir =
  let store, engine, encoding = sat_scene () in
  let opb = Filename.concat dir "search_sat.opb" in
  let pbp = Filename.concat dir "search_sat.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x1 = x2; x1 + x2 + x3 = 2" ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  (match Search.solve ~engine ~store ~ctx ~check:sat_check () with
  | Search.Sat _ -> ()
  | Search.Unsat -> failwith "build_search_sat_proof: expected Sat");
  close_out oc;
  (opb, pbp)

let build_search_unsat_proof dir =
  let store, engine, encoding = unsat_scene () in
  let opb = Filename.concat dir "search_unsat.opb" in
  let pbp = Filename.concat dir "search_unsat.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x1 = x2; x1 + x2 = 1" ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  (match Search.solve ~engine ~store ~ctx ~check:(fun _ -> true) () with
  | Search.Unsat -> ()
  | Search.Sat _ -> failwith "build_search_unsat_proof: expected Unsat");
  close_out oc;
  (opb, pbp)

(* ===================================================================== *)
(* 6. M1-T55. A decision whose push settles past a hole, and the bridge  *)
(*    line that puts the settle on the page.                             *)
(* ===================================================================== *)

(* [hx], [hy] in 0..2 with [hx <> 1], [hx = hy] and [hx <> hy].

   Every part of that is load-bearing, and the shape is the one M1-T44/M2-T11 describe:

     - [hx <> 1] is a disequality with one term, so it prunes at the root and punches a
       hole strictly inside [0, 2]. No bound moves, so lib/core/trace.ml writes no line
       for it -- the exclusion is on the page only as the .opb rows of that disequality.
     - [hx <> hy] has two unfixed terms, so it infers nothing at the root. That is what
       makes the search *have* to branch rather than being handed the answer by
       propagation (the blind spot test/models/guess_wrong_sat.fzn's header records).
     - [hx = hy] beside it makes the model UNSAT, so both branches fail and both nogoods
       are emitted -- including the high side's, which is the one the settle is under.

   So at the root fixpoint [hx] is {0, 2}: [first_fail] picks it (size 2 against [hy]'s
   3), docs/SPEC.md 3.4's indomain_min splits at [lo = 0], and [explore_ge] pushes
   [set_lo hx 1] -- straight onto the hole, which [Domain.settle] walks to 2. The trail
   then records [hx >= 2] while the nogood negates [hx_ge_1].
   [test_hole_split_precondition] asserts that precondition directly instead of trusting
   this paragraph, because an instance that has stopped exhibiting the defect it was
   written for is this project's signature failure (M1-T45, M1-T50). *)
let hole_domains = [ ("hx", 0, 2); ("hy", 0, 2) ]

let hole_scene () =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) hole_domains;
  ignore (Encoding.add_int_lin_ne e [ (1, "hx") ] 1 : int * int);
  let le_id = Encoding.add_int_lin_le e [ (1, "hx"); (-1, "hy") ] 0 in
  let ge_id = Encoding.add_int_lin_le e [ (-1, "hx"); (1, "hy") ] 0 in
  ignore (Encoding.add_int_lin_ne e [ (1, "hx"); (-1, "hy") ] 0 : int * int);
  let store = mk_store hole_domains in
  let hx, hy = (var 0, var 1) in
  let le, ge = eq_pair store hx hy ~le_id ~ge_id in
  let ne_hole = Ne.make store [ (1, hx) ] 1 in
  let ne_pair = Ne.make store [ (1, hx); (-1, hy) ] 0 in
  let engine =
    Engine.create
      [ pack_linear 0 le; pack_linear 1 ge; pack_ne 2 ne_hole; pack_ne 3 ne_pair ]
  in
  (store, engine, e)

let test_hole_split_precondition () =
  let store, engine, _ = hole_scene () in
  (match Engine.propagate engine store with
  | Engine.Conflict _ ->
      check "M1-T55: the hole scene reaches a root fixpoint rather than failing there"
        false
  | Engine.Fixpoint -> ());
  let d = Store.get store (var 0) in
  check
    "M1-T55: at the root fixpoint hx is unfixed with lo = 0 and lo + 1 a HOLE -- so \
     spec_order splits at 0 and the high push settles past 1"
    (Domain.size d > 1 && Domain.lo d = 0 && (not (Domain.mem d 1)) && Domain.mem d 2);
  check "M1-T55: hy is the wider domain, so first_fail branches on hx"
    (Domain.size (Store.get store (var 1)) > Domain.size d)

let build_hole_split_proof dir =
  let store, engine, encoding = hole_scene () in
  let opb = Filename.concat dir "hole_split.opb" in
  let pbp = Filename.concat dir "hole_split.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "hx <> 1; hx = hy; hx <> hy" ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  (match Search.solve ~engine ~store ~ctx ~check:(fun _ -> true) () with
  | Search.Unsat -> ()
  | Search.Sat _ -> failwith "build_hole_split_proof: expected Unsat");
  close_out oc;
  (opb, pbp)

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let contains needle s =
  let n = String.length needle and m = String.length s in
  let rec go i = i + n <= m && (String.sub s i n = needle || go (i + 1)) in
  n = 0 || go 0

let lines_of s = String.split_on_char '\n' s

(* The bridge this scene must produce, as bytes. Deliberately a literal string and not
   something rebuilt out of [Lit]: a fix that computed the right clause and then failed
   to write it would satisfy a check phrased in terms of [Lit], and "the check could not
   see its own subject fail" is the thing this project keeps getting caught by. *)
let hole_bridge_body = "+1 hx_ge_2 +1 ~hx_ge_1 >= 1"

(* Is this line derivable from the model *alone*? A one-rule proof: load the .opb, state
   the line, conclude nothing. VeriPB accepts `conclusion NONE`. The same question
   test/unit/test_trace.ml asks of every trace line, asked here of the bridge -- which is
   the whole claim the bridge makes, since it is decision-free for this scene (the split
   is at the root, so it has no ancestors to carry).

   **What this check cannot see, measured rather than assumed.** It confirms the bridge is
   derivable. It does NOT discriminate a correct bridge from an over-strong one, and the
   reason is structural, not a defect in the wiring:

     - this scene's .opb is unsatisfiable, and every clause over its variables is
       therefore entailed by it -- `rup +1 hx_ge_2 >= 1`, the bridge with its own
       assumption dropped, verifies standalone here too;
     - and that is not cured by moving to a satisfiable scene. [spec_order] is low-side
       first, so it enters the high side of a hole split only when [x = lo] has just
       failed *under the ancestor decisions* -- which is to say the claim literal is
       entailed under those ancestors wherever a bridge exists at all. A scene where it
       is not would need the hole split to sit under a decision path that fails while
       some other path has a solution with [x = lo].

   So the discriminating check here is the byte-exact one above, which reddens under all
   three of "the bridge is not emitted", "its claim is off by one" and "its assumption is
   dropped". This one is the I-X1 statement -- the line veripb is asked to accept really
   is accepted, standing alone, with no search and no other derived constraint in the
   database. Both are worth having and neither is the other. *)
let standalone_verifies ~veripb ~dir ~opb ~n_model rule_line =
  let t s = s ^ " ;" in
  let pbp = Filename.concat dir "standalone.pbp" in
  let oc = open_out pbp in
  output_string oc
    (String.concat "\n"
       [
         "pseudo-Boolean proof version 3.0";
         t (Printf.sprintf "f %d" n_model);
         rule_line;
         t "output NONE";
         t "conclusion NONE";
         t "end pseudo-Boolean proof";
         "";
       ]);
  close_out oc;
  let log = Filename.concat dir "standalone.log" in
  let rc =
    Sys.command
      (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb) (Filename.quote opb)
         (Filename.quote pbp) (Filename.quote log))
  in
  (rc = 0, read_file log)

let test_hole_split_bridge () =
  let name = "M1-T55: the bridge for a decision that settled past a hole" in
  match veripb_path () with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- the bridge was NOT checked. Install it and re-run; \
         do not treat this as a pass.\n"
        name
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_hole_split" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let opb, pbp = build_hole_split_proof dir in
      let proof = read_file pbp in
      (* 1. The line is on the page at all. *)
      let bridge_line =
        List.find_opt
          (fun l -> contains "rup" l && contains hole_bridge_body l)
          (lines_of proof)
      in
      (match bridge_line with
      | None ->
          incr failures;
          Printf.printf
            "FAIL %s: no `rup %s` in the emitted proof. The decision's push settled from \
             hx >= 1 onto hx >= 2 and nothing said so, which is the M1-T55 defect.\n\
            \  proof: %s\n"
            name hole_bridge_body pbp
      | Some l -> Printf.printf "ok   %s is emitted (%s)\n" name (String.trim l));
      (* 2. It is a real consequence of the model, not decoration. *)
      let n_model =
        List.fold_left
          (fun acc l ->
            match String.split_on_char ' ' (String.trim l) with
            | "f" :: n :: _ -> ( try int_of_string n with _ -> acc)
            | _ -> acc)
          0 (lines_of proof)
      in
      (match bridge_line with
      | None -> ()
      | Some l -> (
          match standalone_verifies ~veripb ~dir ~opb ~n_model (String.trim l) with
          | true, _ ->
              Printf.printf
                "ok   %s verifies STANDALONE against the .opb (I-X1, and it is not \
                 decoration)\n"
                name
          | false, log ->
              incr failures;
              Printf.printf
                "FAIL %s: the bridge is NOT derivable from the model alone. %s\n\
                \  model: %s\n"
                name log opb));
      (* 3. And the whole proof still verifies, bridge and all. *)
      let log = Filename.concat dir "whole.log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      if rc = 0 then
        Printf.printf "ok   %s: the whole hole-split proof verifies (I-X1)\n" name
      else (
        incr failures;
        Printf.printf "FAIL %s: veripb rejected the hole-split proof (I-X1)\n%s\n" name
          (read_file log));
      List.iter
        (fun f -> try Sys.remove f with _ -> ())
        [
          opb;
          pbp;
          log;
          Filename.concat dir "standalone.pbp";
          Filename.concat dir "standalone.log";
        ];
      try Sys.rmdir dir with _ -> ())

(* ===================================================================== *)
(* 7. M1-T36. The node counter, and the fact that it is NOT the level    *)
(*    marker count the benchmark used to report in its place.            *)
(* ===================================================================== *)

(* How many level markers does a proof contain? This is the benchmark's old `lvl` proxy,
   transcribed. The spelling is [Writer.level_marker]'s -- there is no set-level RULE at
   all (D-0024), so [Writer.set_level] leaves the comment `% level l` -- and it is asked
   for here rather than hardcoded, so a test that pins a count cannot silently start
   counting nothing if the spelling moves. *)
let level_markers pbp =
  List.length
    (List.filter
       (fun l ->
         let l = String.trim l in
         let after p =
           String.length l > String.length p
           && String.sub l 0 (String.length p) = p
           &&
           let rest =
             String.sub l (String.length p) (String.length l - String.length p)
           in
           rest <> "" && String.for_all (fun c -> c >= '0' && c <= '9') rest
         in
         after "% level ")
       (lines_of (read_file pbp)))

let check_eq name got want =
  if got = want then Printf.printf "ok   %s (%d)\n" name got
  else (
    incr failures;
    Printf.printf "FAIL %s: got %d, want %d\n" name got want)

(* [unsat_scene] is x1 = x2 and x1 + x2 = 1 over 0..1, and its tree is small enough to
   write down by hand rather than record whatever the counter happens to say -- which is
   the whole point, since a counter checked against its own output checks nothing.

   Root: no bound moves (x1 + x2 = 1 with both in 0..1 tightens nothing), so the root is
   a fixpoint with two unfixed variables. [first_fail] breaks the size tie by index and
   picks x1; [spec_order] splits at [lo = 0]. The low side fixes x1 = 0, which forces
   x2 = 0 and contradicts the sum; the high side fixes x1 = 1, which forces x2 = 1 and
   contradicts it again. So: ONE decision, TWO children, and the root.

   nodes = 3, decisions = 1, max_depth = 1. *)
let unsat_tree = (3, 1, 1)

(* And the marker count that same run's proof carries, pinned as a number rather than
   compared to the nodes. Both numbers are pinned so that a change in either one reddens,
   and one changed: M2-L3 introduces a learned clause at level 0 through
   [Justify.with_level] (D-0045's addendum), which is a marker pair per learned clause on
   top of the branching's own -- a cost D-0045 states and does not hide.

   3 nodes and 7 markers here; 3 nodes and 4 markers on [sat_tree_markers]'s scene. The
   finding is unchanged and is if anything louder than when the two read 3 and 2: the
   proxy is neither the node count nor a multiple of it, and it now moves with the
   DERIVATION shape as well as the tree's -- which is precisely the confusion D-0026's
   claim cannot be tested through. The tree itself did not move: nodes, decisions and
   depth are all still what [unsat_tree] pins, and M2-L3's backjump does not fire on a
   one-decision tree because there is no intervening level to skip. *)
let unsat_markers = 7
let sat_tree_markers = (3, 1, 4)
let node_stats = ref None
let sat_node_stats = ref None

let build_node_count_proof dir =
  let store, engine, encoding = unsat_scene () in
  let opb = Filename.concat dir "nodes.opb" in
  let pbp = Filename.concat dir "nodes.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x1 = x2; x1 + x2 = 1" ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let stats = Search.stats_create () in
  (match Search.solve ~engine ~store ~ctx ~check:(fun _ -> true) ~stats () with
  | Search.Unsat -> ()
  | Search.Sat _ -> failwith "build_node_count_proof: expected Unsat");
  close_out oc;
  node_stats := Some (stats, level_markers pbp);
  (opb, pbp)

(* The counts themselves, read back from the run [run_veripb] just checked. Asserting
   them there rather than in a run of its own is deliberate: the numbers then describe a
   search whose proof a real checker accepted, so "a test that does not check the proof
   is half a test" holds for the counter too. *)
let test_node_counts () =
  match !node_stats with
  | None ->
      incr failures;
      print_endline
        "FAIL M1-T36: the node-count proof was never built, so nothing was counted"
  | Some (st, markers) ->
      let n, d, depth = unsat_tree in
      check_eq "M1-T36: nodes visited on the hand-derived UNSAT tree" st.Search.nodes n;
      check_eq "M1-T36: decisions taken on it" st.Search.decisions d;
      check_eq "M1-T36: tree depth reached" st.Search.max_depth depth;
      check "M1-T36: nodes = 2 * decisions + 1 -- the tree was exhausted"
        (Search.stats_consistent st ~exhausted:true);
      check_eq "M1-T36: level markers in the same proof -- the old `lvl` proxy" markers
        unsat_markers

(* And the other half of the identity: a search that stops at the first solution has
   NOT visited both sides of every decision, so only the inequality may be asserted.
   [sat_scene] is x1 = x2 and x1 + x2 + x3 = 2 over the same widths. *)
let test_node_counts_sat () =
  let store, engine, encoding = sat_scene () in
  let path, oc = scratch_writer () in
  let writer = Writer.create ~comments:false ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let stats = Search.stats_create () in
  let outcome = Search.solve ~engine ~store ~ctx ~check:sat_check ~stats () in
  close_out oc;
  let markers = level_markers path in
  Sys.remove path;
  check "M1-T36: the SAT scene is still SAT with a stats record threaded through it"
    (match outcome with Search.Sat _ -> true | Search.Unsat -> false);
  check "M1-T36: nodes <= 2 * decisions + 1 on a search stopped at a solution"
    (Search.stats_consistent stats ~exhausted:false);
  check "M1-T36: the root alone is a node, so a search that ran counts at least one"
    (stats.Search.nodes >= 1);
  let n, d, m = sat_tree_markers in
  check_eq "M1-T36: nodes visited before the first solution" stats.Search.nodes n;
  check_eq "M1-T36: decisions taken before it" stats.Search.decisions d;
  check_eq "M1-T36: level markers in the SAT proof" markers m;
  sat_node_stats := Some (stats, markers)

(* THE POINT OF THE ROW, and it can only be made by comparing two trees. The proxy is
   not the node count, and it is not a fixed multiple of it either: the UNSAT scene has
   3 nodes and 3 markers, the SAT scene has 3 nodes and 2 markers. Same node count,
   different marker count -- so a benchmark holding only the markers cannot tell whether
   the tree moved, which is exactly what D-0026's claim needs it to be able to do.
   A change that made this counter read the proof back, or a scaling that pretended one
   number is the other times a constant, reddens here. *)
let test_marker_proxy_is_not_the_node_count () =
  match (!node_stats, !sat_node_stats) with
  | Some (u, um), Some (sa, sm) ->
      check
        "M1-T36: two trees with the SAME node count carry DIFFERENT marker counts -- the \
         proxy is neither the node count nor a multiple of it"
        (u.Search.nodes = sa.Search.nodes && um <> sm)
  | _ ->
      incr failures;
      print_endline
        "FAIL M1-T36: one of the two runs did not record its counts, so the proxy \
         comparison was NOT made"

(* ===================================================================== *)
(* 8. M1-T45. Every branching shape random_order's hole guard refused,   *)
(*    forced deliberately, and the real checker over each proof.          *)
(* ===================================================================== *)

(* The guard's own condition, transcribed: it would take a split at [k] only when both
   [k] and [k + 1] were in the domain. Everything else it refused, and this predicate is
   what says a shape below is one of those -- rather than a comment claiming it is. *)
let guard_refused d k = not (Domain.mem d k && Domain.mem d (k + 1))

(* An order that makes one chosen decision and otherwise defers to the normative one.
   This is how the refused shapes get exercised DELIBERATELY instead of being waited for:
   [random_order] would reach them at 0.4% of its draws, which is a measurement, not a
   test. *)
let forced_order (wanted : (Var.t * int * bool) list) store cands =
  let rec pick = function
    | [] -> Search.spec_order store cands
    | (v, k, hf) :: rest ->
        let d = Store.get store v in
        if Array.exists (fun c -> c = v) cands && k >= Domain.lo d && k < Domain.hi d then
          Search.Split { Search.d_var = v; d_split = k; d_high_first = hf }
        else pick rest
  in
  pick wanted

(* [hx] in 0..4 with a hole punched at each of [holes], [hy] in 0..4, [hx = hy] and
   [hx <> hy]. Built to the same recipe as [hole_scene] above and for the same reasons:
   the disequalities punch interior holes at the root without moving a bound, [hx <> hy]
   has two unfixed terms so it infers nothing and the search must branch, and [hx = hy]
   beside it makes the model UNSAT so BOTH children emit a nogood -- which is where a
   settled decision has to be bridged. Width 5, so the order encoding stays small and
   the declared-width lint has nothing to say. *)
let sweep_domains = [ ("hx", 0, 4); ("hy", 0, 4) ]

let sweep_scene holes =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) sweep_domains;
  List.iter
    (fun h -> ignore (Encoding.add_int_lin_ne e [ (1, "hx") ] h : int * int))
    holes;
  let le_id = Encoding.add_int_lin_le e [ (1, "hx"); (-1, "hy") ] 0 in
  let ge_id = Encoding.add_int_lin_le e [ (-1, "hx"); (1, "hy") ] 0 in
  ignore (Encoding.add_int_lin_ne e [ (1, "hx"); (-1, "hy") ] 0 : int * int);
  let store = mk_store sweep_domains in
  let hx, hy = (var 0, var 1) in
  let le, ge = eq_pair store hx hy ~le_id ~ge_id in
  let props =
    pack_linear 0 le :: pack_linear 1 ge
    :: List.mapi (fun i h -> pack_ne (2 + i) (Ne.make store [ (1, hx) ] h)) holes
    @ [ pack_ne (2 + List.length holes) (Ne.make store [ (1, hx); (-1, hy) ] 0) ]
  in
  (store, Engine.create props, e)

(* Three variables in 0..2, each with its middle value punched out, and a disequality
   against every sum they can reach. Three unfixed terms infer nothing, and two still
   infer nothing, so the search must take TWO decisions before propagation can close a
   branch -- which is what puts a settled hole decision in [bridges]' ANCESTORS list
   rather than only in its own conjunct. The depth-1 sweep above cannot reach that. *)
let deep_domains = [ ("dx", 0, 2); ("dy", 0, 2); ("dz", 0, 2) ]

let deep_scene () =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) deep_domains;
  List.iter
    (fun n -> ignore (Encoding.add_int_lin_ne e [ (1, n) ] 1 : int * int))
    [ "dx"; "dy"; "dz" ];
  let terms = [ (1, "dx"); (1, "dy"); (1, "dz") ] in
  List.iter
    (fun c -> ignore (Encoding.add_int_lin_ne e terms c : int * int))
    [ 0; 2; 4; 6 ];
  let store = mk_store deep_domains in
  let dx, dy, dz = (var 0, var 1, var 2) in
  let holes =
    List.mapi (fun i v -> pack_ne i (Ne.make store [ (1, v) ] 1)) [ dx; dy; dz ]
  in
  let sums =
    List.mapi
      (fun i c -> pack_ne (3 + i) (Ne.make store [ (1, dx); (1, dy); (1, dz) ] c))
      [ 0; 2; 4; 6 ]
  in
  (store, Engine.create (holes @ sums), e)

(* One shape: build the scene, force the decisions, solve to UNSAT, hand the proof to
   the real checker. Returns [None] on acceptance and [Some complaint] on rejection --
   and a missing checker is a rejection here, never a skip (I-X1). *)
let run_shape ~veripb ~dir ~tag ~scene ~opb_comment ~wanted =
  let store, engine, encoding = scene () in
  let opb = Filename.concat dir (tag ^ ".opb") in
  let pbp = Filename.concat dir (tag ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ opb_comment ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let stats = Search.stats_create () in
  let outcome =
    Search.solve ~engine ~store ~ctx
      ~check:(fun _ -> true)
      ~stats ~order:(forced_order wanted) ()
  in
  close_out oc;
  let verdict =
    match outcome with
    | Search.Sat _ -> Some "the scene was SAT, so no child nogood was emitted"
    | Search.Unsat ->
        let log = Filename.concat dir (tag ^ ".log") in
        let rc =
          Sys.command
            (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
               (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
        in
        let out = read_file log in
        (try Sys.remove log with _ -> ());
        if rc = 0 then None else Some out
  in
  (* Kept only when it is the evidence of a rejection. *)
  if verdict = None then List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp ];
  (verdict, stats.Search.nodes)

(* The sweep. Every interior hole pattern of a width-5 domain, crossed with every split
   position and both child orders; the ones the guard would have refused are forced and
   checked, and the ones it would have allowed are counted separately so that the
   "refused" figure is a proportion of something and not a bare number.

   THE ROW'S BAR, BOTH WAYS ROUND. M1-T45 asked for "an instance showing what it
   catches" before the shapes could be taken back. A rejection here IS that instance and
   would put the guard back; no rejection over the whole enumeration, with the count
   printed, is the other answer -- and the count is printed precisely so that "no
   instance found" comes with the size of the search that failed to find one. *)
let test_hole_split_sweep () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M1-T45: veripb not found -- NOT ONE hole-split shape was checked. This is \
         not a pass; install it (docs/PROOF-FORMAT.md) and re-run."
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_holesweep" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let refused = ref 0 and allowed = ref 0 and rejected = ref 0 in
      let patterns =
        [ []; [ 1 ]; [ 2 ]; [ 3 ]; [ 1; 2 ]; [ 1; 3 ]; [ 2; 3 ]; [ 1; 2; 3 ] ]
      in
      List.iter
        (fun holes ->
          (* The root fixpoint's domain is what the guard would have inspected, so read
             it from a propagated store rather than computing it from [holes]. *)
          let probe, probe_engine, _ = sweep_scene holes in
          (match Engine.propagate probe_engine probe with
          | Engine.Conflict _ ->
              incr failures;
              Printf.printf
                "FAIL M1-T45: the sweep scene with holes %s failed at the root, so it \
                 branches at nothing\n"
                (String.concat "," (List.map string_of_int holes))
          | Engine.Fixpoint -> ());
          let d = Store.get probe (var 0) in
          for k = Domain.lo d to Domain.hi d - 1 do
            if not (guard_refused d k) then incr allowed
            else
              List.iter
                (fun hf ->
                  incr refused;
                  let tag =
                    Printf.sprintf "h%s_k%d_%s"
                      (String.concat "" (List.map string_of_int holes))
                      k
                      (if hf then "hi" else "lo")
                  in
                  match
                    run_shape ~veripb ~dir ~tag
                      ~scene:(fun () -> sweep_scene holes)
                      ~opb_comment:"hx has interior holes; hx = hy; hx <> hy"
                      ~wanted:[ (var 0, k, hf) ]
                  with
                  | None, _ -> ()
                  | Some why, _ ->
                      incr rejected;
                      Printf.printf
                        "FAIL M1-T45: veripb REJECTED the hole split holes=[%s] k=%d \
                         high_first=%b -- THIS is the instance the guard catches, and it \
                         belongs back\n\
                         %s\n"
                        (String.concat "," (List.map string_of_int holes))
                        k hf why)
                [ false; true ]
          done)
        patterns;
      check
        "M1-T45: the sweep really did reach shapes the guard refused (a sweep that \
         reached none would pass vacuously)"
        (!refused > 0);
      check
        "M1-T45: and shapes it allowed too, so `refused` is a proportion and not a bare \
         count"
        (!allowed > 0);
      (* Pinned, not compared to itself. The enumeration over eight interior hole
         patterns x four split positions x two child orders yields exactly these two
         counts; a change that quietly stopped enumerating -- a pattern dropped, a loop
         bound slipped -- would otherwise still print a confident "0 rejected". *)
      check_eq "M1-T45: hole-split shapes the guard used to refuse, forced and checked"
        !refused 40;
      check_eq "M1-T45: and shapes it would have allowed, in the same enumeration"
        !allowed 12;
      if !rejected = 0 then
        Printf.printf
          "ok   M1-T45: %d previously-refused hole-split shapes forced (against %d the \
           guard allowed), 0 rejected by veripb\n"
          !refused !allowed
      else (
        incr failures;
        Printf.printf "FAIL M1-T45: %d of %d refused shapes were rejected\n" !rejected
          !refused);
      try Sys.rmdir dir with _ -> ())

(* And the depth-2 case, which the sweep above structurally cannot reach: a settled hole
   decision sitting in [bridges]' ancestor list, not just in its own conjunct. *)
let test_hole_split_with_settled_ancestor () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M1-T45: veripb not found -- the ancestor case was NOT checked. Not a pass."
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_holedeep" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      (* The precondition, asserted rather than asserted-in-a-comment: at the root every
         one of the three variables is {0, 2}, so a split at 1 is refused on each, and
         propagation infers nothing -- so the search has to take two of them. *)
      let probe, probe_engine, _ = deep_scene () in
      (match Engine.propagate probe_engine probe with
      | Engine.Conflict _ ->
          incr failures;
          print_endline "FAIL M1-T45: the depth-2 scene failed at the root"
      | Engine.Fixpoint -> ());
      let ok_hole v =
        let d = Store.get probe v in
        Domain.lo d = 0 && Domain.hi d = 2 && (not (Domain.mem d 1)) && guard_refused d 1
      in
      check
        "M1-T45: in the depth-2 scene every variable is {0, 2} at the root, so a split \
         at 1 is one the guard refused"
        (ok_hole (var 0) && ok_hole (var 1) && ok_hole (var 2));
      List.iter
        (fun hf ->
          match
            run_shape ~veripb ~dir
              ~tag:(Printf.sprintf "deep_%s" (if hf then "hi" else "lo"))
              ~scene:deep_scene
              ~opb_comment:"dx, dy, dz in {0, 2}; dx + dy + dz <> 0, 2, 4, 6"
              ~wanted:[ (var 0, 1, hf); (var 1, 1, hf); (var 2, 1, hf) ]
          with
          | None, nodes ->
              check
                (Printf.sprintf
                   "M1-T45: a hole split under a SETTLED hole ancestor verifies \
                    (high_first=%b, %d nodes)"
                   hf nodes)
                (nodes > 3)
          | Some why, _ ->
              incr failures;
              Printf.printf
                "FAIL M1-T45: veripb REJECTED a hole split under a settled hole ancestor \
                 (high_first=%b) -- the guard belongs back\n\
                 %s\n"
                hf why)
        [ false; true ];
      try Sys.rmdir dir with _ -> ())

let () =
  test_fixpoint_tightens_and_settles ();
  test_conflict_carries_explanation ();
  test_attribution_names_the_right_instance ();
  test_conflict_names_its_propagator ();
  test_stolen_credit_is_refused ();
  test_undeclared_variable_is_refused ();
  test_independent_constraints_reach_fixpoint ();
  test_wake_order_is_unchanged ();
  test_trigger_derivation ();
  test_hole_wake_delivered ();
  test_hole_wake_starved_is_caught ();
  test_bounds_propagator_masked_safely ();
  test_check_fixpoint_is_quiet_on_real_fixpoints ();
  test_search_finds_and_verifies_a_solution ();
  test_search_exhausts_and_reports_unsat ();
  test_audit_empty_at_conclusion ();
  run_veripb ~name:"search: a real SAT search with a backtrack, checked end to end"
    ~build:build_search_sat_proof;
  run_veripb ~name:"search: a real UNSAT search with a backtrack, checked end to end"
    ~build:build_search_unsat_proof;
  test_hole_split_precondition ();
  test_hole_split_bridge ();
  run_veripb ~name:"M1-T36: the node-counted UNSAT search, checked end to end"
    ~build:build_node_count_proof;
  test_node_counts ();
  test_node_counts_sat ();
  test_marker_proxy_is_not_the_node_count ();
  test_hole_split_sweep ();
  test_hole_split_with_settled_ancestor ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nengine/search unit tests passed"
