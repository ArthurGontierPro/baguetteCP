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
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Engine = Baguette_core.Engine
module Justify = Baguette_core.Justify
module Search = Baguette_core.Search
module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

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
  (match Store.set_lo store (var 1) 4 (Explanation.model_row 1) with
  | Store.Conflict _ -> failwith "test_conflict_carries_explanation: setup failed"
  | Store.Changed | Store.Unchanged -> ());
  let engine = Engine.create [ pack_linear 0 lin ] in
  match Engine.propagate engine store with
  | Engine.Fixpoint ->
      incr failures;
      Printf.printf "FAIL conflict: expected Conflict, got Fixpoint\n"
  | Engine.Conflict e ->
      let forced = Explanation.force e in
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
    match Store.set_lo store (var v) n (Explanation.model_row 1) with
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

   Both use [Store.remove] with a placeholder [Model_row] reason and no facts. That is
   fine only
   because nothing here writes a proof (see I-P5: a bound-moving prune through a
   factless mutator would write a trace line with an empty reason). No [Engine] test
   below emits proof rules from these two. *)

module Punch = struct
  type t = { px : Var.t; pv : int }

  let name = "punch"

  (* [Value]: it names the value it removes and claims nothing about the rest. Keeps
     [wake_on_any], which is what we want -- the mask under test is the OTHER one's. *)
  let consistency = Propagator.Value
  let vars p = [ p.px ]

  let propagate p store =
    match Store.remove store p.px p.pv (Explanation.model_row 1) with
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
            match Store.remove store b v (Explanation.model_row 1) with
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
     BAGUETTE_DEBUG=1, so that case is a pass here, not an uncaught exception. *)
  match Engine.propagate engine store with
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
   Every test module open-coded this search, and every copy looked at
   ~/.local/bin/veripb first -- so a project-wide choice of checker lived in nine
   places and silently meant the Python 2.2.2 (M1-T18). [None] is a FAILURE at every
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

let () =
  test_fixpoint_tightens_and_settles ();
  test_conflict_carries_explanation ();
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
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nengine/search unit tests passed"
