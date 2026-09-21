(* M2-T10: the consistency oracle's own tests.

   [Engine.check_consistency] asserts that each propagator achieves AT LEAST its declared
   [Propagator.consistency]. Read that function's header first -- it says where the
   semantics come from (the propagator's own checking verdict at total assignments, which
   docs/SPEC.md 3.2 pins), which levels carry an obligation and which carry none, and why
   [Bounds] is read as bounds(Z) rather than bounds(D).

   ---------------------------------------------------------------------------
   What this file has to prove, and in what order
   ---------------------------------------------------------------------------

   A harness that has never been seen to go red is not evidence. Every lane below that
   asserts "no violation" is therefore paired with a CONTROL that differs in one thing and
   DOES go red -- usually the declared level, because the declared level is what is under
   test. If a lane cannot be paired, it says so.

     1. The oracle finds nothing on a propagator that meets its level.
     2. THE BREAK. A propagator with its pruning removed, declared [Domain], is caught,
        and the violation names the variable, the value and the scene.
     3. THE NE LANE, which is the point of the whole exercise. [Ne] deliberately declares
        the weaker [Value] (docs/GLOSSARY.md says so, and lib/core/prop/ne.ml's header
        says so at length). It must PASS. Its control is the SAME INSTANCE with only the
        declared level changed to [Domain], on a scene where [Ne] really is weaker than
        domain consistent -- which proves this harness is testing the DECLARATION and not
        merely soundness.
     4. The bounds(Z) reading, pinned by a scene where bounds(Z) and bounds(D) differ.
     5. Levels that carry no obligation carry none, and that is a decision with a reason
        rather than an omission.
     6. The budget. An instance too wide for brute force is SKIPPED AND COUNTED. A skip
        must never read as a pass.
     7. The oracle does not perturb the search it audits.

   No lane here declares a domain wider than 12 values. Brute force over a scope is a
   product of domain sizes, and CLAUDE.md's width rule is at its sharpest in this file. *)

module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Reason = Baguette_core.Reason
module Explanation = Baguette_core.Explanation
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Ne = Baguette_core.Ne
module Engine = Baguette_core.Engine
module Debug = Baguette_core.Debug

(* M1-T53: the inner heap guard; see mem_guard.ml for what it cannot see. *)
let () = Mem_guard.install ()
let failures = ref 0
let checks = ref 0

let check name cond =
  incr checks;
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let fail fmt =
  incr checks;
  incr failures;
  Printf.ksprintf (fun s -> Printf.printf "FAIL %s\n" s) fmt

(* ------------------------------------------------------------------- helpers *)

let var i = Var.of_int i

(* [dom] takes an explicit value list so a lane can punch a hole, which lane 4 needs:
   bounds(Z) and bounds(D) are the same relation on a domain with no holes, so a scene
   without one cannot tell the two readings apart. *)
let mk_store (specs : (string * int list) list) =
  let names = Array.of_list (List.map fst specs) in
  let domains = Array.of_list (List.map (fun (_, vs) -> Domain.of_list vs) specs) in
  Store.create ~names ~domains

let range lo hi = List.init (hi - lo + 1) (fun i -> lo + i)
let next_row = ref 900

let unrendered_row () =
  incr next_row;
  !next_row

(* Relabelling an instance's declared level is the whole technique of this file's
   controls, and it is available because [Propagator.instance] is a plain record: the
   propagator's CODE is untouched, only what it claims about itself changes. That is the
   point -- CLAUDE.md forbids weakening a propagator to make a test pass, and nothing here
   edits lib/core/prop/. *)
let relabel (inst : Propagator.instance) level =
  { inst with Propagator.inst_consistency = level }

let names_of (vs : Engine.violation list) =
  List.map (fun (v : Engine.violation) -> (v.Engine.vi_var_name, v.Engine.vi_value)) vs

let describe_unexpected label (vs : Engine.violation list) =
  List.iter
    (fun v -> Printf.printf "     %s: %s\n" label (Engine.violation_to_string v))
    vs

(* ===================================================================== *)
(* 1. A propagator that meets its level.                                 *)
(* ===================================================================== *)

(* Domain consistent and genuinely hole-reading: it mirrors each domain into the other,
   which is a pruning no bounds reasoning finds. Same shape as test_engine.ml's [Eq_dom],
   duplicated rather than shared because that file is another session's and because this
   one needs to vary the declared level, which [Eq_dom] fixes. *)
let no_facts = Reason.because ~concludes:None Reason.none (Explanation.model_row 1)

module Eq_dom = struct
  type t = { ex : Var.t; ey : Var.t }

  let name = "eq_dom"
  let consistency = Propagator.Domain
  let vars p = [ p.ex; p.ey ]

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
            match Store.remove store b v no_facts with
            | Store.Conflict e -> Propagator.Conflict e
            | Store.Changed | Store.Unchanged -> Propagator.Fixpoint))
      Propagator.Fixpoint gone

  let propagate p store =
    match mirror store p.ex p.ey with
    | Propagator.Conflict e -> Propagator.Conflict e
    | Propagator.Fixpoint -> mirror store p.ey p.ex
end

(* THE BREAK, and it is a break of the pruning only: the CHECKING verdict is identical to
   [Eq_dom]'s, because at a total assignment [mirror] still fails exactly when the two
   values differ. So the oracle's semantics are unchanged and the only thing that moved is
   how much this propagator infers before everything is fixed -- which is precisely the
   axis [Propagator.consistency] names. It infers nothing.

   A propagator like this is SOUND. It passes test_random.ml's brute force and every model
   test, because a propagator that prunes nothing never prunes wrongly. That is the gap
   M2-T10 exists to close, stated as executable code rather than as a claim. *)
module Eq_lazy = struct
  type t = Eq_dom.t

  let name = "eq_lazy"
  let consistency = Propagator.Domain
  let vars = Eq_dom.vars

  let propagate (p : t) store =
    let dx = Store.get store p.Eq_dom.ex and dy = Store.get store p.Eq_dom.ey in
    if Domain.is_fixed dx && Domain.is_fixed dy && Domain.lo dx <> Domain.lo dy then
      Propagator.Conflict (Store.conflict store no_facts)
    else Propagator.Fixpoint
end

let pack_eq (type a) id (m : (module Propagator.S with type t = a)) (p : a) =
  Propagator.pack ~id m p

let eq_scene () =
  (* x and y each miss a different value, so domain consistency has two prunings to make
     and bounds reasoning has none: both intervals are already [0..3]. *)
  let store = mk_store [ ("x", [ 0; 1; 3 ]); ("y", [ 0; 2; 3 ]) ] in
  (store, { Eq_dom.ex = var 0; ey = var 1 })

let test_meets_its_level () =
  let store, p = eq_scene () in
  let inst = pack_eq 0 (module Eq_dom : Propagator.S with type t = Eq_dom.t) p in
  let engine = Engine.create [ inst ] in
  match Engine.propagate engine store with
  | Engine.Conflict _ -> fail "lane 1: the scene conflicted, so it tests nothing"
  | Engine.Fixpoint ->
      let vs = Engine.check_consistency engine store in
      describe_unexpected "lane 1" vs;
      check "1. a domain-consistent propagator declaring Domain reports no violation"
        (vs = [])

(* ===================================================================== *)
(* 2. THE BREAK, performed.                                              *)
(* ===================================================================== *)

let test_the_break_is_caught () =
  let store, p = eq_scene () in
  let inst = pack_eq 0 (module Eq_lazy : Propagator.S with type t = Eq_lazy.t) p in
  let engine = Engine.create [ inst ] in
  match Engine.propagate engine store with
  | Engine.Conflict _ -> fail "lane 2: the scene conflicted, so it tests nothing"
  | Engine.Fixpoint ->
      let vs = Engine.check_consistency engine store in
      (* x = 1 has no y to match it and y = 2 has no x; a domain-consistent propagator
         removes both. This one removed neither. *)
      let found = List.sort compare (names_of vs) in
      check "2. THE BREAK: pruning removed, declared Domain -- the oracle catches it"
        (found = [ ("x", 1); ("y", 2) ]);
      (* The report has to be usable without a debugger: the scene, the variable and the
         value. A violation that says only "something is wrong" sends the reader back to
         the search that produced it, which is the one thing they cannot replay. *)
      (match vs with
      | v :: _ ->
          let s = Engine.violation_to_string v in
          let has sub =
            let n = String.length sub and m = String.length s in
            let rec go i = i + n <= m && (String.sub s i n = sub || go (i + 1)) in
            go 0
          in
          check "2b. the violation names the propagator, the level and the scene"
            (has "eq_lazy" && has "declares domain" && has "x in " && has "y in ")
      | [] -> fail "2b. no violation to inspect");
      (* AND THE CONTROL FOR THE BREAK: the identical code, declaring what it actually
         achieves. Nothing about the propagator changed. It is not a bug to be weak; it is
         a bug to be weaker than declared. *)
      let quiet = relabel inst Propagator.Checking in
      check "2c. control: the same broken propagator declaring Checking is NOT a finding"
        (Engine.check_instance_consistency quiet store = [])

(* ===================================================================== *)
(* 3. THE NE LANE. Obligation (c).                                       *)
(* ===================================================================== *)

(* lib/core/prop/ne.ml declares [Value] and its header explains why: the level bounds what
   an explanation may CLAIM (docs/SPEC.md 3.2), so declaring less than the algorithm
   happens to achieve is conservative in the only direction that matters. This harness
   must pass it. That is lane 3a.

   3b is the control, and it is the single most important check in this file. It needs a
   scene where [Ne] really IS weaker than domain consistent, or "the harness would have
   caught it had it declared Domain" is untestable. ne.ml's own header names one:

     "A variable may appear more than once -- callers that care about propagation strength
      should merge duplicates first, as lib/flatzinc/compile.ml's [normalise_terms] does
      ... because two occurrences of the same unfixed variable read here as two unfixed
      terms and this propagator then declines to infer anything. Declining is sound, just
      weaker."

   So: [2x <> 4] over x in 0..3, posted WITHOUT merging. Domain consistency removes x = 2.
   [Ne] sees two unfixed terms, declines, and x = 2 survives the fixpoint. Declared
   [Value] that is correct and the oracle says nothing. Relabelled [Domain] -- one field
   of the instance record, no edit to ne.ml -- the oracle names x = 2.

   Note what this does NOT claim. On DISTINCT variables [Ne] is domain consistent, exactly
   as its header says, so relabelling THAT instance [Domain] does not go red. Lane 3c
   measures it rather than asserting the header, and a red there would be a finding
   against ne.ml's header, not against this file. *)

let test_ne_declares_value_and_passes () =
  let store = mk_store [ ("x", range 0 3); ("y", [ 1 ]) ] in
  let ne = Ne.make store [ (1, var 0); (-1, var 1) ] 0 in
  let inst = Propagator.pack ~id:0 (module Ne : Propagator.S with type t = Ne.t) ne in
  let engine = Engine.create [ inst ] in
  match Engine.propagate engine store with
  | Engine.Conflict _ -> fail "lane 3a: the scene conflicted, so it tests nothing"
  | Engine.Fixpoint ->
      check "3a-pre: the scene actually ran Ne's pruning path (x lost the value 1)"
        (not (Domain.mem (Store.get store (var 0)) 1));
      let vs = Engine.check_consistency engine store in
      describe_unexpected "lane 3a" vs;
      check "3a. ne.ml's deliberate Value declaration PASSES" (vs = []);
      (* 3c: and it is in fact domain consistent here, which is what its header claims.
         Measured, not assumed. *)
      check "3c. on distinct variables Ne is stronger than it declares (header's claim)"
        (Engine.check_instance_consistency (relabel inst Propagator.Domain) store = [])

let test_ne_control_would_have_been_caught () =
  (* 2x <> 4, x in 0..3, duplicates NOT merged. *)
  let store = mk_store [ ("x", range 0 3) ] in
  let ne = Ne.make store [ (1, var 0); (1, var 0) ] 4 in
  let inst = Propagator.pack ~id:0 (module Ne : Propagator.S with type t = Ne.t) ne in
  let engine = Engine.create [ inst ] in
  match Engine.propagate engine store with
  | Engine.Conflict _ -> fail "lane 3b: the scene conflicted, so it tests nothing"
  | Engine.Fixpoint ->
      (* The scene is only a control if [Ne] really declines here. Assert the premise
         rather than trusting the header: if a future ne.ml merges duplicates, this lane
         must go red and be rewritten, not quietly become vacuous. *)
      check "3b-pre: Ne declines on the duplicated variable, so x = 2 survives"
        (Domain.mem (Store.get store (var 0)) 2);
      let as_declared = Engine.check_consistency engine store in
      describe_unexpected "lane 3b" as_declared;
      check "3b. declaring Value, the genuinely value-consistent scene PASSES"
        (as_declared = []);
      let as_domain =
        Engine.check_instance_consistency (relabel inst Propagator.Domain) store
      in
      check
        "3b-CONTROL. THE SAME INSTANCE relabelled Domain is CAUGHT, naming x = 2 -- the \
         harness tests the DECLARATION, not soundness"
        (names_of as_domain = [ ("x", 2) ])

(* ===================================================================== *)
(* 4. The bounds(Z) reading, pinned.                                     *)
(* ===================================================================== *)

(* [Engine.check_consistency]'s header reads [Bounds] as bounds(Z): [lo] and [hi] must
   extend to a solution over the other variables' INTERVALS, holes ignored, which is what
   docs/GLOSSARY.md's "saying nothing about interior values" forces. That reading is not
   cosmetic and it is not free: read [Bounds] as bounds(D) instead and [Linear], [Int_le],
   [Int_lt], [Pb] and [Bool2int] all become findings, none of which is a bug.

   This lane makes the difference executable. [x + y = 3] over x, y in {0, 1, 3}, a scene
   at which the interval propagator below is already at its fixpoint -- it narrows nothing,
   because [lo] and [hi] of each side are exactly reachable:

     - bounds(Z) probes [lo] and [hi] only. x = 0 wants y = 3 and x = 3 wants y = 0, both
       real values of y. Supported. Nothing is owed and the oracle reports nothing.
     - bounds(D) -- which is what the [Domain] obligation runs -- probes every value, and
       x = 1 wants y = 2, which is a HOLE. Unsupported, and symmetrically for y = 1.

   So the same instance on the same scene reports nothing at [Bounds] and reports two
   values at [Domain]. That pair IS the difference between the readings.

   The [Domain] relabel is the bounds(D) answer, so the pair of lanes below is the
   difference itself: same instance, same scene, one reports and one does not. If SPEC 3.2
   is ever amended to say which reading is normative, THIS is the test that has to move,
   and it will say so by going red. *)

module Sum_eq_bounds = struct
  type t = { sx : Var.t; sy : Var.t; total : int }

  let name = "sum_eq_bounds_z"

  (* Interval reasoning only, and deliberately: it never looks at a hole. *)
  let consistency = Propagator.Bounds
  let vars p = [ p.sx; p.sy ]

  let narrow store a b total =
    let db = Store.get store b in
    let lo = total - Domain.hi db and hi = total - Domain.lo db in
    match Store.set_lo store a lo no_facts with
    | Store.Conflict e -> Propagator.Conflict e
    | _ -> (
        match Store.set_hi store a hi no_facts with
        | Store.Conflict e -> Propagator.Conflict e
        | _ -> Propagator.Fixpoint)

  let propagate p store =
    match narrow store p.sx p.sy p.total with
    | Propagator.Conflict e -> Propagator.Conflict e
    | Propagator.Fixpoint -> narrow store p.sy p.sx p.total
end

let test_bounds_is_bounds_z () =
  let store = mk_store [ ("x", [ 0; 1; 3 ]); ("y", [ 0; 1; 3 ]) ] in
  let p = { Sum_eq_bounds.sx = var 0; sy = var 1; total = 3 } in
  let inst =
    Propagator.pack ~id:0
      (module Sum_eq_bounds : Propagator.S with type t = Sum_eq_bounds.t)
      p
  in
  let engine = Engine.create [ inst ] in
  match Engine.propagate engine store with
  | Engine.Conflict _ -> fail "lane 4: the scene conflicted, so it tests nothing"
  | Engine.Fixpoint ->
      (* The premise of the whole lane: the interval propagator is at a fixpoint with
         both domains still three values wide and the hole at 2 still there. If a future
         change made this scene collapse to a fixed point, the lane would go green for
         the wrong reason, so the shape is asserted rather than assumed. *)
      check "4-pre: the fixpoint kept both domains at {0,1,3}, hole at 2 included"
        (Domain.to_list (Store.get store (var 0)) = [ 0; 1; 3 ]
        && Domain.to_list (Store.get store (var 1)) = [ 0; 1; 3 ]);
      let as_bounds = Engine.check_consistency engine store in
      describe_unexpected "lane 4" as_bounds;
      check "4. bounds(Z): an interval propagator declaring Bounds reports nothing"
        (as_bounds = []);
      let as_domain =
        Engine.check_instance_consistency (relabel inst Propagator.Domain) store
      in
      check
        "4-CONTROL. the same scene under the Domain obligation DOES report -- the \
         bounds(Z)/bounds(D) choice is load-bearing and tested, not assumed"
        (List.sort compare (names_of as_domain) = [ ("x", 1); ("y", 1) ])

(* ===================================================================== *)
(* 5. Levels that carry no obligation.                                   *)
(* ===================================================================== *)

let test_no_obligation_levels () =
  (* The broken propagator from lane 2 -- which is weaker than every level above
     [Checking] -- passes under [Value] and under [Checking], and that is correct.
     docs/GLOSSARY.md: [Value] claims "nothing about the values it leaves behind". A
     harness that invented a support obligation for [Value] would be reading a
     declaration as saying more than it says, which is the mirror image of the bug this
     task exists to catch. *)
  let store, p = eq_scene () in
  let inst = pack_eq 0 (module Eq_lazy : Propagator.S with type t = Eq_lazy.t) p in
  let engine = Engine.create [ inst ] in
  match Engine.propagate engine store with
  | Engine.Conflict _ -> fail "lane 5: the scene conflicted, so it tests nothing"
  | Engine.Fixpoint ->
      check "5a. Value carries no support obligation"
        (Engine.check_instance_consistency (relabel inst Propagator.Value) store = []);
      check "5b. Checking carries no support obligation"
        (Engine.check_instance_consistency (relabel inst Propagator.Checking) store = []);
      check "5c. and Domain on the very same instance still reports"
        (Engine.check_instance_consistency (relabel inst Propagator.Domain) store <> [])

(* ===================================================================== *)
(* 6. The budget, and that a skip is not a pass.                         *)
(* ===================================================================== *)

let test_a_skip_is_counted_not_passed () =
  (* Eight variables of six values each is 6^8 tuples, far over the default cap of 4096.
     Nothing here is wide -- the widest domain is SIX -- which is the point: brute force
     blows up on the number of variables in a scope, not on the width of any one of them,
     and the cap has to be about the product. *)
  let specs = List.init 8 (fun i -> (Printf.sprintf "v%d" i, range 0 5)) in
  let store = mk_store specs in
  let p = { Eq_dom.ex = var 0; ey = var 1 } in
  (* Declare a scope of all eight even though the mock reads two: the point is the
     product the oracle would have to enumerate. *)
  let module Wide = struct
    type t = Eq_dom.t

    let name = "wide_scope"
    let consistency = Propagator.Domain
    let vars _ = List.init 8 var
    let propagate = Eq_lazy.propagate
  end in
  let inst = pack_eq 0 (module Wide : Propagator.S with type t = Wide.t) p in
  Engine.reset_oracle_stats ();
  let vs = Engine.check_instance_consistency inst store in
  let _, checked, tuples, skipped = Engine.oracle_stats () in
  check "6a. an over-budget instance reports no violation ..." (vs = []);
  check "6b. ... and enumerates nothing, so the silence is not evidence" (tuples = 0);
  check "6c. ... and is COUNTED as a skip, which is how a reader can tell"
    (skipped = 1 && checked = 0);
  (* And it is a budget, not a wall: raised, the same instance IS checked. Asserted
     against the default rather than by re-reading the environment, because
     [Debug.consistency_cap] is read once at module initialisation, like every other gate
     in lib/core/debug.ml. *)
  check "6d. the cap is the documented default" (Debug.consistency_cap = 4096)

(* ===================================================================== *)
(* 7. The oracle does not perturb the search it audits.                  *)
(* ===================================================================== *)

let test_oracle_is_non_invasive () =
  let store, p = eq_scene () in
  let inst = pack_eq 0 (module Eq_lazy : Propagator.S with type t = Eq_lazy.t) p in
  let engine = Engine.create [ inst ] in
  match Engine.propagate engine store with
  | Engine.Conflict _ -> fail "lane 7: the scene conflicted, so it tests nothing"
  | Engine.Fixpoint ->
      let snap = Store.snapshot store in
      let trail = Store.trail_length store in
      let level = Store.level store in
      let vs = Engine.check_consistency engine store in
      check "7-pre: the lane audits something that actually reports" (vs <> []);
      (* Every tuple the oracle tries runs a REAL propagator, which can prune and can
         conflict. It does it on scratch stores, so none of that reaches here. If this
         ever fails, a BAGUETTE_CONSISTENCY run and a plain run would answer differently
         and emit different proofs, and the audit would be unusable over the suite it is
         meant to audit. *)
      check "7a. the audited store's domains are untouched"
        (Store.same_domains store snap);
      check "7b. its trail is untouched" (Store.trail_length store = trail);
      check "7c. its decision level is untouched" (Store.level store = level)

(* ===================================================================== *)
(* 8. The real propagators, at a real fixpoint, through the engine.      *)
(* ===================================================================== *)

(* Lanes 1-7 are about the oracle. This one is about the code it audits: the shipped
   [Linear] and [Ne], several instances, one engine, one fixpoint. It is the in-process
   echo of the run over test/models/, which is where the real coverage comes from
   (BAGUETTE_CONSISTENCY=1 scripts/run_model_tests.sh); this lane exists so that a
   regression is caught by `dune runtest` rather than only by remembering to set an
   environment variable. *)
let test_real_propagators_meet_their_levels () =
  let store = mk_store [ ("a", range 0 4); ("b", range 0 4); ("c", range 0 4) ] in
  let lin1 = Linear.make ~row_id:(unrendered_row ()) store [ (1, var 0); (1, var 1) ] 5 in
  let lin2 =
    Linear.make ~row_id:(unrendered_row ()) store [ (-1, var 1); (1, var 2) ] (-1)
  in
  let ne = Ne.make store [ (1, var 0); (-1, var 2) ] 0 in
  let insts =
    [
      Propagator.pack ~id:0 (module Linear : Propagator.S with type t = Linear.t) lin1;
      Propagator.pack ~id:1 (module Linear : Propagator.S with type t = Linear.t) lin2;
      Propagator.pack ~id:2 (module Ne : Propagator.S with type t = Ne.t) ne;
    ]
  in
  let engine = Engine.create insts in
  match Engine.propagate engine store with
  | Engine.Conflict _ -> fail "lane 8: the scene conflicted, so it tests nothing"
  | Engine.Fixpoint ->
      Engine.reset_oracle_stats ();
      let vs = Engine.check_consistency engine store in
      describe_unexpected "lane 8" vs;
      let _, checked, tuples, skipped = Engine.oracle_stats () in
      (* The count is the anti-vacuity guard. "No violations" over zero instance-checks is
         the failure this reports as a pass, so the checks are asserted to have happened. *)
      check "8-pre: the lane actually enumerated (it is not vacuously green)"
        (checked >= 2 && tuples > 0 && skipped = 0);
      check "8. shipped Linear and Ne meet their declared levels at a real fixpoint"
        (vs = [])

(* ===================================================================== *)

let () =
  test_meets_its_level ();
  test_the_break_is_caught ();
  test_ne_declares_value_and_passes ();
  test_ne_control_would_have_been_caught ();
  test_bounds_is_bounds_z ();
  test_no_obligation_levels ();
  test_a_skip_is_counted_not_passed ();
  test_oracle_is_non_invasive ();
  test_real_propagators_meet_their_levels ();
  Printf.printf "\ntest_consistency: %d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
