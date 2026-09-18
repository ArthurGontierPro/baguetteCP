(* Unit tests for lib/core/analysis.ml -- the implication graph and the cut, as data
   (M2-L2, D-0044 and its 2026-09-18 amendment).

   The four tests the roadmap row requires are (a) the oracle, (b) the stopping criterion
   as a named component, (c) the [entry.prop] break, and (d) holes. Each is a section
   below and each says in its header what it would catch.

   Two things constrain how the scenes are built, and both are deliberate:

     - **Nothing here constructs a [Reason.justified].** Every domain change comes out of
       a real propagator ([Linear], [Ne.Int_ne]) run under [Store.with_running]. A
       parallel session is adding a field to that record (D-0043) and a test that built
       one by hand would break on a change that has nothing to do with it.

     - **A decision is a posted single-term row, not a [Store.set_lo] with a hand-made
       decision reason.** [Linear.make ~row_id store [ (-1, x) ] (-3)] pushes [x >= 3] and
       its reason is EMPTY, because [row_snaps ~exclude] drops the only term -- which is
       exactly the shape [Search]'s decision push has ([Reason.none]), and exactly what
       [Analysis] treats as a root. So the scenes get real assumptions without this file
       ever naming [Reason.because].

   Domains are 0..4 throughout. D-0028 makes the order encoding width-proportional and
   these scenes emit no proof at all, but the declared width is also the brute-force
   oracle's search space, and 5^5 = 3125 is the whole of it. *)

module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Var = Baguette_core.Var
module Reason = Baguette_core.Reason
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Ne = Baguette_core.Ne
module Engine = Baguette_core.Engine
module Analysis = Baguette_core.Analysis

let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* ------------------------------------------------------------------- driving a scene *)

(* A propagator instance plus the id the store will stamp its entries with. They are the
   same number in every scene but one: test (c) drives the whole scene with one step's
   [s_id] set one high, which is the only way to get a wrong [entry.prop] past a store
   that never takes an id from a propagator (M2-T7). *)
type step = { s_id : int; s_inst : Propagator.instance }

let linear_step ~id store terms rhs =
  let lin = Linear.make ~row_id:(1000 + id) store terms rhs in
  {
    s_id = id;
    s_inst = Propagator.pack ~id (module Linear : Propagator.S with type t = Linear.t) lin;
  }

let ne_step ~id store x y =
  let ne = Ne.Int_ne.make store x y in
  {
    s_id = id;
    s_inst =
      Propagator.pack ~id (module Ne.Int_ne : Propagator.S with type t = Ne.Int_ne.t) ne;
  }

let restamp s id = { s with s_id = id }

(* A deterministic mini-engine: run the steps in order, repeating while anything changed,
   and return the first conflict. Used instead of [Engine] so that a scene can be built
   with one step's stamp deliberately wrong -- [Engine.check_attribution] refuses that
   route on purpose (M2-T7), which is the behaviour to preserve, so the break goes around
   the engine rather than through it. [test_engine_agrees] below runs the same scene
   through the real engine so that nothing here rests on the mini one. *)
let run_steps store steps =
  let rec pass () =
    let before = Store.trail_length store in
    let rec go = function
      | [] -> if Store.trail_length store > before then pass () else None
      | s :: rest -> (
          match
            Store.with_running store s.s_id (fun () -> s.s_inst.Propagator.run store)
          with
          | Propagator.Conflict c -> Some c
          | Propagator.Fixpoint -> go rest)
    in
    go steps
  in
  pass ()

let vars_of_table steps id =
  let rec go = function
    | [] -> None
    | s :: rest ->
        if s.s_inst.Propagator.id = id then Some s.s_inst.Propagator.inst_vars
        else go rest
  in
  go steps

(* ------------------------------------------------------------------- the oracle *)

(* Brute force over the declared box. [sat] is the conjunction being tested. *)
let satisfiable ~n ~lo ~hi ~sat =
  let a = Array.make n lo in
  let rec go i =
    if i = n then sat a
    else
      let found = ref false in
      for v = lo to hi do
        a.(i) <- v;
        if (not !found) && go (i + 1) then found := true
      done;
      !found
  in
  go 0

(* A cut's facts as a predicate on an assignment. This is the half of test (a) that needs
   the model: [Analysis.holds_on_trail] is the other half. *)
let facts_hold store facts a =
  List.for_all
    (fun f ->
      match Store.var_named store (Reason.fact_owner f) with
      | None -> false
      | Some v ->
          let x = a.(Var.to_int v) in
          if Reason.fact_is_lower f then x >= Analysis.fact_value f
          else x <= Analysis.fact_value f)
    facts

(* ===================================================================== *)
(* Scene 1: a reconverging graph with a hole in it.                      *)
(*                                                                       *)
(*   vars a b c d e, all 0..4, indices 0..4                              *)
(*   model   R1  a - b <= 0     (b >= a)                                 *)
(*           R2  b - c <= 0     (c >= b)                                 *)
(*           R3  b - d <= 0     (d >= b)                                 *)
(*           R4  c + d <= 6                                              *)
(*           N   d <> e                                                  *)
(*   level 1  assume e = 3   (two single-term rows)                      *)
(*            -> N punches a HOLE in d at 3                              *)
(*   level 2  assume a >= 3                                              *)
(*            -> b >= 3, c >= 3, d >= 3 which SETTLES to 4 over the hole  *)
(*            -> R4 sees 3 + 4 = 7 > 6 and fails                         *)
(*                                                                       *)
(* The reconvergence (b implies both c and d) is what makes 1UIP stop at  *)
(* a real UIP -- b >= 3 -- rather than at the assumption, so the cut is   *)
(* not just the branch nogood M1 already had.                            *)
(* ===================================================================== *)

let names1 = [| "a"; "b"; "c"; "d"; "e" |]
let va = Var.of_int 0
let vb = Var.of_int 1
let vc = Var.of_int 2
let vd = Var.of_int 3
let ve = Var.of_int 4

let model1 a =
  a.(0) - a.(1) <= 0
  && a.(1) - a.(2) <= 0
  && a.(1) - a.(3) <= 0
  && a.(2) + a.(3) <= 6
  && a.(3) <> a.(4)

(* Ids are contiguous from 0 and in list order: [Engine] sizes its trigger array by
   them, so a sparse id set makes [Engine.create] throw rather than fail a check. *)
let build_scene1 ?(break : (int * int) option) () =
  let store = Store.create ~names:names1 ~domains:(Array.make 5 (Domain.make 0 4)) in
  let r1 = linear_step ~id:0 store [ (1, va); (-1, vb) ] 0 in
  let r2 = linear_step ~id:1 store [ (1, vb); (-1, vc) ] 0 in
  let r3 = linear_step ~id:2 store [ (1, vb); (-1, vd) ] 0 in
  let r4 = linear_step ~id:3 store [ (1, vc); (1, vd) ] 6 in
  let n = ne_step ~id:4 store vd ve in
  let model = [ r1; r2; r3; r4; n ] in
  let a_e_lo = linear_step ~id:5 store [ (-1, ve) ] (-3) in
  let a_e_hi = linear_step ~id:6 store [ (1, ve) ] 3 in
  let a_a = linear_step ~id:7 store [ (-1, va) ] (-3) in
  let all = model @ [ a_e_lo; a_e_hi; a_a ] in
  let apply_break steps =
    match break with
    | None -> steps
    | Some (target, stamp) ->
        List.map
          (fun s -> if s.s_inst.Propagator.id = target then restamp s stamp else s)
          steps
  in
  (* Level 0: nothing moves. Level 1: e is assumed 3 and the hole appears. Level 2: a is
     assumed >= 3 and the conflict follows. *)
  let c0 = run_steps store (apply_break model) in
  Store.new_level store;
  let c1 = run_steps store (apply_break (a_e_lo :: a_e_hi :: model)) in
  Store.new_level store;
  let c2 = run_steps store (apply_break (a_a :: model)) in
  (store, all, c0, c1, c2)

let scene1 () =
  match build_scene1 () with
  | store, all, None, None, Some c -> (store, all, c)
  | _ -> failwith "test_analysis: scene 1 did not reach its conflict where it should"

let cut1 criterion =
  let store, all, c = scene1 () in
  match Analysis.analyse store c ~vars_of:(vars_of_table all) ~criterion with
  | Ok t -> (store, t)
  | Error e -> failwith ("test_analysis: scene 1 " ^ Analysis.error_to_string e)

(* -------------------------------------------------- the scene is the scene we meant *)

let test_scene1_shape () =
  let store, _, c = scene1 () in
  check "scene 1: the conflict is at level 2" (Store.level store = 2);
  check "scene 1: the trail is the seven entries the comment draws"
    (Store.trail_length store = 7);
  check "scene 1: the conflict's own reason is c >= 3 and d >= 4"
    (Reason.to_string c.Store.c_reason = "c>=3 d>=4");
  check "scene 1: d settled over the hole at 3, so its bound is 4 and not 3"
    (Domain.lo (Store.get store vd) = 4 && not (Domain.mem (Store.get store vd) 3));
  check "scene 1: the conflicting row is R4" (c.Store.c_prop = 3)

(* ===================================================================== *)
(* (a) THE ORACLE.                                                       *)
(*                                                                       *)
(* Two halves, and the second is the one that matters: every literal in   *)
(* the cut holds on the trail, AND the model together with the cut is     *)
(* unsatisfiable by brute force. Non-vacuity is checked too -- a cut is   *)
(* only evidence of anything if the model ALONE is satisfiable, which it  *)
(* is: the assumptions are posted rows and are deliberately NOT part of   *)
(* the model the oracle enumerates.                                      *)
(* ===================================================================== *)

let oracle_says_valid store t =
  satisfiable ~n:5 ~lo:0 ~hi:4 ~sat:(fun a ->
      model1 a && facts_hold store (Analysis.facts t) a)
  = false

let test_oracle_non_vacuous () =
  check "(a) the model alone is satisfiable, so a cut over it is evidence of something"
    (satisfiable ~n:5 ~lo:0 ~hi:4 ~sat:model1)

let test_oracle_every_criterion () =
  List.iter
    (fun (criterion : Analysis.criterion) ->
      let store, t = cut1 criterion in
      let tag = criterion.Analysis.crit_name in
      check
        (Printf.sprintf "(a) %s: every literal of the cut holds on the trail" tag)
        (Analysis.holds_on_trail store t);
      check
        (Printf.sprintf "(a) %s: model + cut is UNSAT by brute force" tag)
        (oracle_says_valid store t);
      check (Printf.sprintf "(a) %s: the cut is non-empty" tag) (Analysis.facts t <> []))
    Analysis.criteria

(* The negation of the oracle, so that a passing oracle is known to be capable of
   failing: drop one literal from the 1UIP cut and the remainder must NOT be a valid
   nogood. Without this, "model + cut is UNSAT" would also pass for a cut that is simply
   too large to be interesting. *)
let test_oracle_can_fail () =
  let store, t = cut1 Analysis.one_uip in
  let weakened = List.tl (Analysis.facts t) in
  check "(a) break: the 1UIP cut with its first literal dropped is NOT a valid nogood"
    (satisfiable ~n:5 ~lo:0 ~hi:4 ~sat:(fun a -> model1 a && facts_hold store weakened a))

(* ===================================================================== *)
(* (b) THE STOPPING CRITERION, AS A NAMED COMPONENT.                     *)
(*                                                                       *)
(* The 1UIP rule is asserted THROUGH [postcondition_holds], which reads   *)
(* the criterion's own postcondition. It is never asserted of a cut in    *)
(* general, because for the PB path it is false: a PB constraint          *)
(* propagates by slack, so a cut carrying several conflict-level literals *)
(* can still be asserting (D-0044 amendment, Le Berre et al. 2107.13085). *)
(* [conflict_side]'s cut carries two of them here and is ACCEPTED, which  *)
(* is the M2-L6 shape; the last check below is the proof that writing the *)
(* 1UIP rule one altitude higher would have reddened for it.             *)
(* ===================================================================== *)

let test_criterion_postconditions () =
  List.iter
    (fun (criterion : Analysis.criterion) ->
      let _, t = cut1 criterion in
      let tag = criterion.Analysis.crit_name in
      check
        (Printf.sprintf "(b) %s: the cut satisfies ITS OWN postcondition" tag)
        (Analysis.postcondition_holds criterion t);
      check
        (Printf.sprintf "(b) %s: the cut records which criterion produced it" tag)
        (t.Analysis.criterion_name = tag);
      check
        (Printf.sprintf "(b) %s: the walk stopped because the criterion said so" tag)
        t.Analysis.stopped_by_criterion)
    Analysis.criteria

let test_one_uip_stops_at_a_real_uip () =
  let _, t = cut1 Analysis.one_uip in
  check "(b) 1UIP: exactly one literal from the conflict level"
    (List.length (Analysis.at_level t t.Analysis.conflict_level) = 1);
  check "(b) 1UIP: the cut is b >= 3 with the hole's two facts folded in"
    (Reason.to_string (Analysis.facts t) = "b>=3 e>=3 e<=3");
  check "(b) 1UIP: it stopped at a UIP strictly inside the level, not at the assumption"
    (List.for_all (fun n -> not n.Analysis.root) (Analysis.at_level t 2));
  check "(b) 1UIP: two resolution steps, one per reconverging branch"
    (t.Analysis.resolutions = 2);
  check "(b) 1UIP: the decision cut is a different, weaker cut over the assumption"
    (let _, d = cut1 Analysis.decision_cut in
     Reason.to_string (Analysis.facts d) = "e>=3 e<=3 a>=3"
     && List.for_all (fun n -> n.Analysis.root) (Analysis.at_level d 2))

let test_conflict_side_carries_several_conflict_level_literals () =
  let store, t = cut1 Analysis.conflict_side in
  check "(b) conflict-side: the cut carries TWO conflict-level literals"
    (List.length (Analysis.at_level t t.Analysis.conflict_level) = 2);
  check "(b) conflict-side: and is accepted -- oracle valid, own postcondition holds"
    (oracle_says_valid store t && Analysis.postcondition_holds Analysis.conflict_side t);
  (* THE check this row exists to get right. If the 1UIP rule had been written as an
     invariant of [Analysis.t] rather than as [one_uip]'s postcondition, this is the line
     that would have gone red -- and it would go red for M2-L6's slack criterion in
     exactly the same way. *)
  check
    "(b) SCOPING: 1UIP's postcondition is FALSE of the conflict-side cut, and that is \
     correct, not a bug"
    (not (Analysis.postcondition_holds Analysis.one_uip t))

let test_backjump_level_is_recorded_for_M2_L3 () =
  let _, t = cut1 Analysis.one_uip in
  check "(b) the cut records a level per literal (I-S4 is M2-L3's debt, not this row's)"
    (Analysis.cited_levels t = [ 1; 2 ]);
  check "(b) the backjump level is the second-highest level cited"
    (Analysis.backjump_level t = 1)

(* ===================================================================== *)
(* (c) THE BREAK: stamp [entry.prop] one high.                           *)
(*                                                                       *)
(* M2-T7 stamps the field from the engine so that no propagator can name  *)
(* the wrong id; this proves the WALK reads it back. Two breaks, and the  *)
(* second is the honest one -- see its comment.                          *)
(* ===================================================================== *)

let analyse_broken ~target ~stamp criterion =
  match build_scene1 ~break:(target, stamp) () with
  | store, all, _, _, Some c ->
      (store, all, Analysis.analyse store c ~vars_of:(vars_of_table all) ~criterion)
  | _ -> failwith "test_analysis: the broken scene did not reach its conflict"

let test_misattribution_is_caught () =
  (* R2 made the entry for c. Stamped one high it claims R3, which watches b and d and
     not c -- so the graph says a constraint implied a bound it cannot see. *)
  let _, _, r = analyse_broken ~target:1 ~stamp:2 Analysis.one_uip in
  check "(c) a mis-stamped entry.prop stops the walk instead of producing a cut"
    (match r with Error (Analysis.Misattributed _) -> true | _ -> false);
  check "(c) and the error names the entry, the id it claimed and the variable"
    (match r with
    | Error (Analysis.Misattributed { claimed; var; _ }) -> claimed = 2 && var = "c"
    | _ -> false);
  check "(c) the same scene unbroken produces a cut, so the break is what changed it"
    (match
       let store, all, c = scene1 () in
       ignore store;
       Analysis.analyse store c ~vars_of:(vars_of_table all) ~criterion:Analysis.one_uip
     with
    | Ok _ -> true
    | Error _ -> false)

let test_misattribution_that_is_not_caught () =
  (* R3 made the entry for d. One high is R4 -- which DOES watch d, because it is the row
     that then conflicted on it. So the attribution check cannot see this one, and saying
     so is the point of this test: "one high" is only detectable when the neighbouring id
     does not happen to watch the same variable, and with contiguous ids over a dense row
     set it often does. [Engine.check_attribution] (M2-T7) has exactly the same blind
     spot for exactly the same reason.

     What DOES change is the data the cut hands to M2-L3: the antecedent list names R4
     twice and never names R3, so the explicit derivation D-0040 requires would be built
     over the wrong model row. That is the observable difference, and it is asserted
     here rather than left as a comment. *)
  let _, _, r = analyse_broken ~target:2 ~stamp:3 Analysis.one_uip in
  let _, truthful = cut1 Analysis.one_uip in
  check "(c) LIMIT: a mis-stamp onto a row that also watches the variable is NOT caught"
    (match r with Ok _ -> true | Error _ -> false);
  check "(c) LIMIT: but the antecedents are then wrong, which is what M2-L3 would emit"
    (match r with
    | Ok t ->
        t.Analysis.antecedents <> truthful.Analysis.antecedents
        && (not (List.mem 2 t.Analysis.antecedents))
        && List.mem 2 truthful.Analysis.antecedents
    | Error _ -> false);
  check "(c) LIMIT: and the cut's literals are unchanged, so the oracle cannot see it"
    (match r with
    | Ok t ->
        Reason.to_string (Analysis.facts t) = Reason.to_string (Analysis.facts truthful)
    | Error _ -> false)

let test_antecedents_are_the_rows_the_cut_rests_on () =
  let _, t = cut1 Analysis.one_uip in
  check "(c) the antecedents are the conflicting row, both resolved rows, and the hole's"
    (t.Analysis.antecedents = [ 3; 2; 4; 1 ])

(* ===================================================================== *)
(* (d) HOLES.                                                            *)
(*                                                                       *)
(* An int_ne removal claims a CLAUSE (Encoding.ne_clause_lits, M1-T56),   *)
(* not a literal, so it is non-asserting and cannot be a graph node in    *)
(* the usual way; the rule is to fold its reason into the bound move that *)
(* consumed it. The first two checks assert the rule FIRED and names the  *)
(* right hole. The third is the one that makes them mean something: with  *)
(* the folded facts removed the cut is no longer a valid nogood, so the   *)
(* fold is load-bearing and a silent drop would be caught by (a).         *)
(* ===================================================================== *)

let test_hole_fold_fired () =
  let _, t = cut1 Analysis.one_uip in
  check "(d) the fold fired: exactly one hole was folded into a bound move"
    (List.length t.Analysis.folds = 1);
  check
    "(d) and it is d's hole at 3, punched by the int_ne instance, folded into d's settle"
    (match t.Analysis.folds with
    | [ f ] ->
        f.Analysis.fold_var = "d" && f.Analysis.fold_value = 3 && f.Analysis.fold_prop = 4
    | _ -> false);
  check "(d) the folded facts are in the cut, at the level the hole was punched at"
    (List.length (Analysis.at_level t 1) = 2)

let test_hole_fold_is_load_bearing () =
  let store, t = cut1 Analysis.one_uip in
  (* The cut without the hole's contribution: exactly what a walk that treated the
     settle as an ordinary bound move would have produced. *)
  let without_hole =
    List.filter (fun f -> Reason.fact_owner f <> "e") (Analysis.facts t)
  in
  check "(d) BREAK: without the folded facts the cut is NOT a valid nogood"
    (satisfiable ~n:5 ~lo:0 ~hi:4 ~sat:(fun a ->
         model1 a && facts_hold store without_hole a));
  check "(d) so the fold is load-bearing and dropping it silently would fail (a)"
    (without_hole <> Analysis.facts t)

(* ===================================================================== *)
(* Scene 2: the support fallback, and a factless root.                   *)
(*                                                                       *)
(*   vars x y v, 0..4                                                     *)
(*   model   S1  x - y <= 0     (y >= x)                                  *)
(*           S2  v - x <= -1    (x >= v + 1)                              *)
(*           S3  y + x <= 5                                               *)
(*   level 1  assume x >= 2  -> y >= 2                                    *)
(*            assume v >= 3  -> x >= 4   (x's lower bound moves AGAIN)    *)
(*            S3 sees 2 + 4 = 6 > 5 and fails                             *)
(*                                                                       *)
(* Resolving y >= 2 asks "what established x >= 2?" from a point BELOW    *)
(* the entry that later pushed x to 4. Store.lo_support names that later  *)
(* entry, so the O(1) answer is the wrong one here and the downward scan  *)
(* has to run -- which is the branch in [support_of] that would otherwise *)
(* never execute in this suite. The second assumption is also a root that *)
(* is not a level start, so it exercises the [factless] report.           *)
(* ===================================================================== *)

let names2 = [| "x"; "y"; "v" |]
let vx = Var.of_int 0
let vy = Var.of_int 1
let vv = Var.of_int 2
let model2 a = a.(0) - a.(1) <= 0 && a.(2) - a.(0) <= -1 && a.(1) + a.(0) <= 5

let scene2 () =
  let store = Store.create ~names:names2 ~domains:(Array.make 3 (Domain.make 0 4)) in
  let s1 = linear_step ~id:0 store [ (1, vx); (-1, vy) ] 0 in
  let s2 = linear_step ~id:1 store [ (1, vv); (-1, vx) ] (-1) in
  let s3 = linear_step ~id:2 store [ (1, vy); (1, vx) ] 5 in
  let a_x = linear_step ~id:3 store [ (-1, vx) ] (-2) in
  let a_v = linear_step ~id:4 store [ (-1, vv) ] (-3) in
  let all = [ s1; s2; s3; a_x; a_v ] in
  Store.new_level store;
  (* Each step runs ONCE, in this order, rather than to a fixpoint. The point of the
     scene is a stale fact: y >= 2 is read off x >= 2, and only afterwards does x move
     again. Running s1 to a fixpoint would re-derive y from the newer bound and there
     would be nothing stale left to resolve. *)
  let c =
    List.fold_left
      (fun acc s ->
        match acc with
        | Some _ -> acc
        | None -> (
            match
              Store.with_running store s.s_id (fun () -> s.s_inst.Propagator.run store)
            with
            | Propagator.Conflict c -> Some c
            | Propagator.Fixpoint -> None))
      None [ a_x; s1; a_v; s2; s3 ]
  in
  match c with
  | Some c -> (store, all, c)
  | None -> failwith "test_analysis: scene 2 did not reach its conflict"

let test_scene2_scan_fallback () =
  let store, all, c = scene2 () in
  check "scene 2: x's lower bound moved twice, so lo_support names the later entry"
    (Store.lo_support store vx = 4 && Domain.lo (Store.get store vx) = 4);
  match
    Analysis.analyse store c ~vars_of:(vars_of_table all) ~criterion:Analysis.decision_cut
  with
  | Error e -> check ("scene 2: " ^ Analysis.error_to_string e) false
  | Ok t ->
      check "scene 2: the O(1) lo_support/hi_support path answers most of the walk"
        (t.Analysis.o1_supports >= 3);
      check
        "scene 2: and the downward-scan fallback runs, because the O(1) answer is the \
         wrong entry for a frozen fact"
        (t.Analysis.scanned_supports >= 1);
      check "scene 2: the cut is over the two assumptions"
        (Reason.to_string (Analysis.facts t) = "v>=3 x>=2");
      check "scene 2: oracle -- model + cut is UNSAT by brute force"
        (satisfiable ~n:3 ~lo:0 ~hi:4 ~sat:(fun a ->
             model2 a && facts_hold store (Analysis.facts t) a)
        = false);
      check "scene 2: oracle is non-vacuous -- the model alone is satisfiable"
        (satisfiable ~n:3 ~lo:0 ~hi:4 ~sat:model2);
      check "scene 2: every literal of the cut holds on the trail"
        (Analysis.holds_on_trail store t);
      check "scene 2: decision-cut's own postcondition holds"
        (Analysis.postcondition_holds Analysis.decision_cut t);
      (* I-P5's shape, reported rather than assumed away: the second assumption is a root
         that rests on no facts and is NOT the entry that opened the level, so it is not a
         decision. A search pushing one decision per level never makes one; [Store.remove]
         and [Store.fix] recording [no_facts] silently (M1-T9 to M1-T17) did. *)
      check "scene 2: the non-decision factless root is REPORTED, not silently dropped"
        (t.Analysis.factless = [ 2 ]);
      (* And the honest half of (b): 1UIP has nothing to say about a level carrying two
         assumptions, so its walk runs out of expandable nodes before its criterion is
         met. The flag says so rather than the cut pretending. *)
      let u =
        Analysis.analyse store c ~vars_of:(vars_of_table all) ~criterion:Analysis.one_uip
      in
      check
        "scene 2: 1UIP runs out of expandable nodes here and SAYS SO rather than \
         claiming its postcondition"
        (match u with
        | Ok t ->
            (not t.Analysis.stopped_by_criterion)
            && not (Analysis.postcondition_holds Analysis.one_uip t)
        | Error _ -> false)

(* ===================================================================== *)
(* The real engine reaches the same cut.                                 *)
(*                                                                       *)
(* Everything above drives propagators through a mini-engine so that the  *)
(* (c) break can get past [Engine.check_attribution]. This check exists   *)
(* so that nothing in this file rests on the mini one: the same scene     *)
(* built by [Engine.propagate] -- different wake order, real attribution  *)
(* checking -- must give a cut that passes the same oracle.               *)
(* ===================================================================== *)

let test_engine_agrees () =
  let store = Store.create ~names:names1 ~domains:(Array.make 5 (Domain.make 0 4)) in
  let r1 = linear_step ~id:0 store [ (1, va); (-1, vb) ] 0 in
  let r2 = linear_step ~id:1 store [ (1, vb); (-1, vc) ] 0 in
  let r3 = linear_step ~id:2 store [ (1, vb); (-1, vd) ] 0 in
  let r4 = linear_step ~id:3 store [ (1, vc); (1, vd) ] 6 in
  let n = ne_step ~id:4 store vd ve in
  let a_e_lo = linear_step ~id:5 store [ (-1, ve) ] (-3) in
  let a_e_hi = linear_step ~id:6 store [ (1, ve) ] 3 in
  let a_a = linear_step ~id:7 store [ (-1, va) ] (-3) in
  let model = [ r1; r2; r3; r4; n ] in
  let all = model @ [ a_e_lo; a_e_hi; a_a ] in
  let insts steps = List.map (fun s -> s.s_inst) steps in
  let e0 = Engine.create (insts model) in
  let e1 = Engine.create (insts (model @ [ a_e_lo; a_e_hi ])) in
  let e2 = Engine.create (insts all) in
  let step engine = Engine.propagate engine store in
  match step e0 with
  | Engine.Conflict _ -> check "engine: scene 1 must not fail at level 0" false
  | Engine.Fixpoint -> (
      Store.new_level store;
      match step e1 with
      | Engine.Conflict _ -> check "engine: scene 1 must not fail at level 1" false
      | Engine.Fixpoint -> (
          Store.new_level store;
          match step e2 with
          | Engine.Fixpoint ->
              check "engine: scene 1 must reach its conflict at level 2" false
          | Engine.Conflict c -> (
              match
                Analysis.analyse store c ~vars_of:(vars_of_table all)
                  ~criterion:Analysis.one_uip
              with
              | Error e -> check ("engine: " ^ Analysis.error_to_string e) false
              | Ok t ->
                  check "engine: the cut passes the same oracle"
                    (oracle_says_valid store t);
                  check "engine: every literal of the cut holds on the trail"
                    (Analysis.holds_on_trail store t);
                  check "engine: 1UIP's postcondition holds"
                    (Analysis.postcondition_holds Analysis.one_uip t);
                  check "engine: the hole fold fired here too"
                    (List.length t.Analysis.folds = 1);
                  check "engine: the cut is the same one the mini-engine reached"
                    (let _, m = cut1 Analysis.one_uip in
                     Reason.to_string (Analysis.facts t)
                     = Reason.to_string (Analysis.facts m)))))

(* ===================================================================== *)
(* Determinism: a cut is naturally a set, and a set iterated in hash      *)
(* order is how the gate's byte-identical requirement gets broken. Ten    *)
(* runs of the same scene must give the same cut, in the same order,      *)
(* with the same counters.                                               *)
(* ===================================================================== *)

let test_determinism () =
  let render () =
    let _, t = cut1 Analysis.one_uip in
    Printf.sprintf "%s|%s|%s|%d" (Analysis.to_string t)
      (String.concat "," (List.map string_of_int t.Analysis.antecedents))
      (String.concat "," (List.map string_of_int (Analysis.cited_levels t)))
      t.Analysis.o1_supports
  in
  let first = render () in
  let same = ref true in
  for _ = 1 to 9 do
    if render () <> first then same := false
  done;
  check "determinism: ten runs give a byte-identical cut, antecedents and counters" !same

(* Nothing in the walk may materialise a literal it does not need, and the clause is the
   negation of the cut with the declared-bound facts dropped. *)
let test_lits_are_the_negated_cut () =
  let _, t = cut1 Analysis.one_uip in
  let module Lit = Baguette_proof.Lit in
  check "the learned clause is the negation of the cut, over order literals"
    (String.concat " " (List.map Lit.to_string (Analysis.lits t))
    = "~b_ge_3 ~e_ge_3 e_ge_4")

let () =
  test_scene1_shape ();
  test_oracle_non_vacuous ();
  test_oracle_every_criterion ();
  test_oracle_can_fail ();
  test_criterion_postconditions ();
  test_one_uip_stops_at_a_real_uip ();
  test_conflict_side_carries_several_conflict_level_literals ();
  test_backjump_level_is_recorded_for_M2_L3 ();
  test_misattribution_is_caught ();
  test_misattribution_that_is_not_caught ();
  test_antecedents_are_the_rows_the_cut_rests_on ();
  test_hole_fold_fired ();
  test_hole_fold_is_load_bearing ();
  test_scene2_scan_fallback ();
  test_engine_agrees ();
  test_determinism ();
  test_lits_are_the_negated_cut ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nconflict-analysis unit tests passed"
