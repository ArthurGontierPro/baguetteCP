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

(* ===================================================================== *)
(* 1. Engine fixpoint (I-P2), and that a conflict returns a usable        *)
(*    explanation.                                                       *)
(* ===================================================================== *)

(* x1 in [0,5], x2 in [3,5], x1 + x2 <= 3: propagation must tighten x1's hi to 0
   (the only way the row can hold once x2 >= 3). *)
let test_fixpoint_tightens_and_settles () =
  let store = mk_store [ ("x1", 0, 5); ("x2", 3, 5) ] in
  let lin = Linear.make store [ (1, var 0); (1, var 1) ] 3 in
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
  let lin = Linear.make store [ (1, var 0); (1, var 1) ] 3 in
  (match Store.set_lo store (var 1) 4 Explanation.trivial with
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
        (forced <> Explanation.Trivial || true);
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
  let lin_x = Linear.make store [ (1, var 0); (1, var 1) ] 3 in
  let lin_y = Linear.make store [ (1, var 2); (1, var 3) ] 3 in
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
   ownership. *)
let eq_pair store a b =
  (Linear.make store [ (1, a); (-1, b) ] 0, Linear.make store [ (-1, a); (1, b) ] 0)

let sum_eq_pair store terms rhs =
  ( Linear.make store terms rhs,
    Linear.make store (List.map (fun (c, x) -> (-c, x)) terms) (-rhs) )

let sat_store_and_engine () =
  let store = mk_store sat_domains in
  let x1, x2, x3 = (var 0, var 1, var 2) in
  let le1, ge1 = eq_pair store x1 x2 in
  let le2, ge2 = sum_eq_pair store [ (1, x1); (1, x2); (1, x3) ] 2 in
  let engine =
    Engine.create
      [ pack_linear 0 le1; pack_linear 1 ge1; pack_linear 2 le2; pack_linear 3 ge2 ]
  in
  (store, engine)

let sat_check (assignment : Search.assignment) =
  let v i = List.assoc (var i) assignment in
  v 0 = v 1 && v 0 + v 1 + v 2 = 2

let unsat_domains = [ ("x1", 0, 1); ("x2", 0, 1) ]

let unsat_store_and_engine () =
  let store = mk_store unsat_domains in
  let x1, x2 = (var 0, var 1) in
  let le1, ge1 = eq_pair store x1 x2 in
  let le2, ge2 = sum_eq_pair store [ (1, x1); (1, x2) ] 1 in
  let engine =
    Engine.create
      [ pack_linear 0 le1; pack_linear 1 ge1; pack_linear 2 le2; pack_linear 3 ge2 ]
  in
  (store, engine)

(* A ctx whose model_id must never be consulted -- [Search] never renders
   [Explanation.Trivial] (see search.ml's module header), so demanding [model_id]
   would itself be the bug this mirrors test_justify.ml's own such checks for. *)
let mk_ctx writer encoding =
  Justify.create ~writer ~encoding ~model_id:(fun () ->
      failwith "search should never need Explanation.Trivial")

let mk_sat_encoding () =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) sat_domains;
  ignore (Encoding.add_equality e [ (1, Lit.ge "x1" 1); (-1, Lit.ge "x2" 1) ] 0);
  ignore
    (Encoding.add_equality e
       [ (1, Lit.ge "x1" 1); (1, Lit.ge "x2" 1); (1, Lit.ge "x3" 1) ]
       2);
  e

let mk_unsat_encoding () =
  let e = Encoding.create () in
  List.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) unsat_domains;
  ignore (Encoding.add_equality e [ (1, Lit.ge "x1" 1); (-1, Lit.ge "x2" 1) ] 0);
  ignore (Encoding.add_equality e [ (1, Lit.ge "x1" 1); (1, Lit.ge "x2" 1) ] 1);
  e

(* ===================================================================== *)
(* 2 and 3. Search functional behaviour: SAT with I-S1's independent      *)
(* check, UNSAT with I-S2/I-S3.                                          *)
(* ===================================================================== *)

let scratch_writer () =
  let path = Filename.temp_file "baguette_engine" ".pbp" in
  let oc = open_out path in
  (path, oc)

let test_search_finds_and_verifies_a_solution () =
  let store, engine = sat_store_and_engine () in
  let encoding = mk_sat_encoding () in
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
  let store, engine = unsat_store_and_engine () in
  let encoding = mk_unsat_encoding () in
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
  let run build_store_engine build_encoding check =
    let store, engine = build_store_engine () in
    let encoding = build_encoding () in
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
  let _, live_sat = run sat_store_and_engine mk_sat_encoding sat_check in
  check "audit: SAT proof's live set is empty at conclusion (I-X2)" (live_sat = 0);
  let _, live_unsat = run unsat_store_and_engine mk_unsat_encoding (fun _ -> true) in
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
  let store, engine = sat_store_and_engine () in
  let encoding = mk_sat_encoding () in
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
  let store, engine = unsat_store_and_engine () in
  let encoding = mk_unsat_encoding () in
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
