(* Unit tests for Justify: Explanation.t rendered into VeriPB proof rules.

   Follows test_proof.ml's shape: cheap unit checks against captured proof text, plus
   real invocations of veripb for the cases that matter for I-X1 ("every emitted rule
   is accepted by VeriPB"). A test that only inspects the text we wrote and never runs
   the checker is half a test (CLAUDE.md) -- tests 1 and 2 below run veripb for real. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Pol = Baguette_proof.Writer.Pol
module Encoding = Baguette_proof.Encoding
module Explanation = Baguette_core.Explanation
module Reason = Baguette_core.Reason
module Justify = Baguette_core.Justify
module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Lin_eq = Baguette_core.Lin_eq
module Learned = Baguette_core.Learned
module Reduce = Baguette_core.Reduce

(* M1-T53: the inner heap guard. test_prop.exe is the binary that reached 14.9 GB RSS on
   2026-09-16 and had to be killed by hand, so a guard that covered only test_output and
   test_compile would have missed the one incident it exists to prevent. `ulimit -v` stays
   the outer backstop -- see mem_guard.ml's header for what this cannot see. *)
let () = Mem_guard.install ()
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let check_eq name ~expected ~got =
  if String.equal expected got then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n       expected: %s\n            got: %s\n" name expected got)

let expect_ok name = function
  | Ok () -> check name true
  | Error e ->
      incr failures;
      Printf.printf "FAIL %s (raised %s)\n" name (Printexc.to_string e)

(* ------------------------------------------------------------------ *)
(* Harness: capture what a writer session wrote, like test_proof.ml's [emitted]. *)
(* ------------------------------------------------------------------ *)

let emitted ?(comments = false) ?(audit = true) f =
  let path = Filename.temp_file "baguette_justify" ".pbp" in
  let oc = open_out path in
  let w = Writer.create ~comments ~audit oc in
  let r = try Ok (f w) with e -> Error e in
  (try close_out oc with _ -> ());
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  Sys.remove path;
  (s, r)

let text f = fst (emitted f)

(* One int variable [x], one model constraint [x >= 2], a ctx pointed at it. Used by
   every test that only needs a single model constraint to justify against. *)
let build_ctx w =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  let c = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1) in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  (e, ctx, c)

(* Two int variables [x], [y], two model constraints [x >= 2] and [y >= 1]. Used by
   the Cut tests. Until M1-T31 this returned two [Justify.for_constraint] views of one
   ctx, each with its own ambient [model_id]; there is only one ctx now, because a row
   is named by the explanation ([Model_row]) and never by the renderer. *)
let build_two_ctx w =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_int e "y" ~lo:0 ~hi:3;
  let cx = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1) in
  let cy = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "y" 1) ] 1) in
  Encoding.start_proof e w;
  let ctx = Justify.create ~writer:w ~encoding:e in
  (e, ctx, cx, cy)

(* ------------------------------------------------------------------ *)
(* 5. Model_row: returns the model constraint id, emits nothing --     *)
(*    and a Decision, which has no id at all, is refused.              *)
(* ------------------------------------------------------------------ *)

let test_model_row () =
  let _, r =
    emitted (fun w ->
        let _, ctx, c = build_ctx w in
        let last0 = Writer.last_id w in
        let live0 = Writer.live_count w in
        let id = Justify.emit ctx (Explanation.model_row c) in
        check "model_row: returns the model constraint's own id" (id = c);
        check "model_row: mints no new id" (Writer.last_id w = last0);
        check "model_row: adds no live entry" (Writer.live_count w = live0))
  in
  expect_ok "model_row: no exception" r

(* M1-T31/M1-T50. [Explanation.Trivial] used to stand here and resolve to
   [ctx.model_id ()] -- the ambient row, which is how a *decision* on the trail came
   out of [linear.ml] as `pol <own row> <own row> +`. The field is gone, so there is
   no ambient row to fall back on, and the one reason with no constraint id says so
   rather than guessing. *)
let test_decision_has_no_id () =
  let _, r =
    emitted (fun w ->
        let _, ctx, _ = build_ctx w in
        let raised =
          match Justify.emit ctx (Explanation.decision (Lit.ge "x" 2)) with
          | _ -> false
          | exception Invalid_argument _ -> true
        in
        check "decision: emit refuses it -- a decision has no constraint id" raised)
  in
  expect_ok "decision: no unexpected exception" r

(* Round 2: the defect that slipped through round 1 was that [emit_linear] discarded
   [terms] and [rhs] entirely and emitted [pol <model_id>] -- veripb happily accepts a
   restatement of the model row, so this test's absence, not any propagator's, was what
   let it through. Assert the actual emitted line, not just that veripb liked *something*. *)
let test_linear_states_its_own_terms () =
  let s =
    text (fun w ->
        let _, ctx, _ = build_ctx w in
        ignore (Justify.emit ctx (Explanation.linear [ (1, Lit.ge "x" 2) ] 1)))
  in
  let lines = List.map Writer.strip_label (String.split_on_char '\n' s) in
  check "linear: emits a rup of exactly its own terms and rhs, not a pol"
    (List.exists (String.equal "rup +1 x_ge_2 >= 1 ;") lines)

(* ------------------------------------------------------------------ *)
(* 4. Memoisation: emitting the same value twice is free the second time. *)
(* ------------------------------------------------------------------ *)

let test_memoisation () =
  let _, r =
    emitted (fun w ->
        let _, ctx, _ = build_ctx w in
        let expl = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
        let id1 = Justify.emit ctx expl in
        let last1 = Writer.last_id w in
        let live1 = Writer.live_count w in
        let id2 = Justify.emit ctx expl in
        check "memo: the same id comes back" (id1 = id2);
        check "memo: no new id minted on repeat" (Writer.last_id w = last1);
        check "memo: no new live entry on repeat" (Writer.live_count w = live1);
        Writer.delete w id1)
  in
  expect_ok "memoisation: no exception" r

(* ------------------------------------------------------------------ *)
(* 3. Deferred: same emitted output as the un-deferred version, thunk runs once. *)
(* ------------------------------------------------------------------ *)

let test_deferred_linear () =
  let direct_text =
    text (fun w ->
        let _, ctx, _ = build_ctx w in
        ignore (Justify.emit ctx (Explanation.linear [ (1, Lit.ge "x" 2) ] 1)))
  in
  let calls = ref 0 in
  let deferred_text =
    text (fun w ->
        let _, ctx, _ = build_ctx w in
        let expl =
          Explanation.deferred (fun () ->
              incr calls;
              Explanation.linear [ (1, Lit.ge "x" 2) ] 1)
        in
        let id1 = Justify.emit ctx expl in
        let id2 = Justify.emit ctx expl in
        check "deferred linear: same id on repeat" (id1 = id2))
  in
  check_eq "deferred linear: identical proof text to the direct explanation"
    ~expected:direct_text ~got:deferred_text;
  check "deferred linear: the thunk ran exactly once" (!calls = 1)

let test_deferred_cut () =
  let direct_text =
    text (fun w ->
        let _, ctx, _, _ = build_two_ctx w in
        let ex = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
        let ey = Explanation.linear [ (1, Lit.ge "y" 1) ] 1 in
        ignore (Justify.emit ctx ex);
        ignore (Justify.emit ctx ey);
        ignore (Justify.emit ctx (Explanation.cut ex ey 1 1)))
  in
  let calls = ref 0 in
  let deferred_text =
    text (fun w ->
        let _, ctx, _, _ = build_two_ctx w in
        let ex = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
        let ey = Explanation.linear [ (1, Lit.ge "y" 1) ] 1 in
        ignore (Justify.emit ctx ex);
        ignore (Justify.emit ctx ey);
        let d =
          Explanation.deferred (fun () ->
              incr calls;
              Explanation.cut ex ey 1 1)
        in
        let id1 = Justify.emit ctx d in
        let id2 = Justify.emit ctx d in
        check "deferred cut: same id on repeat" (id1 = id2))
  in
  check_eq "deferred cut: identical proof text to the direct cut" ~expected:direct_text
    ~got:deferred_text;
  check "deferred cut: the thunk ran exactly once" (!calls = 1)

(* ------------------------------------------------------------------ *)
(* 6. Wipe: drops the right memo entries, and nothing below the wiped level. *)
(* ------------------------------------------------------------------ *)

let test_wipe () =
  let _, r =
    emitted (fun w ->
        let e = Encoding.create () in
        Encoding.declare_int e "x" ~lo:0 ~hi:3;
        ignore (Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 1) ] 1));
        ignore (Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1));
        Encoding.start_proof e w;
        let ctx0 = Justify.create ~writer:w ~encoding:e in
        let expl0 = Explanation.linear [ (1, Lit.ge "x" 1) ] 1 in
        let id0 = Justify.emit ctx0 expl0 in
        (* id0 is tagged at level 0. Everything from here on is tagged at level 2. *)
        Writer.set_level w 2;
        (* One ctx, not a [for_constraint] view of it: M1-T31 removed the ambient row
           a view could differ in, and the memo -- which is what this test is about --
           was always shared anyway. *)
        let ctx2 = ctx0 in
        let expl2 = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
        let id2a = Justify.emit ctx2 expl2 in
        check "wipe: the level-2 id is live before the wipe" (Writer.is_live w id2a);
        Justify.wipe_level ctx2 2;
        check "wipe: the level-2 id is gone after the wipe" (not (Writer.is_live w id2a));
        (* expl0's memo entry is at level 0, strictly below the wiped level: it must
           survive, and asking for it again must mint nothing new. *)
        let last_before = Writer.last_id w in
        let id0_again = Justify.emit ctx0 expl0 in
        check "wipe: a level-0 memo entry survives a wipe of level 2"
          (id0_again = id0 && Writer.is_live w id0);
        check "wipe: re-asking for the surviving entry mints nothing new"
          (Writer.last_id w = last_before);
        (* expl2's memo entry was dropped: asking again must re-derive, minting a
           fresh id rather than resurrecting the wiped one. *)
        let id2b = Justify.emit ctx2 expl2 in
        check "wipe: a wiped memo entry is re-derived, not resurrected" (id2b <> id2a);
        check "wipe: the fresh id is live" (Writer.is_live w id2b);
        Writer.delete_many w [ id0; id2b ])
  in
  expect_ok "wipe: no exception" r

(* ------------------------------------------------------------------ *)
(* 1 and 2: the ones that matter -- veripb actually accepts the proof (I-X1). *)
(* ------------------------------------------------------------------ *)

(* Which checker to run: lib/proof/checker.ml, shared with scripts/checker.sh.
   Every test module open-coded this search, and every copy looked at
   ~/.local/bin/veripb first -- so a project-wide choice of checker lived in nine
   places and could silently mean a build nobody intended (M1-T18). [None] is a FAILURE
   at every
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
      let dir = Filename.temp_file "baguette_justify_veripb" "" in
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

(* Model: x in [0,3], model constraint [x >= 2]. A [Linear] explanation restating that
   exact constraint, emitted through Justify, then deleted (it is an owned id); the
   proof concludes SAT with x = 2. *)
let build_linear_proof dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  let c_x2 = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1) in
  let opb = Filename.concat dir "linear.opb" in
  let pbp = Filename.concat dir "linear.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x >= 2" ] e oc;
  close_out oc;
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  ignore c_x2;
  let ctx = Justify.create ~writer:w ~encoding:e in
  let expl = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
  let derived = Justify.emit ctx expl in
  Writer.delete w derived;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 2) ]));
  close_out oc;
  (opb, pbp)

(* Model: x, y in [0,3], model constraints [x >= 2] and [y >= 1]. A [Cut] of the two
   matching [Linear] explanations, coefficients 1 and 1. Each child used to be
   pre-emitted through its own [for_constraint] view, so that the Cut's shared ctx
   never had to resolve either leaf through an ambient row. M1-T31 removed the ambient
   row and with it the need for the views: one ctx renders both children, and a [Cut]
   that did have to resolve a leaf would resolve it from the leaf's own value. *)
let build_cut_proof dir =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_int e "y" ~lo:0 ~hi:3;
  let c_x2 = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1) in
  let c_y1 = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "y" 1) ] 1) in
  let opb = Filename.concat dir "cut.opb" in
  let pbp = Filename.concat dir "cut.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "x >= 2; y >= 1" ] e oc;
  close_out oc;
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  ignore (c_x2, c_y1);
  let ctx = Justify.create ~writer:w ~encoding:e in
  let ex = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
  let ey = Explanation.linear [ (1, Lit.ge "y" 1) ] 1 in
  let id_x = Justify.emit ctx ex in
  let id_y = Justify.emit ctx ey in
  let id_cut = Justify.emit ctx (Explanation.cut ex ey 1 1) in
  Writer.delete_many w [ id_x; id_y; id_cut ];
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 2); ("y", 1) ]));
  close_out oc;
  (opb, pbp)

(* ------------------------------------------------------------------ *)
(* Round 2: agent-core's actual int_lin_le shape, end to end.          *)
(*                                                                     *)
(* D-0009 (docs/DECISIONS.md) already flags that full validation of an *)
(* int_lin_le justification is blocked on M1-T10 (search logging       *)
(* decisions as constraints) -- a level-0 test has no bound facts in   *)
(* the database. What follows is the closest honest approximation of  *)
(* that without it: stand in for "search logged a decision" with a     *)
(* genuine second model constraint that establishes the bound fact     *)
(* int_lin_le's explanation is going to cite, then run the real        *)
(* [Linear.propagate] to get a real [Explanation.t] rather than one I  *)
(* hand-wrote (see lib/core/prop/linear.ml's header for the shape).    *)
(* ------------------------------------------------------------------ *)

(* The order-encoding telescoping of an integer term [a * x] over a variable declared
   [0, width]: sum_{v=1}^{width} a * [x >= v]. Standing in for the general "expand a
   linear term into order-encoding literals" machinery that docs/DECISIONS.md D-0009
   notes does not exist yet (M1-T7c) -- written out by hand here because this test
   controls its own tiny model and does not need the general case. *)
let telescope a name width = List.init width (fun i -> (a, Lit.ge name (i + 1)))

(* Build the model and store for [x1 + x2 <= rhs], x1 in [0,5], x2 in [0,5] modelled,
   but with the store's *runtime* domain for x2 starting at [x2_lo, 5] -- standing in
   for "x2 >= x2_lo was already established", backed by a genuine extra model
   constraint so the fact int_lin_le's explanation cites is real, not orphaned. Runs
   the real propagator and returns everything a caller needs to Justify.emit the
   explanation for x1's pruning and check it end to end. *)
let setup_int_lin_le ~x2_lo ~rhs dir tag =
  let e = Encoding.create () in
  Encoding.declare_int e "x1" ~lo:0 ~hi:5;
  Encoding.declare_int e "x2" ~lo:0 ~hi:5;
  let c_bound = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x2" x2_lo) ] 1) in
  let model_row =
    Encoding.add_constraint e (Opb.le (telescope 1 "x1" 5 @ telescope 1 "x2" 5) rhs)
  in
  let opb = Filename.concat dir (tag ^ ".opb") in
  let pbp = Filename.concat dir (tag ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ Printf.sprintf "x1 + x2 <= %d; x2 >= %d" rhs x2_lo ] e oc;
  close_out oc;
  (* D-0010: the store's declared domains must agree with the encoding's, because the
     model row's constant comes from one and the explanation's chain offset from the
     other. So x2 is *declared* [0, 5] here, matching [declare_int] above, and the fact
     "x2 >= x2_lo" is applied below as a pruning -- after [make] has frozen the declared
     bounds -- rather than smuggled in as a narrower initial domain. *)
  let store =
    Store.create ~names:[| "x1"; "x2" |] ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let lin =
    Linear.make store [ (1, Var.of_int 0); (1, Var.of_int 1) ] rhs ~row_id:model_row
  in
  (match
     Store.set_lo store (Var.of_int 1) x2_lo
       (Reason.because ~concludes:None Reason.none (Explanation.model_row c_bound))
   with
  | Store.Conflict _ -> failwith "setup_int_lin_le: x2 >= x2_lo conflicts"
  | Store.Unchanged | Store.Changed -> ());
  (match Linear.propagate lin store with
  | Propagator.Conflict _ ->
      failwith "setup_int_lin_le: expected a Fixpoint, got Conflict"
  | Propagator.Fixpoint -> ());
  let entry =
    match
      List.find_opt
        (fun (en : Store.entry) -> Var.equal en.var (Var.of_int 0))
        (Store.trail_entries store)
    with
    | Some en -> en
    | None -> failwith "setup_int_lin_le: x1's bound was never pushed"
  in
  let expl = Explanation.force (Store.explanation store entry) in
  (e, c_bound, model_row, opb, pbp, expl)

(* x2_lo = 1: the excluded bound fact is [x2 >= 1], one step above x2's declared lo of
   0 -- the case D-0010 shows is the one a green suite can miss (it happens to be the
   value where a wrong, one-literal shape would also have verified). Under D-0013 this
   is a [Combine]: [Model_row model_row]'s base, weakening x1 away entirely (x1 is
   still fully declared), cite x2's established bound ([c_bound]) scaled by [abs
   coeff = 1], divided by 1 (x1's own coefficient). *)
let build_int_lin_le_ok dir =
  let e, _c_bound, _model_row, opb, pbp, expl =
    setup_int_lin_le ~x2_lo:1 ~rhs:2 dir "intlinle_ok"
  in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof e w;
  (* [expl]'s base is [Model_row model_row]. This used to install a [~model_id] thunk
     that failed if consulted, to prove the base was not [Trivial]; M1-T31 deleted
     both, so there is nothing left that could be consulted. *)
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x1", 0); ("x2", 1) ]));
  close_out oc;
  (opb, pbp)

(* x2_lo = 2: the excluded bound fact is [x2 >= 2], *two* steps above x2's declared lo
   of 0. This is the case that caught D-0010: int_lin_le used to state it as the single
   literal [(1, x2_ge_2)] at rhs 2, which no proof state can satisfy since one 0/1
   literal at coefficient 1 reaches at most 1. Under D-0013 the fact does not need
   restating at all -- [c_bound] (the constraint that already established [x2 >= 2])
   is cited directly, by id, scaled by [abs coeff]; the gap D-0010 found is simply not
   expressible any more, since there is no chain length left to get wrong. Counted,
   not a probe: it guards the fix. *)
let build_int_lin_le_gap dir =
  let e, _c_bound, _model_row, opb, pbp, expl =
    setup_int_lin_le ~x2_lo:2 ~rhs:3 dir "intlinle_gap"
  in
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:false oc in
  Encoding.start_proof e w;
  (* Same as [build_int_lin_le_ok]: [expl]'s base is a [Model_row], and since M1-T31
     there is no ambient row it could have been instead. *)
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x1", 0); ("x2", 2) ]));
  close_out oc;
  (opb, pbp)

(* ------------------------------------------------------------------ *)
(* D-0013, checked end to end: the worked example itself.              *)
(*                                                                     *)
(* 2*x1 + 4*x2 = 7, x1/x2 in [0,3] -- refuted at the root, no search   *)
(* at all. int_lin_eq posts as two int_lin_le instances (D-0011); run  *)
(* to a joint fixpoint the way engine.ml will, one of the two hits the *)
(* cross-instance conflict D-0013's own worked example ends on. This   *)
(* is the derivation docs/DECISIONS.md D-0013 records as accepted by   *)
(* the checker in full; this test is what checks the *solver*          *)
(* actually produces it, not just that the hand-written proof does.    *)
(* ------------------------------------------------------------------ *)

let propagate_pair (le, ge) store =
  let rec loop () =
    let snap = Store.snapshot store in
    match Linear.propagate le store with
    | Propagator.Conflict _ as c -> c
    | Propagator.Fixpoint -> (
        match Linear.propagate ge store with
        | Propagator.Conflict _ as c -> c
        | Propagator.Fixpoint ->
            if Store.same_domains store snap then Propagator.Fixpoint else loop ())
  in
  loop ()

let setup_d0013 () =
  let e = Encoding.create () in
  Encoding.declare_int e "x1" ~lo:0 ~hi:3;
  Encoding.declare_int e "x2" ~lo:0 ~hi:3;
  let opb_terms, const = Encoding.linear_terms_int_lin_le e [ (2, "x1"); (4, "x2") ] in
  let geq_id, leq_id = Encoding.add_equality e opb_terms (7 - const) in
  let store =
    Store.create ~names:[| "x1"; "x2" |] ~domains:[| Domain.make 0 3; Domain.make 0 3 |]
  in
  let le, ge =
    Lin_eq.make store
      [ (2, Var.of_int 0); (4, Var.of_int 1) ]
      7 ~le_id:leq_id ~ge_id:geq_id
  in
  let outcome = propagate_pair (le, ge) store in
  (e, opb_terms, geq_id, leq_id, outcome)

let build_d0013_conflict dir =
  let e, opb_terms, _geq_id, _leq_id, outcome = setup_d0013 () in
  let expl =
    match outcome with
    | Propagator.Conflict c -> Explanation.force c.Store.c_why
    | Propagator.Fixpoint -> failwith "build_d0013_conflict: expected a Conflict"
  in
  let opb = Filename.concat dir "d0013.opb" in
  let pbp = Filename.concat dir "d0013.pbp" in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "2*x1 + 4*x2 = 7, x1/x2 in [0,3]" ] e oc;
  close_out oc;
  let oc = open_out pbp in
  let w = Writer.create ~comments:true ~audit:false oc in
  Encoding.start_proof e w;
  (* Every base in this derivation is a [Model_row]; M1-T31 leaves no ambient row for
     one of them to have been instead. *)
  let ctx = Justify.create ~writer:w ~encoding:e in
  let id = Justify.emit ctx expl in
  Writer.conclusion w (Writer.Unsat (Some id));
  close_out oc;
  ignore opb_terms;
  (opb, pbp)

let test_d0013_conflict () =
  (* Solved shape: propagation alone (no search) must already find the conflict. *)
  let _, _, _, _, outcome = setup_d0013 () in
  check "D-0013: 2x1+4x2=7 in [0,3]^2 is refuted by propagation alone, no search"
    (match outcome with Propagator.Conflict _ -> true | Propagator.Fixpoint -> false);
  (* The divisor text D-0013's own worked example calls out explicitly (task
     instructions: "assert that a division emits the divisor you expect"). Both
     int_lin_le instances divide by their own coefficient magnitude: 4 for x2's
     pruning, 2 for x1's. *)
  let s =
    text (fun w ->
        let _, _, _, _, outcome = setup_d0013 () in
        let expl =
          match outcome with
          | Propagator.Conflict c -> Explanation.force c.Store.c_why
          | Propagator.Fixpoint -> failwith "test_d0013_conflict: expected a Conflict"
        in
        let e = Encoding.create () in
        Encoding.declare_int e "x1" ~lo:0 ~hi:3;
        Encoding.declare_int e "x2" ~lo:0 ~hi:3;
        let opb_terms, const =
          Encoding.linear_terms_int_lin_le e [ (2, "x1"); (4, "x2") ]
        in
        let _geq_id, _leq_id = Encoding.add_equality e opb_terms (7 - const) in
        Encoding.start_proof e w;
        let ctx = Justify.create ~writer:w ~encoding:e in
        ignore (Justify.emit ctx expl))
  in
  let ends_with suffix s =
    let ls = String.length s and lsuf = String.length suffix in
    ls >= lsuf && String.sub s (ls - lsuf) lsuf = suffix
  in
  (* [rule_body], not [strip_label]: under 3.0 a `pol` is introduced as `@cN pol ...`
     AND terminated with `;`, and the claim pinned here -- that some step divides by
     this coefficient -- is about the derivation, not about its name or punctuation. *)
  let lines = List.map Writer.rule_body (String.split_on_char '\n' s) in
  check "D-0013: some step divides by 4 (x2's own coefficient)"
    (List.exists
       (fun l -> String.length l > 0 && l.[0] = 'p' && ends_with " 4 d" l)
       lines);
  check "D-0013: some step divides by 2 (x1's own coefficient)"
    (List.exists
       (fun l -> String.length l > 0 && l.[0] = 'p' && ends_with " 2 d" l)
       lines);
  run_veripb ~name:"D-0013: 2x1+4x2=7 in [0,3]^2, root conflict, checked end to end"
    ~build:build_d0013_conflict

(* ------------------------------------------------------------------ *)
(* M1-T13 / D-0018: [emit_rup_clause], the door [Trace] writes through. *)
(* ------------------------------------------------------------------ *)

(* Three things are worth pinning here, all of which [Trace]'s own tests would only see
   indirectly: the exact text (a clause, in Opb's `+1 l ... >= 1 ;` form), that it is
   NOT memoised (two structurally identical trace lines are two different prunings and
   must be two different ids -- memoising on structure would silently merge them, and
   memoising on identity would never fire anyway), and that a literal about a variable
   the encoding never declared is refused here rather than several lines later inside
   veripb. *)
let test_emit_rup_clause () =
  let s =
    text (fun w ->
        let _, ctx, _ = build_ctx w in
        ignore
          (Justify.emit_rup_clause ctx ~origin:"trace"
             [ Lit.ge "x" 2; Lit.negate (Lit.ge "x" 3) ]))
  in
  check_eq "emit_rup_clause: writes the clause verbatim"
    ~expected:"rup +1 x_ge_2 +1 ~x_ge_3 >= 1 ;"
    ~got:(Writer.strip_label (List.nth (String.split_on_char '\n' s) 2));
  let _, r =
    emitted (fun w ->
        let _, ctx, _ = build_ctx w in
        let a = Justify.emit_rup_clause ctx ~origin:"trace" [ Lit.ge "x" 2 ] in
        let b = Justify.emit_rup_clause ctx ~origin:"trace" [ Lit.ge "x" 2 ] in
        check "emit_rup_clause: not memoised -- one id per line, not per clause value"
          (a <> b);
        (* Both are this test's to retire: an id you receive is an id you delete. *)
        Writer.delete_many w [ a; b ])
  in
  expect_ok "emit_rup_clause: no exception" r;
  let _, r =
    emitted (fun w ->
        let _, ctx, _ = build_ctx w in
        ignore (Justify.emit_rup_clause ctx ~origin:"trace" [ Lit.ge "nosuchvar" 1 ]))
  in
  check "emit_rup_clause: an undeclared variable is refused here, not by veripb"
    (match r with Error (Invalid_argument _) -> true | _ -> false)

(* ------------------------------------------------------------------ *)
(* M2-T9. The claim index: clause -> the line that states it.          *)
(* ------------------------------------------------------------------ *)

(* An index is a new thing, so it can be wrong in new ways, and none of them is visible
   from "the proof still verifies": a reused id that names the wrong line is a valid
   [pol] over the wrong constraint (D-0020's lesson -- "veripb accepts" is not evidence
   that a derivation is load-bearing), and an index that never fires at all leaves the
   old duplicate lines and passes every pre-existing check. So each way it can be wrong
   gets its own check, and the first of them is the one that catches the break the
   handover asked for: point the index at a line that does not state the clause.

     * it fires at all, and the reuse is against the RIGHT line -- checked by reading
       the emitted text back and matching the reused id's own line against the clause;
     * it is keyed structurally, not on rendered OPB names, which [Lit.sanitize]
       makes non-injective;
     * it is order-insensitive, because a clause is a set;
     * it does not survive its level (the stale-after-a-backtrack case), and
     * it does not reach *up* a level, which is I-S4 as a precondition and what keeps
       [Search]'s nogood out of its way;
     * the outermost line wins when two lines state the same clause;
     * [defining_lit] answers only for a unit line, because only a unit line
       establishes a literal (D-0009). *)

(* The body of the line labelled [@c<id>] in [text], label stripped, or "" if no line
   carries that label. *)
let line_labelled text id =
  let want = Printf.sprintf "@c%d " id in
  let n = String.length want in
  let rec go = function
    | [] -> ""
    | l :: rest ->
        if String.length l >= n && String.sub l 0 n = want then Writer.strip_label l
        else go rest
  in
  go (String.split_on_char '\n' text)

(* ---- resolving an id to its line WITHOUT a label (M2-T14) -------------------

   The check below wants to know that the id the index handed back names the line that
   states the clause. It used to ask that of [line_labelled], i.e. by reading a label --
   so under a format without labels it could not be asked at all, and the lane asserted
   [false] on
   purpose rather than pass vacuously. That is honest but it leaves a 2.0 run
   permanently one check red, and a run that is always red is a run people stop reading.

   An id can be resolved by CONTENT instead. VeriPB numbers constraints itself: the
   `f <n>` header loads n model rows as ids 1..n, and every rule that mints an id takes
   the next one, in file order. Walking the file with that counter reproduces the
   checker's own numbering and so answers the same question in either format. *)

(* The model-row count off the proof's own `f <n>` header. Both formats write it; 3.0
   just adds a ` ;` terminator, which splitting on spaces discards. *)
let model_row_count text =
  let rec go = function
    | [] -> 0
    | l :: rest -> (
        match String.split_on_char ' ' (String.trim (Writer.strip_label l)) with
        | "f" :: n :: _ -> ( try int_of_string (String.trim n) with _ -> go rest)
        | _ -> go rest)
  in
  go (String.split_on_char '\n' text)

(* Which rules mint an id: exactly the emitters in writer.ml that call [fresh]. `#`,
   `w`, `del`, `*`, `output`, `conclusion` and the level markers mint nothing, so they
   must not advance the counter. *)
let mints_id line =
  let body = Writer.strip_label line in
  List.exists
    (fun p ->
      String.length body >= String.length p && String.sub body 0 (String.length p) = p)
    [ "pol "; "rup "; "ia "; "red "; "solx "; "soli "; "obju " ]

(* The body of the line that mints constraint id [id], 3.0 label stripped, or "" if no
   line mints it. Works in both formats. *)
let line_minting_id text id =
  let n = ref (model_row_count text) in
  let rec go = function
    | [] -> ""
    | l :: rest ->
        if mints_id l then (
          incr n;
          if !n = id then Writer.strip_label l else go rest)
        else go rest
  in
  go (String.split_on_char '\n' text)

let test_index_reuses_the_right_line () =
  let clause = [ Lit.ge "x" 2; Lit.negate (Lit.ge "x" 3) ] in
  let s, r =
    emitted (fun w ->
        let _, ctx, _ = build_ctx w in
        let trace_id = Justify.emit_rup_clause ctx ~origin:"trace" clause in
        let last = Writer.last_id w in
        let reused = Justify.emit ctx (Explanation.clause clause) in
        check "index: an Explanation.Clause reuses the trace line's id" (reused = trace_id);
        check "index: and mints no new line for it" (Writer.last_id w = last);
        (* The one check that would catch an index pointing at the WRONG line. An id is
           just an integer, so [reused = trace_id] only says the two agree; this says
           the line that id labels really does state the clause. *)
        Writer.delete w trace_id;
        reused)
  in
  let reused = match r with Ok id -> id | Error _ -> -1 in
  (* [reused = trace_id] above only says two integers agree. THIS is the check that
     would catch an index pointing at the wrong line: the line that mints that id
     really does state the clause. Asked by CONTENT, which is what M2-T14 changed here
     and is a keeper: the ` ;` in the expectation belongs to [Opb.constr_to_string], not
     to the rule terminator. *)
  let expected = "rup +1 x_ge_2 +1 ~x_ge_3 >= 1 ;" in
  check_eq "index: the reused id names the line that states the clause" ~expected
    ~got:(line_minting_id s reused);
  (* The same line must also carry `@c<reused>` as its label. That was the whole of this
     lane before M2-T14; it is kept, so nothing is checked less, and it doubles as a
     cross-check that the content-based numbering above agrees with what the writer
     labelled. *)
  check_eq "index: and the line's @c label agrees with that numbering" ~expected
    ~got:(line_labelled s reused);
  expect_ok "index: no exception" (Result.map ignore r)

let test_index_is_structural () =
  (* [Lit.sanitize] maps every non-alphanumeric to '_', so these two distinct variables
     render to the same OPB name. An index keyed on [Lit.to_string] would hand back the
     first one's line for the second one's clause -- a valid line about the wrong
     variable, which is exactly the class of defect D-0009 and D-0020 record. *)
  let _, r =
    emitted (fun w ->
        let e = Encoding.create () in
        Encoding.declare_int e "a-b" ~lo:0 ~hi:3;
        Encoding.declare_int e "a_b" ~lo:0 ~hi:3;
        Encoding.start_proof e w;
        let ctx = Justify.create ~writer:w ~encoding:e in
        check "index: the two variables really do render to one OPB name"
          (String.equal (Lit.to_string (Lit.ge "a-b" 2)) (Lit.to_string (Lit.ge "a_b" 2)));
        let first = Justify.emit_rup_clause ctx ~origin:"trace" [ Lit.ge "a-b" 2 ] in
        let last = Writer.last_id w in
        let second = Justify.emit ctx (Explanation.clause [ Lit.ge "a_b" 2 ]) in
        check "index: a different variable with the same OPB name is NOT reused"
          (second <> first);
        check "index: so it mints its own line" (Writer.last_id w > last);
        Writer.delete_many w [ first; second ])
  in
  expect_ok "index: structural key, no exception" r

let test_index_ignores_clause_order () =
  let _, r =
    emitted (fun w ->
        let _, ctx, _ = build_ctx w in
        let a = Lit.ge "x" 2 and b = Lit.negate (Lit.ge "x" 3) in
        let first = Justify.emit_rup_clause ctx ~origin:"trace" [ a; b ] in
        let last = Writer.last_id w in
        let reused = Justify.emit ctx (Explanation.clause [ b; a ]) in
        check "index: a clause is a set -- literal order does not matter"
          (reused = first && Writer.last_id w = last);
        Writer.delete w first)
  in
  expect_ok "index: clause order, no exception" r

let test_index_levels () =
  let _, r =
    emitted (fun w ->
        let _, ctx, _ = build_ctx w in
        let clause = [ Lit.ge "x" 2 ] in
        (* (a) Reaching UP a level is refused: a line at level 2 must not be handed to a
           caller writing at level 1, because `w 2` would retire the cited line and
           leave the citing one. This is I-S4 as a precondition, and it is what keeps
           [Search]'s nogood -- emitted at the parent level -- from ever being answered
           with a trace line from inside the branch it closes. *)
        Writer.set_level w 2;
        let deep = Justify.emit_rup_clause ctx ~origin:"trace" clause in
        Writer.set_level w 1;
        let shallow = Justify.emit ctx (Explanation.clause clause) in
        check "index: a line at a deeper level is not reused by a shallower one"
          (shallow <> deep);
        (* (b) Stale after a backtrack: wiping level 2 must take the index entry with
           it, so nothing later cites an id the proof no longer contains. Asked at
           level 1, where (a) would refuse it anyway, and then at level 2 again, where
           only the wipe can be the reason. *)
        Writer.set_level w 2;
        let deep2 = Justify.emit_rup_clause ctx ~origin:"trace" [ Lit.ge "x" 3 ] in
        check "index: the level-2 line is live before the wipe" (Writer.is_live w deep2);
        Justify.wipe_level ctx 2;
        check "index: and gone after it" (not (Writer.is_live w deep2));
        Writer.set_level w 2;
        let after = Justify.emit ctx (Explanation.clause [ Lit.ge "x" 3 ]) in
        check "index: a wiped line is not reused at the same level afterwards"
          (after <> deep2);
        (* (c) The outermost line wins when two lines state the same clause. Both are
           written -- [emit_rup_clause] never consults the index -- and the one a later
           caller may cite is the one that survives the most backtracking. *)
        Writer.set_level w 0;
        let outer = Justify.emit_rup_clause ctx ~origin:"trace" [ Lit.ge "x" 1 ] in
        Writer.set_level w 3;
        let inner = Justify.emit_rup_clause ctx ~origin:"trace" [ Lit.ge "x" 1 ] in
        check "index: two lines can state one clause -- Trace always writes its own"
          (inner <> outer);
        let got = Justify.emit ctx (Explanation.clause [ Lit.ge "x" 1 ]) in
        check "index: and the outermost of the two is the one handed back" (got = outer);
        Justify.wipe_level ctx 1;
        Writer.set_level w 0;
        Writer.delete_many w [ shallow; outer ])
  in
  expect_ok "index: levels, no exception" r

let test_defining_lit () =
  let _, r =
    emitted (fun w ->
        let _, ctx, _ = build_ctx w in
        let unit_id = Justify.emit_rup_clause ctx ~origin:"trace" [ Lit.ge "x" 2 ] in
        let pair =
          Justify.emit_rup_clause ctx ~origin:"trace"
            [ Lit.ge "x" 3; Lit.negate (Lit.ge "x" 1) ]
        in
        check "defining_lit: a unit line establishes its literal"
          (Justify.defining_lit ctx (Lit.ge "x" 2) = Some unit_id);
        (* D-0009: a multi-literal clause establishes nothing about any one of its
           literals, so the index must not answer for its members. *)
        check "defining_lit: a member of a two-literal clause is NOT established"
          (Justify.defining_lit ctx (Lit.ge "x" 3) = None);
        check "defining_lit: a literal no line has stated is None"
          (Justify.defining_lit ctx (Lit.negate (Lit.ge "x" 2)) = None);
        check "defining_lit: the two-literal clause itself IS found"
          (Justify.defining_line ctx [ Lit.negate (Lit.ge "x" 1); Lit.ge "x" 3 ]
          = Some pair);
        (* The empty clause is deliberately not indexed: it is the root nogood's own
           claim, whose id [conclusion UNSAT] cites and [Search.solve] must not find
           answered by someone else's line. *)
        check "defining_lit: the empty clause is never indexed"
          (Justify.defining_line ctx [] = None);
        Writer.delete_many w [ unit_id; pair ])
  in
  expect_ok "defining_lit: no exception" r

(* ------------------------------------------------------------------ *)
(* M2-L0 / D-0043, test (a): the conclusion is what makes the CHECKER  *)
(*   reject a `pol` that derives less than the pruning claimed.        *)
(* ------------------------------------------------------------------ *)

(* M1-T51 measured this break at the [Writer] level, with the claim handed to
   [Writer.pol_concluding] by the test itself (test_proof.ml,
   [test_pol_states_its_conclusion]). The gap it left is the one D-0043 closes: nothing
   in [lib/] had a claim to hand it, because [Explanation.Combine] records how a bound was
   derived and not what. This test is the same break one layer up, with the claim coming
   from where it now lives -- [Reason.justified]'s [concludes] -- through
   [Justify.emit_concluding].

   Four lanes, and the first two exist so the last two mean something:

     1. the honest derivation, bare               -- must be ACCEPTED
     2. the honest derivation, stating its bound  -- must be ACCEPTED
     3. the derivation truncated to its leftmost operand, so it derives a clause strictly
        weaker than the bound the pruning claimed, and bare it is ACCEPTED. This lane
        asserts the ACCEPTANCE. If it ever starts failing, a bare [pol] has grown a
        conclusion check and this test's premise wants re-measuring, not deleting.
     4. the same corruption with the conclusion stated -- REJECTED.

   The model is UNSAT and the contradiction is derived under its own origin, so the
   mutation knob cannot reach it: what differs between lanes is the pruning's line and
   nothing else. *)
let conclusion_break_opb dir name =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_int e "y" ~lo:0 ~hi:3;
  let v = Lit.ge "x" 1 and u = Lit.ge "y" 2 in
  (* c1 + c2, halved, is `x >= 1`; c3 says the opposite, so the model is UNSAT and the
     proof can conclude. c1 alone is what the truncation leaves behind. *)
  let c1 = Encoding.add_constraint e (Opb.ge [ (1, v); (1, u) ] 1) in
  let c2 = Encoding.add_constraint e (Opb.ge [ (1, v); (1, Lit.negate u) ] 1) in
  let c3 = Encoding.add_constraint e (Opb.ge [ (1, Lit.negate v) ] 1) in
  let opb = Filename.concat dir (name ^ ".opb") in
  let oc = open_out opb in
  (* The .opb and the .pbp are one artefact in two files and they must agree about
     labelling, or the checker stops at the GRAMMAR and never judges the derivation --
     found by M2-L5, when this pair disagreed and the lane asserting REJECTED **passed on
     the parse error**. That is D-0020/D-0030's rule exactly. Labelling is now
     unconditional on both sides (D-0046), so they cannot disagree; the note stays
     because the failure it records is what a future knob here would reintroduce. *)
  Encoding.write_opb e oc;
  close_out oc;
  (e, opb, c1, c2, c3)

let test_conclusion_rejects_a_weakened_pol () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        ("FAIL M2-L0/D-0043 (a): " ^ Baguette_proof.Checker.not_found_message
       ^ " -- the whole point of this test is that the CHECKER rejects the weakened \
          derivation, so with no checker there is nothing here. This is not a pass.")
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_concl" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let log = Filename.concat dir "log" in
      let site = "combine(2 summand(s), / 2)" in
      (* [stated]: does the pruning go out through [emit_concluding] with the
         [Reason.fact] it concluded, or through plain [emit]? [truncated]: is the `pol`
         corrupted to its leftmost operand? Returns [true] iff veripb ACCEPTED. *)
      let run ~name ~stated ~truncated =
        let e, opb, c1, c2, c3 = conclusion_break_opb dir name in
        let pbp = Filename.concat dir (name ^ ".pbp") in
        let oc = open_out pbp in
        let mutation = Writer.Mutation.make ~site Writer.Mutation.Truncate_derivation in
        let w =
          if truncated then Writer.create_mutated ~comments:false ~audit:true ~mutation oc
          else Writer.create ~comments:false ~audit:true oc
        in
        Encoding.start_proof e w;
        let ctx = Justify.create ~writer:w ~encoding:e in
        (* The pruning as a propagator builds it: one [Combine] over the two rows,
           divided by 2, and the bound it concluded. [x >= 1] with [x] declared from 0,
           so the fact materialises to the literal the `ia` claims. *)
        let expl =
          Explanation.combine
            [
              Explanation.term 1 (Explanation.model_row c1);
              Explanation.term 1 (Explanation.model_row c2);
            ]
            2
        in
        let concludes = Some (Reason.at_least ~name:"x" ~decl:0 1) in
        let id =
          if stated then Justify.emit_concluding ctx ~concludes expl
          else Justify.emit ctx expl
        in
        if truncated && Writer.mutation_note w = None then (
          incr failures;
          Printf.printf
            "FAIL M2-L0 %s: the Truncate_derivation knob never fired at site %S, so this \
             lane corrupted nothing and its verdict means nothing.\n"
            name site);
        Writer.delete w id;
        let bottom =
          Writer.pol w ~origin:"the contradiction"
            Pol.(add (div (add (id c1) (id c2)) 2) (id c3))
        in
        Writer.conclusion w (Writer.Unsat (Some bottom));
        close_out oc;
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
        = 0
      in
      check "D-0043 (a) baseline: an honest Combine, emitted bare, is accepted"
        (run ~name:"honest_bare" ~stated:false ~truncated:false);
      check
        "D-0043 (a) baseline: the same Combine through emit_concluding is accepted -- \
         stating the bound costs nothing when the derivation is honest"
        (run ~name:"honest_stated" ~stated:true ~truncated:false);
      check
        "D-0043 (a) THE GAP: a Combine truncated to derive strictly LESS than the bound \
         the pruning claimed is still ACCEPTED when nothing states the claim"
        (run ~name:"weak_bare" ~stated:false ~truncated:true);
      check
        "D-0043 (a) THE CONTROL: the same truncation is REJECTED once the conclusion \
         travels on Reason.justified and reaches the page as an `ia`"
        (not (run ~name:"weak_stated" ~stated:true ~truncated:true));
      (* And it is the implication check that rejects it, not a parse error or a dangling
         label. Asserted at full strength: an exit status cannot tell a JUDGEMENT from a
         refusal to parse, which is how four lanes came to be green (M2-T14). *)
      let contains needle hay =
        let n = String.length needle and h = String.length hay in
        let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
        n = 0 || go 0
      in
      let s =
        let ic = open_in_bin log in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      in
      check "D-0043 (a): the rejection is the implication check, in the checker's words"
        (contains "not syntactically implied" s);
      Sys.readdir dir
      |> Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ());
      try Sys.rmdir dir with _ -> ())

(* ------------------------------------------------------------------ *)
(* M2-L5 / D-0044: REDUCTION as a named, swappable component.          *)
(*   (a) hand-built rows, pinned against RoundingSat's definition;     *)
(*   (b) the conflicting invariant is preserved;                       *)
(*   (c) the checker-level control -- a TRUNCATED reduction is         *)
(*       rejected once M2-L0's conclusion is stated, and accepted      *)
(*       bare.                                                         *)
(* ------------------------------------------------------------------ *)

(* The literals every M2-L5 test is built from. Three order literals on three
   single-digit domains -- D-0028 makes the encoding width-proportional and nothing here
   needs width. *)
let rv = Lit.ge "x" 1
let ru = Lit.ge "y" 2
let rw = Lit.ge "z" 1

(* [falsified] as a set membership, which is all [Reduce.view] is ever shown: no store,
   no live state (reduce.ml's header, and analysis.ml's [view] for the same reason). *)
let falsified_in set l = List.exists (Lit.equal l) set
let view row ~pivot ~falsified = { Reduce.row; pivot; falsified = falsified_in falsified }

(* ------------------------------------------------------------- (a) *)

(* The worked case of reduce.ml's header and of D-0044's table:

     C = 3v + 3u + 1w >= 5,  pivot v (d = 3),  u and w NOT falsified

   [division] weakens every non-falsified literal but the pivot, so u and w both go and
   the row collapses to the pivot alone. [roundToOne] weakens only what the division
   would round -- w, whose coefficient 1 is not a multiple of 3 -- and keeps u, whose 3
   is. [v + u >= 2] is strictly stronger than [v >= 1] over 0-1 variables, which is the
   dominance D-0044 cites and the whole reason both names exist. *)
let test_reduce_pins_both_rules () =
  let row = Learned.make [ (3, rv); (3, ru); (1, rw) ] 5 in
  check_eq "M2-L5 (a): the hand-built reason row itself"
    ~expected:"+3 x_ge_1 +3 y_ge_2 +1 z_ge_1 >= 5" ~got:(Learned.to_string row);
  let v = view row ~pivot:rv ~falsified:[] in
  check "M2-L5 (a): the row propagates its pivot, so it is a legitimate reason"
    (Reduce.propagates row ~pivot:rv ~falsified:(falsified_in []));
  (match Reduce.division.reduce v with
  | None -> check "M2-L5 (a): division applies" false
  | Some o ->
      check_eq "M2-L5 (a) division: 3v+3u+w >= 5, pivot v -> v >= 1"
        ~expected:"+1 x_ge_1 >= 1" ~got:(Learned.to_string o.reduced);
      check "M2-L5 (a) division: divides by the pivot's coefficient" (o.divisor = 3);
      check_eq "M2-L5 (a) division: the literal axioms it adds are ~u and ~w, scaled"
        ~expected:"3*~y_ge_2 1*~z_ge_1"
        ~got:
          (String.concat " "
             (List.map
                (fun (c, l) -> Printf.sprintf "%d*%s" c (Lit.to_string l))
                o.weakened));
      check "M2-L5 (a) division: its own postcondition holds"
        (Reduce.postcondition_holds Reduce.division v o));
  match Reduce.round_to_one.reduce v with
  | None -> check "M2-L5 (a): roundToOne applies" false
  | Some o ->
      check_eq "M2-L5 (a) roundToOne: the same row -> v + u >= 2, strictly stronger"
        ~expected:"+1 x_ge_1 +1 y_ge_2 >= 2" ~got:(Learned.to_string o.reduced);
      check_eq "M2-L5 (a) roundToOne: it weakens ONLY w, whose 1 is not a multiple of 3"
        ~expected:"1*~z_ge_1"
        ~got:
          (String.concat " "
             (List.map
                (fun (c, l) -> Printf.sprintf "%d*%s" c (Lit.to_string l))
                o.weakened));
      check "M2-L5 (a) roundToOne: its own postcondition holds"
        (Reduce.postcondition_holds Reduce.round_to_one v o);
      (* D-0044's "divide so the reduced reason has slack zero", asserted rather than
         quoted. *)
      check "M2-L5 (a) roundToOne: the reduced reason has slack exactly zero"
        (Reduce.slack o.reduced ~falsified:(falsified_in []) = 0);
      (* And the dominance is the wrong way round for the other rule's postcondition:
         roundToOne's output keeps a non-falsified literal, which is exactly what
         [division]'s own clause forbids. A standing proof that the postconditions are
         each rule's and not the type's (analysis.ml's [conflict_side] does this job for
         the cut criterion). *)
      check
        "M2-L5 (a): division's postcondition is DIVISION's -- roundToOne's output fails \
         it"
        (not (Reduce.postcondition_holds Reduce.division v o))

(* A falsified literal is never weakened: dropping it would take its coefficient out of
   the degree but not out of the slack sum, which is exactly how a reduction loses the
   conflict (reduce.ml's header). Both rules must leave it alone, so here they agree. *)
let test_reduce_never_weakens_a_falsified_literal () =
  let row = Learned.make [ (3, rv); (2, ru) ] 3 in
  let v = view row ~pivot:rv ~falsified:[ ru ] in
  let expect name (r : Reduce.t) =
    match r.reduce v with
    | None -> check (name ^ ": applies") false
    | Some o ->
        check_eq
          (name ^ ": 3v+2u >= 3 with u falsified -> v + u >= 1")
          ~expected:"+1 x_ge_1 +1 y_ge_2 >= 1" ~got:(Learned.to_string o.reduced);
        check (name ^ ": nothing was weakened away") (o.weakened = []);
        check (name ^ ": its own postcondition holds") (Reduce.postcondition_holds r v o)
  in
  expect "M2-L5 (a) division, falsified u" Reduce.division;
  expect "M2-L5 (a) roundToOne, falsified u" Reduce.round_to_one

(* Pivot coefficient 1: the divisor is 1, roundToOne finds every coefficient a multiple
   of it, weakens nothing and returns the row unchanged -- and its [derive] is the
   IDENTITY, so no `pol` line is written for a step that does nothing. Division still
   weakens, because its rule does not consult the divisor at all. *)
let test_reduce_is_a_no_op_at_divisor_one () =
  let row = Learned.make [ (1, rv); (2, ru) ] 3 in
  let v = view row ~pivot:rv ~falsified:[] in
  (match Reduce.round_to_one.reduce v with
  | None -> check "M2-L5 (a) roundToOne at d=1: applies" false
  | Some o ->
      check_eq "M2-L5 (a) roundToOne at d=1: the row is returned unchanged"
        ~expected:(Learned.to_string row) ~got:(Learned.to_string o.reduced);
      check "M2-L5 (a) roundToOne at d=1: divisor is 1 and nothing is weakened"
        (o.divisor = 1 && o.weakened = []);
      let base = Explanation.model_row 7 in
      check "M2-L5 (a) roundToOne at d=1: [derive] is the identity -- no pol line at all"
        (o.derive base == base);
      check "M2-L5 (a) roundToOne at d=1: its own postcondition still holds"
        (Reduce.postcondition_holds Reduce.round_to_one v o));
  match Reduce.division.reduce v with
  | None -> check "M2-L5 (a) division at d=1: applies" false
  | Some o ->
      check_eq "M2-L5 (a) division at d=1: u is weakened away anyway"
        ~expected:"+1 x_ge_1 >= 1" ~got:(Learned.to_string o.reduced);
      check "M2-L5 (a) division at d=1: it does emit a step, but no division"
        (o.divisor = 1 && o.weakened <> []
        && not (o.derive (Explanation.model_row 7) == Explanation.model_row 7))

(* [reduce] answers [None], rather than something, when the rule does not apply. *)
let test_reduce_declines () =
  let row = Learned.make [ (3, rv); (3, ru) ] 4 in
  check "M2-L5 (a): a pivot that is not a literal of the row is declined"
    (Reduce.round_to_one.reduce (view row ~pivot:rw ~falsified:[]) = None);
  check "M2-L5 (a): a falsified pivot is declined -- there is nothing to resolve on"
    (Reduce.round_to_one.reduce (view row ~pivot:rv ~falsified:[ rv ]) = None)

(* ------------------------------------------------------------- (b) *)

(* THE PROPERTY M2-L5's row asks for: the reduced reason still propagates the same
   literal, and still has negative slack once that literal is falsified -- the
   conflicting invariant, which is the only reason reduction exists.

   Those two halves are one fact (see [Reduce.propagates]), and both are asserted
   separately anyway so that a future change that breaks the identity is caught by the
   test rather than hidden by it.

   Rows are pseudo-random from a FIXED seed: the determinism gate
   (scripts/check_determinism.sh) is a commit gate here, so a test that samples has to
   sample the same way twice. Coefficients stay in the single digits -- nothing about
   this property needs magnitude, and Checked's cap is not what is under test. *)
let test_reduce_preserves_the_conflicting_invariant () =
  let st = Random.State.make [| 20260918 |] in
  let pool = [| rv; ru; rw; Lit.ge "x" 2; Lit.ge "y" 1; Lit.ge "z" 3 |] in
  let bad_lanes = ref 0 and rounds = 400 in
  for _ = 1 to rounds do
    let pivot = pool.(Random.State.int st (Array.length pool)) in
    let d = 1 + Random.State.int st 6 in
    (* Two to four other literals, each falsified or not. *)
    let others =
      List.filter_map
        (fun l ->
          if Lit.equal l pivot then None
          else if Random.State.bool st then
            Some (1 + Random.State.int st 8, l, Random.State.bool st)
          else None)
        (Array.to_list pool)
    in
    let fals = List.filter_map (fun (_, l, f) -> if f then Some l else None) others in
    let free_sum =
      List.fold_left (fun acc (c, _, f) -> if f then acc else acc + c) d others
    in
    (* Degree chosen so the row PROPAGATES the pivot: slack in [0, d). *)
    let degree = free_sum - Random.State.int st d in
    if degree >= 1 then
      let row =
        Learned.make
          (List.map (fun (c, l, _) -> (c, l)) ((d, pivot, false) :: others))
          degree
      in
      let v = view row ~pivot ~falsified:fals in
      if Reduce.propagates row ~pivot ~falsified:(falsified_in fals) then
        List.iter
          (fun (r : Reduce.t) ->
            match r.reduce v with
            | None -> incr bad_lanes
            | Some o ->
                let still_propagates =
                  Reduce.propagates o.reduced ~pivot ~falsified:(falsified_in fals)
                in
                let still_conflicting =
                  Reduce.slack_with_pivot_falsified o.reduced ~pivot
                    ~falsified:(falsified_in fals)
                  < 0
                in
                if
                  not
                    (still_propagates && still_conflicting
                    && Reduce.postcondition_holds r v o)
                then incr bad_lanes)
          Reduce.reductions
  done;
  check
    (Printf.sprintf
       "M2-L5 (b): over %d pseudo-random propagating reasons, every reduction's output \
        still propagates the pivot AND still has negative slack"
       rounds)
    (!bad_lanes = 0);
  if !bad_lanes > 0 then
    Printf.printf "       %d lane(s) broke the invariant\n" !bad_lanes

(* The property above is worth nothing unless it can go red, so here is a reduction that
   breaks it, run through the same postcondition: one that weakens FALSIFIED literals
   too. Weakening a falsified literal takes its coefficient out of the degree but not out
   of the slack sum, so the slack rises by that coefficient -- and where the reason was
   tight, that is enough to lose the conflict outright.

     C = 3v + 3f >= 3,  pivot v (d = 3),  f FALSIFIED.  Slack 0, so C propagates v.

       honest      weakens nothing:        3v + 3f >= 3   / 3  ->  v + f >= 1   slack 0
       wrong       weakens f as well:      3v      >= 0   / 3  ->  v     >= 0   slack 1

   [v >= 0] is not false -- it is vacuously true, and a reduction that hands the analysis
   a vacuous reason has thrown the conflict away without saying so. The postcondition is
   what says so. *)
let test_reduce_property_has_teeth () =
  let row = Learned.make [ (3, rv); (3, ru) ] 3 in
  let v = view row ~pivot:rv ~falsified:[ ru ] in
  check "M2-L5 (b) control: the row propagates its pivot, so it is a legitimate reason"
    (Reduce.propagates row ~pivot:rv ~falsified:(falsified_in [ ru ]));
  let honest = Option.get (Reduce.round_to_one.reduce v) in
  check_eq "M2-L5 (b) control: the honest reduction keeps the falsified literal"
    ~expected:"+1 x_ge_1 +1 y_ge_2 >= 1"
    ~got:(Learned.to_string honest.reduced);
  check "M2-L5 (b) control: and it keeps the conflict"
    (Reduce.slack_with_pivot_falsified honest.reduced ~pivot:rv
       ~falsified:(falsified_in [ ru ])
     < 0
    && Reduce.postcondition_holds Reduce.round_to_one v honest);
  (* The same rule with the "never weaken a falsified literal" clause removed: weaken
     every literal but the pivot, then divide. *)
  let wrong =
    {
      Reduce.name = "weaken-everything (deliberately wrong)";
      reduce =
        (fun (vw : Reduce.view) ->
          match Reduce.round_to_one.reduce vw with
          | None -> None
          | Some o ->
              let d = o.divisor in
              let dropped =
                List.filter
                  (fun (tm : Learned.term) -> not (Lit.equal tm.lit vw.pivot))
                  (Learned.terms vw.row)
              in
              let degree =
                List.fold_left
                  (fun acc (tm : Learned.term) -> acc - tm.coeff)
                  (Learned.degree vw.row) dropped
              in
              let up x = if x <= 0 then 0 else ((x - 1) / d) + 1 in
              Some
                {
                  o with
                  reduced = Learned.make [ (1, vw.pivot) ] (up degree);
                  weakened =
                    List.map
                      (fun (tm : Learned.term) -> (tm.coeff, Lit.negate tm.lit))
                      dropped;
                });
      postcondition = Reduce.round_to_one.postcondition;
    }
  in
  match wrong.reduce v with
  | None -> check "M2-L5 (b) control: the wrong rule applies" false
  | Some o ->
      check_eq "M2-L5 (b) THE BREAK: weakening the falsified f gives a VACUOUS reason"
        ~expected:"+1 x_ge_1 >= 0" ~got:(Learned.to_string o.reduced);
      check
        "M2-L5 (b) THE BREAK: it no longer propagates the pivot and its slack is no \
         longer negative -- the conflict is gone"
        ((not (Reduce.propagates o.reduced ~pivot:rv ~falsified:(falsified_in [ ru ])))
        && Reduce.slack_with_pivot_falsified o.reduced ~pivot:rv
             ~falsified:(falsified_in [ ru ])
           >= 0);
      check
        "M2-L5 (b) THE BREAK: and the postcondition the property test uses is what says \
         so, so (b) can go red"
        (not (Reduce.postcondition_holds Reduce.round_to_one v o))

(* ------------------------------------------------------------- (c) *)

(* The model every lane of (c) is checked against.

     c1: 3v + 3u + 1w >= 5    the reason row
     c2: ~v >= 1              v is false, so the model is UNSAT (3u + w <= 4 < 5)

   Reducing c1 on pivot v derives [v >= 1] (division) or [v + u >= 2] (roundToOne); both
   imply the bound [x >= 1] the pruning claims. A TRUNCATED reduction -- roundToOne with
   its weakening step dropped, i.e. a bare division of an unweakened row -- derives
   [v + u + w >= 2], which does NOT imply [x >= 1]: by the syntactic implication rule
   2 - 1 - 1 = 0 < 1. That is the whole break, and nothing but the stated conclusion can
   see it. *)
let reduce_break_encoding () =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_int e "y" ~lo:0 ~hi:3;
  Encoding.declare_int e "z" ~lo:0 ~hi:3;
  let c1 = Encoding.add_constraint e (Opb.ge [ (3, rv); (3, ru); (1, rw) ] 5) in
  let c2 = Encoding.add_constraint e (Opb.ge [ (1, Lit.negate rv) ] 1) in
  (e, c1, c2)

(* The checker this break lane runs against. It used to be a LIST -- one entry per
   checker, each paired with the format it could read -- because a break lane measured
   against one binary says nothing about the other (M1-T46). D-0046 left one checker, so
   the list collapsed to a single entry and the pairing has nothing left to pair. The
   cost of that is recorded in D-0046 and is not hidden here: veripb 3.0.2 is now the
   sole oracle for every lane below.

   [] is a FAILURE, never a skip. *)
let reduce_break_checkers () =
  match Baguette_proof.Checker.find () with
  | None -> []
  | Some p -> [ ("veripb 3.0.2, the checker of record", p) ]

let test_reduction_truncation_is_rejected () =
  match reduce_break_checkers () with
  | [] ->
      incr failures;
      print_endline
        ("FAIL M2-L5 (c): " ^ Baguette_proof.Checker.not_found_message
       ^ " -- (c) IS the checker rejecting a truncated reduction, so with no checker \
          there is nothing here. This is not a pass.")
  | checkers -> (
      let dir = Filename.temp_file "baguette_reduce" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let log = Filename.concat dir "log" in
      let last_out = ref "" in
      (* [expl_of] picks the derivation the lane emits; [stated] decides whether the
         bound it claims reaches the page as an `ia` (M2-L0's [emit_concluding]).
         Returns [true] iff veripb ACCEPTED. *)
      let run ~veripb ~name ~stated ~expl_of =
        let e, c1, c2 = reduce_break_encoding () in
        let pbp = Filename.concat dir (name ^ ".pbp") in
        let opb = Filename.concat dir (name ^ ".opb") in
        let oc = open_out pbp in
        let w = Writer.create ~comments:false ~audit:true oc in
        let oc_opb = open_out opb in
        Encoding.write_opb e oc_opb;
        close_out oc_opb;
        Encoding.start_proof e w;
        let ctx = Justify.create ~writer:w ~encoding:e in
        let row = Learned.make [ (3, rv); (3, ru); (1, rw) ] 5 in
        let v = view row ~pivot:rv ~falsified:[] in
        let expl = expl_of v (Explanation.model_row c1) in
        let concludes = Some (Reason.at_least ~name:"x" ~decl:0 1) in
        let id =
          if stated then Justify.emit_concluding ctx ~concludes expl
          else Justify.emit ctx expl
        in
        Writer.delete w id;
        (* The contradiction is derived under its own origin, from the model rows
           directly, so every lane ends the same way and what differs between them is the
           pruning's line and nothing else. *)
        let bottom =
          Writer.pol w ~origin:"the contradiction"
            Pol.(
              add
                (div
                   (add
                      (add (id c1) (mul (axiom (Lit.negate ru)) 3))
                      (mul (axiom (Lit.negate rw)) 1))
                   3)
                (id c2))
        in
        Writer.conclusion w (Writer.Unsat (Some bottom));
        close_out oc;
        let rc =
          Sys.command
            (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
               (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
        in
        (let ic = open_in_bin log in
         last_out := really_input_string ic (in_channel_length ic);
         close_in ic);
        rc = 0
      in
      let honest (r : Reduce.t) v base = (Option.get (r.reduce v)).derive base in
      (* The truncation: roundToOne's divisor with roundToOne's weakening step dropped.
         This is not a mutation knob -- it is the defect a reduction component actually
         has, a rule that weakens less than its own definition says. *)
      let truncated _v base = Explanation.combine [ Explanation.term 1 base ] 3 in
      let contains needle hay =
        let n = String.length needle and h = String.length hay in
        let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
        n = 0 || go 0
      in
      List.iter
        (fun (label, veripb) ->
          let tag = Printf.sprintf " [%s]" label in
          let slug =
            String.map (function 'a' .. 'z' | '0' .. '9' -> '_' | c -> c) label
          in
          let slug = String.concat "" (String.split_on_char ' ' slug) in
          let run = run ~veripb in
          check
            ("M2-L5 (c) baseline: roundToOne's derivation, emitted bare, is ACCEPTED"
           ^ tag)
            (run ~name:("rto_bare" ^ slug) ~stated:false
               ~expl_of:(honest Reduce.round_to_one));
          check
            ("M2-L5 (c) baseline: roundToOne's derivation stating the bound it concluded \
              is ACCEPTED -- an honest reduction pays nothing for the `ia`" ^ tag)
            (run ~name:("rto_stated" ^ slug) ~stated:true
               ~expl_of:(honest Reduce.round_to_one));
          check
            ("M2-L5 (c) baseline: division's derivation stating the same bound is \
              ACCEPTED" ^ tag)
            (run ~name:("div_stated" ^ slug) ~stated:true
               ~expl_of:(honest Reduce.division));
          check
            ("M2-L5 (c) THE GAP: the reduction TRUNCATED -- divided without its \
              weakening step, so it derives v+u+w >= 2 where roundToOne derives v+u >= 2 \
              -- is still ACCEPTED bare. A bare `pol` checks well-formedness, not what \
              was claimed." ^ tag)
            (run ~name:("trunc_bare" ^ slug) ~stated:false ~expl_of:truncated);
          check
            ("M2-L5 (c) THE CONTROL M1-T42 COULD NOT BUILD: the same truncated reduction \
              is REJECTED once M2-L0's conclusion is stated" ^ tag)
            (not (run ~name:("trunc_stated" ^ slug) ~stated:true ~expl_of:truncated));
          (* Which rejection it is, named at full strength: the implication check, not a
             parse error and not a dangling label. The fragment "reverse unit
             propagation" is deliberately not used -- it is the least specific thing the
             checker says, and this is an implication failure, not a RUP one. *)
          let wordings =
            [ ("\"not syntactically implied\"", "not syntactically implied") ]
          in
          let hit = List.filter (fun (_, needle) -> contains needle !last_out) wordings in
          let matched = hit <> [] in
          if matched then
            Printf.printf "note M2-L5 (c)%s said: %s\n" tag
              (String.concat " + " (List.map fst hit));
          check
            ("M2-L5 (c): the rejection is the IMPLICATION check -- \"Expected constraint \
              is not syntactically implied by the constraint at the hint.\" -- not a \
              parse error and not a dangling label" ^ tag)
            matched;
          if not matched then
            Printf.printf "       checker said: %s\n" (String.trim !last_out))
        checkers;
      Sys.readdir dir
      |> Array.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ());
      try Sys.rmdir dir with _ -> ())

let () =
  test_model_row ();
  test_decision_has_no_id ();
  test_emit_rup_clause ();
  test_index_reuses_the_right_line ();
  test_index_is_structural ();
  test_index_ignores_clause_order ();
  test_index_levels ();
  test_defining_lit ();
  test_memoisation ();
  test_linear_states_its_own_terms ();
  test_deferred_linear ();
  test_deferred_cut ();
  test_wipe ();
  run_veripb ~name:"justify: a Linear explanation, checked end to end"
    ~build:build_linear_proof;
  run_veripb ~name:"justify: a Cut of two Linears, checked end to end"
    ~build:build_cut_proof;
  run_veripb
    ~name:"justify: a real int_lin_le pruning (one-step bound), checked end to end"
    ~build:build_int_lin_le_ok;
  run_veripb ~name:"justify: a real int_lin_le pruning (two-step bound, the D-0010 chain)"
    ~build:build_int_lin_le_gap;
  test_d0013_conflict ();
  test_conclusion_rejects_a_weakened_pol ();
  test_reduce_pins_both_rules ();
  test_reduce_never_weakens_a_falsified_literal ();
  test_reduce_is_a_no_op_at_divisor_one ();
  test_reduce_declines ();
  test_reduce_preserves_the_conflicting_invariant ();
  test_reduce_property_has_teeth ();
  test_reduction_truncation_is_rejected ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\njustify unit tests passed"
