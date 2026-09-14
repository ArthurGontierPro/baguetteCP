(* Unit tests for Justify: Explanation.t rendered into VeriPB proof rules.

   Follows test_proof.ml's shape: cheap unit checks against captured proof text, plus
   real invocations of veripb for the cases that matter for I-X1 ("every emitted rule
   is accepted by VeriPB"). A test that only inspects the text we wrote and never runs
   the checker is half a test (CLAUDE.md) -- tests 1 and 2 below run veripb for real. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding
module Explanation = Baguette_core.Explanation
module Justify = Baguette_core.Justify
module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Lin_eq = Baguette_core.Lin_eq

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
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> c) in
  (e, ctx, c)

(* Two int variables [x], [y], two model constraints [x >= 2] and [y >= 1], and two
   ctx views over the same underlying writer/encoding/memo, each pointed at its own
   constraint (see Justify.for_constraint). Used by the Cut tests. *)
let build_two_ctx w =
  let e = Encoding.create () in
  Encoding.declare_int e "x" ~lo:0 ~hi:3;
  Encoding.declare_int e "y" ~lo:0 ~hi:3;
  let cx = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1) in
  let cy = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "y" 1) ] 1) in
  Encoding.start_proof e w;
  let ctx_x = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> cx) in
  let ctx_y = Justify.for_constraint ctx_x (fun () -> cy) in
  (e, ctx_x, ctx_y)

(* ------------------------------------------------------------------ *)
(* 5. Trivial: returns the model constraint id, emits nothing.        *)
(* ------------------------------------------------------------------ *)

let test_trivial () =
  let _, r =
    emitted (fun w ->
        let _, ctx, c = build_ctx w in
        let last0 = Writer.last_id w in
        let live0 = Writer.live_count w in
        let id = Justify.emit ctx Explanation.trivial in
        check "trivial: returns the model constraint's own id" (id = c);
        check "trivial: mints no new id" (Writer.last_id w = last0);
        check "trivial: adds no live entry" (Writer.live_count w = live0))
  in
  expect_ok "trivial: no exception" r

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
  let lines = String.split_on_char '\n' s in
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
        let _, ctx_x, ctx_y = build_two_ctx w in
        let ex = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
        let ey = Explanation.linear [ (1, Lit.ge "y" 1) ] 1 in
        ignore (Justify.emit ctx_x ex);
        ignore (Justify.emit ctx_y ey);
        ignore (Justify.emit ctx_x (Explanation.cut ex ey 1 1)))
  in
  let calls = ref 0 in
  let deferred_text =
    text (fun w ->
        let _, ctx_x, ctx_y = build_two_ctx w in
        let ex = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
        let ey = Explanation.linear [ (1, Lit.ge "y" 1) ] 1 in
        ignore (Justify.emit ctx_x ex);
        ignore (Justify.emit ctx_y ey);
        let d =
          Explanation.deferred (fun () ->
              incr calls;
              Explanation.cut ex ey 1 1)
        in
        let id1 = Justify.emit ctx_x d in
        let id2 = Justify.emit ctx_x d in
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
        let c0 = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 1) ] 1) in
        let c2 = Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x" 2) ] 1) in
        Encoding.start_proof e w;
        let ctx0 = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> c0) in
        let expl0 = Explanation.linear [ (1, Lit.ge "x" 1) ] 1 in
        let id0 = Justify.emit ctx0 expl0 in
        (* id0 is tagged at level 0. Everything from here on is tagged at level 2. *)
        Writer.set_level w 2;
        let ctx2 = Justify.for_constraint ctx0 (fun () -> c2) in
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

let veripb_path () =
  let candidates =
    [
      Filename.concat
        (Sys.getenv_opt "HOME" |> Option.value ~default:"")
        ".local/bin/veripb";
    ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some p -> Some p
  | None ->
      if Sys.command "command -v veripb >/dev/null 2>&1" = 0 then Some "veripb" else None

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
  let ctx = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> c_x2) in
  let expl = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
  let derived = Justify.emit ctx expl in
  Writer.delete w derived;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits e [ ("x", 2) ]));
  close_out oc;
  (opb, pbp)

(* Model: x, y in [0,3], model constraints [x >= 2] and [y >= 1]. A [Cut] of the two
   matching [Linear] explanations, coefficients 1 and 1: each child is pre-emitted
   through its own [for_constraint] view so the Cut's shared ctx never has to resolve
   either leaf itself -- see the Justify header comment on cross-constraint Cuts. *)
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
  let ctx_x = Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> c_x2) in
  let ctx_y = Justify.for_constraint ctx_x (fun () -> c_y1) in
  let ex = Explanation.linear [ (1, Lit.ge "x" 2) ] 1 in
  let ey = Explanation.linear [ (1, Lit.ge "y" 1) ] 1 in
  let id_x = Justify.emit ctx_x ex in
  let id_y = Justify.emit ctx_y ey in
  (* This ctx's own model_id must never be consulted: both children are already
     memoised, so the Cut recursion hits the memo instead of falling through to it. *)
  let ctx_cut =
    Justify.for_constraint ctx_x (fun () ->
        failwith "Cut should not need to resolve either leaf itself")
  in
  let id_cut = Justify.emit ctx_cut (Explanation.cut ex ey 1 1) in
  Writer.delete_many w [ id_x; id_y; id_cut ];
  Writer.conclusion w
    (Writer.Sat (Encoding.assignment_lits e [ ("x", 2); ("y", 1) ]));
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
  let c_bound =
    Encoding.add_constraint e (Opb.ge [ (1, Lit.ge "x2" x2_lo) ] 1)
  in
  let model_row =
    Encoding.add_constraint e
      (Opb.le (telescope 1 "x1" 5 @ telescope 1 "x2" 5) rhs)
  in
  let opb = Filename.concat dir (tag ^ ".opb") in
  let pbp = Filename.concat dir (tag ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb
    ~comments:[ Printf.sprintf "x1 + x2 <= %d; x2 >= %d" rhs x2_lo ]
    e oc;
  close_out oc;
  (* D-0010: the store's declared domains must agree with the encoding's, because the
     model row's constant comes from one and the explanation's chain offset from the
     other. So x2 is *declared* [0, 5] here, matching [declare_int] above, and the fact
     "x2 >= x2_lo" is applied below as a pruning -- after [make] has frozen the declared
     bounds -- rather than smuggled in as a narrower initial domain. *)
  let store =
    Store.create ~names:[| "x1"; "x2" |]
      ~domains:[| Domain.make 0 5; Domain.make 0 5 |]
  in
  let lin = Linear.make store [ (1, Var.of_int 0); (1, Var.of_int 1) ] rhs ~row_id:model_row in
  (match Store.set_lo store (Var.of_int 1) x2_lo (Explanation.model_row c_bound) with
  | Store.Conflict _ -> failwith "setup_int_lin_le: x2 >= x2_lo conflicts"
  | Store.Unchanged | Store.Changed -> ());
  (match Linear.propagate lin store with
  | Propagator.Conflict _ -> failwith "setup_int_lin_le: expected a Fixpoint, got Conflict"
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
  (* [expl]'s base is [Model_row model_row], not [Trivial] (D-0013 / explanation.ml's
     header): [ctx.model_id] should never be consulted, so make it fail if it ever
     is. *)
  let ctx =
    Justify.create ~writer:w ~encoding:e
      ~model_id:(fun () ->
        failwith
          "build_int_lin_le_ok: ctx.model_id was consulted -- expl's base should be \
           Model_row, not Trivial")
  in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w
    (Writer.Sat (Encoding.assignment_lits e [ ("x1", 0); ("x2", 1) ]));
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
  let ctx =
    Justify.create ~writer:w ~encoding:e
      ~model_id:(fun () ->
        failwith
          "build_int_lin_le_gap: ctx.model_id was consulted -- expl's base should be \
           Model_row, not Trivial")
  in
  let id = Justify.emit ctx expl in
  Writer.delete w id;
  Writer.conclusion w
    (Writer.Sat (Encoding.assignment_lits e [ ("x1", 0); ("x2", 2) ]));
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
(* veripb 2.2.2 in full; this test is what checks the *solver*         *)
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
  let opb_terms, const =
    Encoding.linear_terms_int_lin_le e [ (2, "x1"); (4, "x2") ]
  in
  let geq_id, leq_id = Encoding.add_equality e opb_terms (7 - const) in
  let store =
    Store.create ~names:[| "x1"; "x2" |] ~domains:[| Domain.make 0 3; Domain.make 0 3 |]
  in
  let le, ge =
    Lin_eq.make store [ (2, Var.of_int 0); (4, Var.of_int 1) ] 7 ~le_id:leq_id ~ge_id:geq_id
  in
  let outcome = propagate_pair (le, ge) store in
  (e, opb_terms, geq_id, leq_id, outcome)

let build_d0013_conflict dir =
  let e, opb_terms, _geq_id, _leq_id, outcome = setup_d0013 () in
  let expl =
    match outcome with
    | Propagator.Conflict e -> Explanation.force e
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
  let ctx =
    Justify.create ~writer:w ~encoding:e
      ~model_id:(fun () ->
        failwith
          "build_d0013_conflict: ctx.model_id was consulted -- every base in this \
           derivation should be Model_row, not Trivial")
  in
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
          | Propagator.Conflict e -> Explanation.force e
          | Propagator.Fixpoint -> failwith "test_d0013_conflict: expected a Conflict"
        in
        let e = Encoding.create () in
        Encoding.declare_int e "x1" ~lo:0 ~hi:3;
        Encoding.declare_int e "x2" ~lo:0 ~hi:3;
        let opb_terms, const = Encoding.linear_terms_int_lin_le e [ (2, "x1"); (4, "x2") ] in
        let _geq_id, _leq_id = Encoding.add_equality e opb_terms (7 - const) in
        Encoding.start_proof e w;
        let ctx =
          Justify.create ~writer:w ~encoding:e ~model_id:(fun () -> failwith "unused")
        in
        ignore (Justify.emit ctx expl))
  in
  let ends_with suffix s =
    let ls = String.length s and lsuf = String.length suffix in
    ls >= lsuf && String.sub s (ls - lsuf) lsuf = suffix
  in
  let lines = String.split_on_char '\n' s in
  check "D-0013: some step divides by 4 (x2's own coefficient)"
    (List.exists (fun l -> String.length l > 0 && l.[0] = 'p' && ends_with " 4 d" l) lines);
  check "D-0013: some step divides by 2 (x1's own coefficient)"
    (List.exists (fun l -> String.length l > 0 && l.[0] = 'p' && ends_with " 2 d" l) lines);
  run_veripb ~name:"D-0013: 2x1+4x2=7 in [0,3]^2, root conflict, checked end to end"
    ~build:build_d0013_conflict

let () =
  test_trivial ();
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
  run_veripb
    ~name:"justify: a real int_lin_le pruning (two-step bound, the D-0010 chain)"
    ~build:build_int_lin_le_gap;
  test_d0013_conflict ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\njustify unit tests passed"
