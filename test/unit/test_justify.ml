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

let () =
  test_trivial ();
  test_memoisation ();
  test_deferred_linear ();
  test_deferred_cut ();
  test_wipe ();
  run_veripb ~name:"justify: a Linear explanation, checked end to end"
    ~build:build_linear_proof;
  run_veripb ~name:"justify: a Cut of two Linears, checked end to end"
    ~build:build_cut_proof;
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\njustify unit tests passed"
