(* The integration test: model -> propagators -> engine -> search -> proof -> veripb.

   Owned by the orchestrator, deliberately. Every bug found in M1 so far was invisible
   to the session that wrote the code and to its own green test suite, and showed up
   only when the halves were run together against the real checker. This file is where
   that happens on purpose.

   What it covers that the per-area suites do not:

   1. **Integer variables wider than [0, 1].** Every search proof in test_engine.ml uses
      0/1 domains, where x = [x >= 1] and every bound fact is exactly one step from its
      declared bound. That is the value at which D-0010's bug was invisible, so a search
      proof over 0/1 variables exercises none of the order-encoding chain machinery. The
      models here use [0, 3].

   2. **Model rows built by the real expansion.** test_engine.ml writes its PB rows by
      hand over [x >= 1] literals, which is correct only because its domains are 0/1.
      Here the rows come from Encoding.add_int_lin_le (M1-T7c), so the constant folding
      and the sign handling are the ones the solver would really use.

   3. **A search tree deeper than one decision**, with backtracking at more than one
      level, so nogood resolution is exercised rather than just nogood emission.

   The models are chosen so that bounds propagation provably cannot settle them and the
   search really has to branch. Both turn on a parity argument, which bounds reasoning
   cannot see:

     x1 = x2, x3 = x4, all in [0, 3], x1 + x2 + x3 + x4 = k
     i.e. 2*(x1 + x3) = k, which has no integer solution for odd k.

   k = 7 is therefore UNSAT, but no bound is ever contradicted at the root: the sum lies
   in [0, 12] and each pair only forces its partner. The solver must enumerate. k = 8 is
   SAT at (1, 1, 3, 3), and first-fail/indomain-min reaches it only after x1 = 0 fails,
   so the SAT proof carries a real backtrack too. *)

module Lit = Baguette_proof.Lit
module Encoding = Baguette_proof.Encoding
module Writer = Baguette_proof.Writer
module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Lin_eq = Baguette_core.Lin_eq
module Engine = Baguette_core.Engine
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let var = Var.of_int

(* Four variables over [0, 3]: wide enough that a bound fact is several order-encoding
   steps from its declared bound, which is the case 0/1 domains cannot produce. *)
let names = [| "x1"; "x2"; "x3"; "x4" |]
let lo, hi = (0, 3)

let mk_store () =
  Store.create ~names
    ~domains:(Array.map (fun _ -> Domain.make lo hi) names)

let pack ~id (lin : Linear.t) =
  Propagator.pack ~id (module Linear : Propagator.S with type t = Linear.t) lin

(* x1 = x2, x3 = x4, and x1 + x2 + x3 + x4 = k, as eight Linear instances: each
   equality posts as its own (le, ge) pair, one instance per model row (D-0011). *)
let build_store_and_engine k =
  let store = mk_store () in
  let x1, x2, x3, x4 = (var 0, var 1, var 2, var 3) in
  let eq12_le, eq12_ge = Lin_eq.make store [ (1, x1); (-1, x2) ] 0 in
  let eq34_le, eq34_ge = Lin_eq.make store [ (1, x3); (-1, x4) ] 0 in
  let sum_le, sum_ge =
    Lin_eq.make store [ (1, x1); (1, x2); (1, x3); (1, x4) ] k
  in
  let engine =
    Engine.create
      [
        pack ~id:0 eq12_le;
        pack ~id:1 eq12_ge;
        pack ~id:2 eq34_le;
        pack ~id:3 eq34_ge;
        pack ~id:4 sum_le;
        pack ~id:5 sum_ge;
      ]
  in
  (store, engine)

(* The same model as PB rows, through the real order-encoding expansion rather than by
   hand. Every equality is posted as its two >= rows explicitly: an .opb line with `=`
   counts as TWO constraints for the `f` rule (PROOF-FORMAT section 2, trap 1), which is
   why Encoding refuses Eq outright. *)
let negate_terms terms = List.map (fun (a, x) -> (-a, x)) terms

let add_equality_rows e terms rhs =
  let le = Encoding.add_int_lin_le e terms rhs in
  let ge = Encoding.add_int_lin_le e (negate_terms terms) (-rhs) in
  (le, ge)

let build_encoding k =
  let e = Encoding.create () in
  Array.iter (fun n -> Encoding.declare_int e n ~lo ~hi) names;
  ignore (add_equality_rows e [ (1, "x1"); (-1, "x2") ] 0);
  ignore (add_equality_rows e [ (1, "x3"); (-1, "x4") ] 0);
  ignore
    (add_equality_rows e [ (1, "x1"); (1, "x2"); (1, "x3"); (1, "x4") ] k);
  e

(* Search never renders Explanation.Trivial (see search.ml's header), so a model_id
   lookup being consulted at all would itself be the bug. *)
let mk_ctx writer encoding =
  Justify.create ~writer ~encoding ~model_id:(fun () ->
      failwith "integration: search demanded Explanation.Trivial")

(* I-S1: re-check a solution against the model directly, never by trusting the
   propagators that produced it. *)
let independent_check k (assignment : Search.assignment) =
  let v i = List.assoc (var i) assignment in
  let x1, x2, x3, x4 = (v 0, v 1, v 2, v 3) in
  List.for_all (fun x -> x >= lo && x <= hi) [ x1; x2; x3; x4 ]
  && x1 = x2 && x3 = x4
  && x1 + x2 + x3 + x4 = k

let veripb_path () =
  let candidates =
    [ Filename.concat (Sys.getenv "HOME") ".local/bin/veripb"; "veripb" ]
  in
  List.find_opt
    (fun p -> Sys.file_exists p || Sys.command (Printf.sprintf "command -v %s >/dev/null 2>&1" (Filename.quote p)) = 0)
    candidates

(* Run one model end to end and hand back what veripb said, plus the proof text so a
   caller can assert on what was actually emitted rather than only on the exit code. *)
let run_model ~k ~expect_sat ~xfail_veripb =
  let dir = Filename.temp_file "baguette_e2e" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "model.opb" in
  let pbp = Filename.concat dir "model.pbp" in
  let store, engine = build_store_and_engine k in
  let encoding = build_encoding k in
  let oc = open_out opb in
  Encoding.write_opb
    ~comments:[ Printf.sprintf "x1 = x2, x3 = x4, x1+x2+x3+x4 = %d, all in [0,3]" k ]
    encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let entry_level = Store.level store in
  let outcome =
    Search.solve ~engine ~store ~ctx ~check:(independent_check k) ()
  in
  close_out oc;
  let exit_level = Store.level store in
  let proof =
    let ic = open_in_bin pbp in
    let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s
  in
  let tag = Printf.sprintf "k=%d" k in
  (match outcome with
  | Search.Sat assignment ->
      check (Printf.sprintf "%s: search reports SAT as expected" tag) expect_sat;
      check
        (Printf.sprintf "%s: the solution independently satisfies the model (I-S1)" tag)
        (independent_check k assignment)
  | Search.Unsat ->
      check (Printf.sprintf "%s: search reports UNSAT as expected" tag) (not expect_sat));
  check
    (Printf.sprintf "%s: decision level restored on return (I-S3)" tag)
    (entry_level = exit_level);
  let rc =
    match veripb_path () with
    | None -> -1
    | Some veripb ->
        let log = Filename.concat dir "log" in
        let rc =
          Sys.command
            (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
               (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
        in
        if rc <> 0 then (
          let ic = open_in_bin log in
          let s = really_input_string ic (in_channel_length ic) in
          close_in ic;
          let ic = open_in_bin opb in
          let m = really_input_string ic (in_channel_length ic) in
          close_in ic;
          Printf.printf "  veripb said:\n%s\n  model was:\n%s\n  proof was:\n%s\n" s m proof);
        rc
  in
  (match veripb_path () with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- I-X1 was NOT checked. Do not treat this as a pass.\n"
        tag
  | Some _ ->
      if not xfail_veripb then
        check (Printf.sprintf "%s: veripb accepts the search proof (I-X1)" tag) (rc = 0)
      else if rc = 0 then (
        (* Same discipline as test/models/PENDING: a known failure that starts passing
           fails the suite, so the list cannot rot into quietly-broken things. *)
        incr failures;
        Printf.printf
          "XPASS %s: veripb now ACCEPTS this proof. M1-T10's nogood scheme was fixed \
           (or the model stopped exercising the gap). Delete ~xfail_veripb here and \
           close out D-0012.\n"
          tag)
      else
        Printf.printf
          "xfail %s: veripb rejects the search proof -- M1-T10 is reopened, see D-0012. \
           The solver's ANSWER is correct; its proof is not.\n"
          tag);
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp; Filename.concat dir "log" ];
  (try Sys.rmdir dir with _ -> ());
  proof

(* Count how many decisions the proof actually opened. A proof that never opened a
   second level would mean the model was settled by propagation alone, and this file
   would be testing nothing it claims to test. *)
let count_occurrences needle s =
  let n = String.length needle in
  let rec go i acc =
    if i + n > String.length s then acc
    else if String.sub s i n = needle then go (i + 1) (acc + 1)
    else go (i + 1) acc
  in
  go 0 0

let () =
  print_endline "";
  (* k=7 is the one that exposes D-0012: its UNSAT proof leans on the branch nogoods
     being RUP-derivable, and over [0,3] domains they are not. k=8 passes because
     `conclusion SAT` checks the assignment against the model, so its nogoods carry no
     weight -- which is precisely why a SAT-only end-to-end test proves little here. *)
  let unsat_proof = run_model ~k:7 ~expect_sat:false ~xfail_veripb:true in
  let sat_proof = run_model ~k:8 ~expect_sat:true ~xfail_veripb:false in
  (* The point of these models is that bounds propagation cannot settle them. If the
     search never branched twice, the parity argument was being decided some other way
     and the deeper tree this file exists to exercise was never built. *)
  check "k=7: the search really branched (more than one decision level opened)"
    (count_occurrences "# 2" unsat_proof > 0);
  check "k=8: the SAT run backtracked at least once"
    (count_occurrences "w " sat_proof > 0);
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nend-to-end tests passed"
