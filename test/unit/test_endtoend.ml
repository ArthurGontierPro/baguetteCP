(* The integration test: model -> propagators -> engine -> search -> proof -> veripb.

   Owned by the orchestrator, deliberately. Every bug found in M1 so far was invisible
   to the session that wrote the code and to its own green test suite, and showed up
   only when the halves were run together against the real checker. This file is where
   that happens on purpose.

   What it covers that the per-area suites do not:

   1. **Integer variables, not 0/1 flags.** test_engine.ml's search proofs use [0, 1]
      domains, where x = [x >= 1], the order encoding degenerates into clauses, and PB
      unit propagation is as strong as bounds propagation. That is why D-0012 was
      invisible to it. The models here use wide domains, including ones that do not start
      at zero and ones that run negative, so a bound fact is several order-encoding steps
      from its declared bound and the expansion's constant is not zero.

   2. **Coefficients other than 1 and -1.** With unit coefficients a bounds push never
      divides, so the rounding half of int_lin_le (PROOF-FORMAT section 4 promises "one
      division", floor or ceil by sign) is never exercised. Several models below have
      coefficients 2, 3, 4 and negatives, chosen so pushes land on non-integer quotients.

   3. **Model rows built by the real expansion**, from Encoding.add_int_lin_le (M1-T7c),
      not written by hand over [x >= 1] literals.

   4. **The expected answer is computed by brute force**, never asserted by hand. Each
      model is enumerated over its full box and the solver must agree with that. A test
      whose expected answer is hand-written is a test that can be talked into agreeing
      with a bug.

   Several models are UNSAT by parity or divisibility, which bounds reasoning cannot see,
   so the search has to branch rather than being settled at the root.

   Note the asymmetry, recorded in D-0012: a SAT run's proof is accepted almost
   regardless, because `conclusion SAT` checks the assignment against the model rather
   than anything the search derived. Only the UNSAT proofs test the search's reasoning. *)

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
module Explanation = Baguette_core.Explanation
module Alldiff = Baguette_core.Alldiff

(* M1-T53: the inner heap guard. test_prop.exe is the binary that reached 14.9 GB RSS on
   2026-09-16 and had to be killed by hand, so a guard that covered only test_output and
   test_compile would have missed the one incident it exists to prevent. `ulimit -v` stays
   the outer backstop -- see mem_guard.ml's header for what this cannot see. *)
let () = Mem_guard.install ()

(* D-0201: this suite was written against the ORDER encoding -- its scenes name x_ge_v
   rungs, ladder rows and order-encoding counts -- which stopped being the default when
   D-0199 made it `--bits-above 0`. Pinned before any test runs, so every scene keeps the
   encoding it was measured on; a bits test sets its own W and restores this one. *)
let () = Baguette_proof.Encoding.bits_above := None
let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* A term is (coefficient, variable index). Turning these into PB rows is Encoding's
   job, not this file's. *)
type cstr = Le of (int * int) list * int | Eq of (int * int) list * int

type model = {
  title : string;
  vars : (string * int * int) array; (* name, lo, hi *)
  cstrs : cstr list;
  needs_search : bool; (* bounds propagation alone cannot settle it *)
}

let models =
  [
    {
      title = "parity, unit coefficients, [0,3]";
      vars = [| ("x1", 0, 3); ("x2", 0, 3); ("x3", 0, 3); ("x4", 0, 3) |];
      cstrs =
        [
          Eq ([ (1, 0); (-1, 1) ], 0);
          Eq ([ (1, 2); (-1, 3) ], 0);
          Eq ([ (1, 0); (1, 1); (1, 2); (1, 3) ], 7);
        ];
      needs_search = true;
    };
    {
      title = "parity, unit coefficients, [0,3], satisfiable";
      vars = [| ("x1", 0, 3); ("x2", 0, 3); ("x3", 0, 3); ("x4", 0, 3) |];
      cstrs =
        [
          Eq ([ (1, 0); (-1, 1) ], 0);
          Eq ([ (1, 2); (-1, 3) ], 0);
          Eq ([ (1, 0); (1, 1); (1, 2); (1, 3) ], 8);
        ];
      needs_search = true;
    };
    {
      title = "divisibility, coefficients 2 and 4, [0,3]";
      vars = [| ("x1", 0, 3); ("x2", 0, 3) |];
      cstrs = [ Eq ([ (2, 0); (4, 1) ], 7) ];
      (* Bounds propagation settles this at the root: the >= row forces x2 >= 1, the <=
         row forces x2 <= 1, and 2*x1 = 3 then has no integer solution. Kept because it
         exercises rounding in both directions with no search at all -- and because its
         proof is rejected too, which shows D-0012 is not only about branching. *)
      needs_search = false;
    };
    {
      title = "mixed signs, negative domain, coefficients 2 and -4";
      vars = [| ("x1", 0, 3); ("x2", -2, 2) |];
      cstrs = [ Eq ([ (2, 0); (-4, 1) ], 3) ];
      (* Also root-refutable: x2 is squeezed to 0 from both sides, leaving 2*x1 = 3. *)
      needs_search = false;
    };
    {
      (* Even left-hand side, odd right-hand side, but with a spread of coefficients and
         enough slack that no bound is contradicted at the root: this one has to branch
         on x2 and refute both children, with divisions in every push. *)
      title = "parity with coefficients 2, 6, 2 -- needs a decision";
      vars = [| ("x1", 0, 3); ("x2", 0, 3); ("x3", 0, 3) |];
      cstrs = [ Eq ([ (2, 0); (6, 1); (2, 2) ], 9) ];
      needs_search = true;
    };
    {
      title = "varied coefficients and offset domains, satisfiable";
      vars = [| ("x1", 1, 4); ("x2", -1, 2); ("x3", -2, 5) |];
      cstrs =
        [
          Eq ([ (3, 0); (-2, 1); (1, 2) ], 4);
          Le ([ (1, 0); (1, 1); (1, 2) ], 6);
          Le ([ (-1, 0); (2, 2) ], 3);
        ];
      needs_search = false;
    };
    {
      title = "common factor 3, right-hand side 5, offset domains";
      vars = [| ("x1", -1, 3); ("x2", 0, 4); ("x3", 2, 6) |];
      cstrs = [ Eq ([ (3, 0); (3, 1); (-3, 2) ], 5) ];
      needs_search = true;
    };
  ]

(* The independent oracle: enumerate the whole box. This is the only thing here that
   says what the answer should be, and the solver is required to agree with it. *)
let evaluate cstrs (assign : int array) =
  let value terms = List.fold_left (fun acc (a, i) -> acc + (a * assign.(i))) 0 terms in
  List.for_all
    (function
      | Le (terms, rhs) -> value terms <= rhs | Eq (terms, rhs) -> value terms = rhs)
    cstrs

let brute_force m =
  let n = Array.length m.vars in
  let assign = Array.make n 0 in
  let found = ref None in
  let rec go i =
    if !found <> None then ()
    else if i = n then (if evaluate m.cstrs assign then found := Some (Array.copy assign))
    else
      let _, lo, hi = m.vars.(i) in
      for v = lo to hi do
        if !found = None then (
          assign.(i) <- v;
          go (i + 1))
      done
  in
  go 0;
  !found

let build_store m =
  Store.create
    ~names:(Array.map (fun (n, _, _) -> n) m.vars)
    ~domains:(Array.map (fun (_, lo, hi) -> Domain.make lo hi) m.vars)

let pack ~id (lin : Linear.t) =
  Propagator.pack ~id (module Linear : Propagator.S with type t = Linear.t) lin

(* A <= is one Linear instance; an equality is its (le, ge) pair -- two instances, one
   per model row (D-0011). *)
let build_engine m store ids =
  let to_vars terms = List.map (fun (a, i) -> (a, Var.of_int i)) terms in
  let instances =
    List.concat
    @@ List.map2
         (fun cstr id ->
           match (cstr, id) with
           | Le (terms, rhs), `Le row_id ->
               [ Linear.make ~row_id store (to_vars terms) rhs ]
           | Eq (terms, rhs), `Eq (le_id, ge_id) ->
               let le, ge = Lin_eq.make ~le_id ~ge_id store (to_vars terms) rhs in
               [ le; ge ]
           | _ -> assert false)
         m.cstrs ids
  in
  Engine.create (List.mapi (fun id lin -> pack ~id lin) instances)

(* An equality posts as its two >= rows explicitly: an .opb line with `=` counts as TWO
   constraints for the `f` rule (PROOF-FORMAT section 2, trap 1). *)
let build_encoding m =
  let e = Encoding.create () in
  Array.iter (fun (n, lo, hi) -> Encoding.declare_int e n ~lo ~hi) m.vars;
  let to_names terms =
    List.map
      (fun (a, i) ->
        let n, _, _ = m.vars.(i) in
        (a, n))
      terms
  in
  let negate terms = List.map (fun (a, x) -> (-a, x)) terms in
  (* Each propagator instance must justify against its OWN row (D-0011), so the ids are
     kept and threaded to build_engine rather than discarded. Without that every
     explanation falls back to Trivial, which cannot say which row it meant. *)
  let ids =
    List.map
      (function
        | Le (terms, rhs) -> `Le (Encoding.add_int_lin_le e (to_names terms) rhs)
        | Eq (terms, rhs) ->
            let t = to_names terms in
            let le_id = Encoding.add_int_lin_le e t rhs in
            let ge_id = Encoding.add_int_lin_le e (negate t) (-rhs) in
            `Eq (le_id, ge_id))
      m.cstrs
  in
  (e, ids)

(* M1-T31: a [ctx] has no ambient row. This used to pass a [~model_id] thunk that
   failed if ever consulted, because [Explanation.Trivial] could still resolve through
   it; every explanation now names its own row with [Model_row]. *)
let mk_ctx writer encoding = Justify.create ~writer ~encoding

(* I-S1: re-check against the model itself, never by trusting the propagators. *)
let independent_check m (assignment : Search.assignment) =
  let n = Array.length m.vars in
  let assign = Array.make n 0 in
  List.iter (fun (v, value) -> assign.(Var.to_int v) <- value) assignment;
  let in_box = ref true in
  Array.iteri
    (fun i (_, lo, hi) -> if assign.(i) < lo || assign.(i) > hi then in_box := false)
    m.vars;
  !in_box && evaluate m.cstrs assign

(* Which checker to run: lib/proof/checker.ml, shared with scripts/checker.sh.
   Every test module open-coded this search, and every copy resolved it differently --
   so a project-wide choice of checker lived in nine places and could silently mean a
   build nobody intended (M1-T18). [None] is a FAILURE at every
   call site below, never a skip. *)
let veripb_path () = Baguette_proof.Checker.find ()

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let run_model m =
  let expected = brute_force m in
  let expect_sat = expected <> None in
  let dir = Filename.temp_file "baguette_e2e" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "model.opb" in
  let pbp = Filename.concat dir "model.pbp" in
  let store = build_store m in
  let encoding, ids = build_encoding m in
  let engine = build_engine m store ids in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ m.title ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:true ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let entry_level = Store.level store in
  let outcome = Search.solve ~engine ~store ~ctx ~check:(independent_check m) () in
  close_out oc;
  let exit_level = Store.level store in
  let proof = read_file pbp in
  let tag = m.title in
  (match outcome with
  | Search.Sat assignment ->
      check (Printf.sprintf "%s: agrees with brute force (SAT)" tag) expect_sat;
      check
        (Printf.sprintf "%s: the solution independently satisfies the model (I-S1)" tag)
        (independent_check m assignment)
  | Search.Unsat ->
      check (Printf.sprintf "%s: agrees with brute force (UNSAT)" tag) (not expect_sat));
  check
    (Printf.sprintf "%s: decision level restored on return (I-S3)" tag)
    (entry_level = exit_level);
  if m.needs_search then
    check
      (Printf.sprintf "%s: the search really branched" tag)
      (Writer.opens_level 1 proof);
  (* There is no xfail here any more. M1-T13 (docs/DECISIONS.md D-0018) closed the
     branching case: a branch's own propagation trace is logged, so the nogood over the
     decision literals is ordinary RUP and every model in this table verifies. The three
     models that used to be marked -- the D-0012 parity instances -- are exactly the ones
     that now exercise the trace, so they are the last ones that should be excused. *)
  let xfail_veripb = false in
  (match veripb_path () with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- I-X1 was NOT checked. Do not treat this as a pass.\n"
        tag
  | Some veripb ->
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      if not xfail_veripb then (
        check (Printf.sprintf "%s: veripb accepts the search proof (I-X1)" tag) (rc = 0);
        if rc <> 0 then
          Printf.printf "  veripb said:\n%s\n  model:\n%s\n  proof:\n%s\n" (read_file log)
            (read_file opb) proof)
      else if rc = 0 then (
        incr failures;
        Printf.printf
          "XPASS %s: veripb now ACCEPTS this UNSAT proof. Either D-0012 is fixed or this \
           model stopped exercising it -- check which, then remove the xfail.\n"
          tag)
      else
        Printf.printf
          "xfail %s: veripb rejects the UNSAT proof (D-0012). The answer is right; the \
           proof is not.\n"
          tag);
  List.iter
    (fun f -> try Sys.remove f with _ -> ())
    [ opb; pbp; Filename.concat dir "log" ];
  try Sys.rmdir dir with _ -> ()

(* M1-T48 tripwire. `Writer.comment` has exactly three callers, all in the M4
   direct-encoding path (lib/proof/encoding.ml), which no current model reaches -- so
   `--proof-comments` is a no-op on every model in test/models/ today, and nothing was
   watching that. This test pins the no-op down two ways:

   1. Directly against Writer.comment: with [comments:false] it must emit nothing at
      all (not even a suppressed attempt reaching the channel); with [comments:true] it
      must emit the line. This is the actual mechanism the flag switches, exercised
      independently of any caller.

   2. End-to-end against a real model+proof, run twice with the two settings: the
      emitted .pbp must be byte-identical, matching M1-T47's finding on all 30 shipped
      models. The day a propagator or M4's direct-encoding path starts calling
      Writer.comment on a reachable path, this half goes red -- which is the point: it
      is the signal that the CLI usage text (bin/main.ml) needs updating again. *)
let test_proof_comments_noop () =
  (* (1) the mechanism itself *)
  let with_flag flag =
    let path = Filename.temp_file "baguette_comment" "" in
    let oc = open_out path in
    let w = Writer.create ~comments:flag ~audit:false oc in
    Writer.comment w "probe";
    close_out oc;
    let s = read_file path in
    Sys.remove path;
    s
  in
  check "Writer.comment: comments:false emits nothing" (with_flag false = "");
  check "Writer.comment: comments:true emits the comment line"
    (String.length (with_flag true) > 0);
  (* (2) end-to-end no-op on a real model *)
  let m = List.nth models 1 in
  let run_once comments =
    let dir = Filename.temp_file "baguette_e2e_flag" "" in
    Sys.remove dir;
    Sys.mkdir dir 0o700;
    let pbp = Filename.concat dir "model.pbp" in
    let store = build_store m in
    let encoding, ids = build_encoding m in
    let engine = build_engine m store ids in
    let oc = open_out pbp in
    let writer = Writer.create ~comments ~audit:true oc in
    Encoding.start_proof encoding writer;
    let ctx = mk_ctx writer encoding in
    ignore (Search.solve ~engine ~store ~ctx ~check:(independent_check m) ());
    close_out oc;
    let s = read_file pbp in
    (try Sys.remove pbp with _ -> ());
    (try Sys.rmdir dir with _ -> ());
    s
  in
  let without = run_once false in
  let with_ = run_once true in
  check "end-to-end: --proof-comments is still a no-op on a real model (M1-T48)"
    (without = with_)

(* --------------------------------------------------------------- M5-T1/M5-T2

   Branch and bound, end to end and through the REAL front end: FlatZinc text ->
   Builder -> Compile -> Search.optimise -> proof -> veripb, with the I-X2 audit on.

   The models above go through this file's hand-built stores on purpose (the header says
   why); this lane does not, because the thing being tested is the whole pipeline
   including the .opb's `min:` line, which only [Compile] writes.

   WHAT IT ASSERTS BEYOND "veripb said yes", and why each one needs asserting:

   - THE AUDIT. [Writer.conclusion] runs the I-X2 audit and raises if the live set is
     non-empty, so reaching the end at all is the check -- but the live set is asserted
     empty here as well, because "no exception escaped" and "nothing leaked" are only
     the same claim while the audit is on, and [Writer.create ~audit:true] is this
     lane's doing rather than the library's default.

   - EVERY DELETED ID IS DELETED ONCE. The audit CANNOT see a double delete (I-X2 says
     so: a second forget is a no-op and the live set is empty either way). The proof
     TEXT can, which is the route test_learned.ml takes for the same reason, and a
     branch-and-bound run is where it matters most -- several solutions, several level-0
     introductions and a sweep at the end.

   - THE `soli` IDS ARE NOT DELETED. That is the whole of [Writer.improving]'s argument:
     deleting one is an unchecked deletion that weakens the guarantee over the
     conclusion that follows it. test_proof.ml performs the break; this asserts the
     solver does not take it.

   - THE LOWER-BOUND ID IS CITED AND NOT DELETED. docs/PROOF-FORMAT.md section 5 says it
     "counts as discharged by the conclusion"; the task's obligation (c) is to assert
     that rather than assume it, so the id in the conclusion line is read back and
     checked against every `del` in the file. *)

let fz_optimisation_model =
  (* The same scene as test/models/opt_min_sat.fzn: two improving solutions, an optimum
     strictly inside the declared domain, and a subtree that has to be refuted rather
     than read off a bound. Repeated here rather than read from disk so that this lane
     does not depend on the cwd -- test_proof.ml's `obju` gate shows what that costs. *)
  "var 0..5: x :: output_var;\n\
   var 0..5: y :: output_var;\n\
   constraint int_lin_le([-1,-1],[x,y],-4);\n\
   constraint int_lin_le([1,-2],[x,y],0);\n\
   solve minimize y;\n"

let count_substring hay needle =
  let hl = String.length hay and nl = String.length needle in
  let rec go i n =
    if i + nl > hl then n
    else go (i + 1) (if String.sub hay i nl = needle then n + 1 else n)
  in
  if nl = 0 then 0 else go 0 0

(* Every constraint id named by a `del` line, with repeats kept -- a `del range LO HI`
   is expanded over its half-open interval (measured, M1-T22: HI survives). Repeats are
   the point: this is the only instrument that can see a double delete. *)
let deleted_ids proof =
  let ids = ref [] in
  List.iter
    (fun line ->
      let line = String.trim line in
      let words = String.split_on_char ' ' line |> List.filter (fun w -> w <> "") in
      let label w =
        let w =
          if String.length w > 0 && w.[String.length w - 1] = ';' then
            String.sub w 0 (String.length w - 1)
          else w
        in
        if String.length w > 2 && String.sub w 0 2 = "@c" then
          int_of_string_opt (String.sub w 2 (String.length w - 2))
        else int_of_string_opt w
      in
      match words with
      | "del" :: "id" :: rest ->
          List.iter
            (fun w -> match label w with Some i -> ids := i :: !ids | None -> ())
            rest
      | "del" :: "range" :: a :: b :: _ -> (
          match (label a, label b) with
          | Some lo, Some hi ->
              for i = lo to hi - 1 do
                ids := i :: !ids
              done
          | _ -> ())
      | _ -> ())
    (String.split_on_char '\n' proof);
  !ids

let test_m5_branch_and_bound () =
  let m = Baguette_flatzinc.Builder.of_string ~file:"m5" fz_optimisation_model in
  let compiled = Baguette_flatzinc.Compile.compile m in
  let dir = Filename.temp_file "baguette_m5_e2e" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "m5.opb" and pbp = Filename.concat dir "m5.pbp" in
  let store = compiled.Baguette_flatzinc.Compile.store in
  let encoding = compiled.Baguette_flatzinc.Compile.encoding in
  let oc = open_out opb in
  Encoding.write_opb encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let objective =
    match compiled.Baguette_flatzinc.Compile.objective with
    | Some o -> o
    | None -> failwith "test_m5: Compile did not resolve `solve minimize y;`"
  in
  let printed = ref 0 in
  let stats = Search.stats_create () in
  let check_asn assignment =
    let values = Array.make (Baguette_flatzinc.Model.nvars m) 0 in
    List.iter (fun (v, x) -> values.(Var.to_int v) <- x) assignment;
    Baguette_flatzinc.Model.check_assignment m values
  in
  let outcome =
    Search.optimise ~engine:compiled.Baguette_flatzinc.Compile.engine ~store ~ctx
      ~check:check_asn ~objective ~stats
      ~on_solution:(fun _ -> incr printed)
      ()
  in
  let live_at_end = Writer.live_ids writer in
  let objective_ids = Writer.objective_ids writer in
  close_out oc;
  let proof = read_file pbp in
  (match outcome with
  | Search.Opt (_, value) ->
      check "M5 e2e: the optimum of `minimize y` is 2, and it is PROVED not merely found"
        (value = 2)
  | Search.Opt_unsat ->
      incr failures;
      print_endline "FAIL M5 e2e: a satisfiable optimisation model reported no solution");
  check "M5 e2e: both improving solutions were reported to the caller (SPEC 2.2)"
    (!printed = 2);
  (* I-X2, first half: nothing leaked. *)
  check "M5 e2e: the writer's live set is empty at the conclusion (I-X2)"
    (live_at_end = []);
  (* I-X2, second half, and the half the audit structurally cannot see. *)
  let deleted = deleted_ids proof in
  let sorted = List.sort compare deleted in
  let rec has_dup = function a :: (b :: _ as r) -> a = b || has_dup r | _ -> false in
  check "M5 e2e: no constraint id is deleted twice across the whole run (I-X2)"
    (not (has_dup sorted));
  check "M5 e2e: there was something to check -- the run did delete ids" (deleted <> []);
  (* The `soli` ids: one per improving solution, none of them deleted. *)
  check
    "M5 e2e: one objective id per improving solution, recorded apart from the live set"
    (List.length objective_ids = 2);
  check "M5 e2e: `soli` appears once per improving solution in the proof"
    (count_substring proof "soli " = 2);
  check
    "M5 e2e: NO `soli` constraint is deleted -- deleting one is an unchecked deletion \
     that weakens the guarantee over the conclusion after it"
    (List.for_all (fun id -> not (List.mem id deleted)) objective_ids);
  (* The lower-bound id: cited by the conclusion, and discharged BY it rather than by a
     `del` (docs/PROOF-FORMAT.md section 5). *)
  let conclusion_line =
    List.find_opt
      (fun l -> String.length l > 10 && String.sub (String.trim l) 0 10 = "conclusion")
      (String.split_on_char '\n' proof)
  in
  (match conclusion_line with
  | None ->
      incr failures;
      print_endline "FAIL M5 e2e: the proof has no conclusion line"
  | Some line ->
      check "M5 e2e: the conclusion is `conclusion BOUNDS 2 : <id> 2`, both bounds equal"
        (count_substring line "conclusion BOUNDS 2 : " = 1
        && count_substring line " 2 ;" = 1);
      (* The cited id, read back out of the line rather than assumed. *)
      let cited =
        String.split_on_char ' ' (String.trim line)
        |> List.filter_map (fun w ->
               if String.length w > 2 && String.sub w 0 2 = "@c" then
                 int_of_string_opt (String.sub w 2 (String.length w - 2))
               else None)
      in
      check "M5 e2e: the conclusion cites exactly one constraint (the lower bound)"
        (List.length cited = 1);
      check
        "M5 e2e: the cited lower-bound id is NOT deleted -- it is discharged by the \
         conclusion (PROOF-FORMAT section 5), asserted rather than assumed"
        (List.for_all (fun id -> not (List.mem id deleted)) cited));
  (* I-X4: THE PROOF IS APPEND-ONLY AND NEVER REWOUND. Branch and bound re-solves under a
     tightened bound, and the hazard the invariant names is that the re-solve becomes
     truncation -- a second pass overwriting the first pass's lines, or reusing its ids.
     Neither can happen here, because the bound is installed on the node the search is
     standing on and the search simply carries on; but "cannot happen" is what the two
     halves of this suite exist to stop anyone from having to take on trust. The
     observable form is that ids are minted strictly increasing and each is defined
     exactly once: a rewind would show up as a repeat or a decrease. *)
  let minted =
    List.filter_map
      (fun l ->
        match String.split_on_char ' ' (String.trim l) with
        | lbl :: _ when String.length lbl > 2 && String.sub lbl 0 2 = "@c" ->
            int_of_string_opt (String.sub lbl 2 (String.length lbl - 2))
        | _ -> None)
      (String.split_on_char '\n' proof)
  in
  let rec increasing = function
    | a :: (b :: _ as r) -> a < b && increasing r
    | _ -> true
  in
  check
    "M5 e2e: constraint ids are minted strictly increasing across the whole run -- the \
     proof is append-only and no re-solve rewound it (I-X4)"
    (minted <> [] && increasing minted);
  (* SPEC 3.4 fixes the search as depth-first with RESTARTS DISABLED, and a re-solve
     under a tightened bound is the obvious place to have smuggled one in. M1-T36's
     identity is what says none was: on an exhausted tree nodes = 2 * decisions + 1 -
     skipped exactly, which can only hold if every node was dispatched once. A restart
     would re-walk a prefix of the tree and break it. *)
  check
    "M5 e2e: nodes = 2 * decisions + 1 - skipped on the exhausted tree -- the re-entry \
     at a solution node is not a restart (SPEC 3.4)"
    (Search.stats_consistent stats ~exhausted:true);
  (* And the product: the checker's verdict, under checked deletion, so that none of the
     above rests on an acceptance bought with a weakened guarantee. *)
  (match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M5 e2e: veripb not found -- invariant I-X1 was NOT checked for the \
         branch-and-bound proof. A missing checker is a failure, never a skip."
  | Some veripb ->
      let log = Filename.concat dir "log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s -c %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      let out = read_file log in
      let says needle =
        let hl = String.length out and nl = String.length needle in
        let rec go i = i + nl <= hl && (String.sub out i nl = needle || go (i + 1)) in
        go 0
      in
      check "M5 e2e: veripb VERIFIES the branch-and-bound proof under checked deletion"
        (rc = 0);
      check "M5 e2e: ... and reports the bounds it verified, both equal to the optimum"
        (says "VERIFIED BOUNDS 2 <= obj <= 2");
      if rc <> 0 then Printf.printf "%s\n" out);
  List.iter
    (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
    (Array.to_list (Sys.readdir dir));
  try Sys.rmdir dir with _ -> ()

(* ------------------------------------------------- M5: IS THE DERIVATION LOAD-BEARING?

   The question this project has had to ask three times, and has twice answered wrongly by
   not asking. A refutation that rests on a clause makes every `pol` in the file
   decorative, because veripb accepts a `pol` whatever it derives -- D-0057 and D-0060
   both found deliberate breaks reddening nothing for exactly that reason. So "veripb said
   VERIFIED BOUNDS" is not evidence that M5 proves optimality until the objective
   derivation has been shown to be load-bearing, by breaking it and watching the checker
   refuse.

   M5's chain is in better shape than a `pol` chain, and the reason is structural rather
   than lucky: the two rules it is made of are both CHECKED.

     - the improving constraint is minted by `soli`, which the CHECKER builds for itself
       from the objective it read out of the .opb. We never write it, so we cannot write
       it wrongly.
     - the bound it licenses is a `rup`, and a `rup` is verified by unit propagation. A
       wrong one is refused where a wrong `pol` is waved through.

   That is the argument. Below is the measurement, on the REAL emitted proof of
   test/models/opt_min_sat.fzn, which is the ordinary branch-and-bound path.

   And one more thing is established here, because the argument above does not reach it:
   `conclusion BOUNDS` CHECKS THE ID IT CITES whatever minted that id. Across the five
   optimisation models the cited id is minted three different ways -- `rup` (the root
   empty clause, opt_min_sat), `soli` (the floor case, opt_floor_sat/opt_max_sat/
   opt_ne_sat) and `pol` (the infeasible case, opt_unsat) -- and the `pol` one is the
   shape the warning above is about. It is broken below too. *)

let m5_emit dir name src =
  let m = Baguette_flatzinc.Builder.of_string ~file:name src in
  let compiled = Baguette_flatzinc.Compile.compile m in
  let opb = Filename.concat dir (name ^ ".opb")
  and pbp = Filename.concat dir (name ^ ".pbp") in
  let store = compiled.Baguette_flatzinc.Compile.store in
  let encoding = compiled.Baguette_flatzinc.Compile.encoding in
  let oc = open_out opb in
  Encoding.write_opb encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let objective =
    match compiled.Baguette_flatzinc.Compile.objective with
    | Some o -> o
    | None -> failwith ("m5_emit: " ^ name ^ " has no objective")
  in
  let check_asn assignment =
    let values = Array.make (Baguette_flatzinc.Model.nvars m) 0 in
    List.iter (fun (v, x) -> values.(Var.to_int v) <- x) assignment;
    Baguette_flatzinc.Model.check_assignment m values
  in
  let outcome =
    Search.optimise ~engine:compiled.Baguette_flatzinc.Compile.engine ~store ~ctx
      ~check:check_asn ~objective
      ~on_solution:(fun _ -> ())
      ()
  in
  close_out oc;
  (opb, pbp, read_file pbp, outcome)

(* Run the checker over a proof written out from [lines], and return (accepted, log). *)
let m5_run_lines checker dir tag opb lines =
  let pbp = Filename.concat dir (tag ^ ".pbp") in
  let oc = open_out pbp in
  List.iter (fun l -> output_string oc (l ^ "\n")) lines;
  close_out oc;
  let log = Filename.concat dir (tag ^ ".log") in
  let rc =
    Sys.command
      (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote checker) (Filename.quote opb)
         (Filename.quote pbp) (Filename.quote log))
  in
  (rc = 0, read_file log)

let m5_says out needle =
  let hl = String.length out and nl = String.length needle in
  let rec go i = i + nl <= hl && (String.sub out i nl = needle || go (i + 1)) in
  go 0

(* The label a line defines, if it defines one: "@c13 rup ..." -> Some (13, "rup"). *)
let m5_minted line =
  match String.split_on_char ' ' (String.trim line) with
  | lbl :: rule :: _ when String.length lbl > 2 && String.sub lbl 0 2 = "@c" -> (
      match int_of_string_opt (String.sub lbl 2 (String.length lbl - 2)) with
      | Some i -> Some (i, rule)
      | None -> None)
  | _ -> None

let test_m5_derivation_is_load_bearing () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M5 load-bearing: veripb not found, so NOTHING about the objective \
         derivation was established. A missing checker is a failure, never a skip."
  | Some checker -> (
      let dir = Filename.temp_file "baguette_m5_lb" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      (* ---------------------------------------------- the ordinary path, opt_min_sat *)
      let opb, _pbp, proof, _ = m5_emit dir "bb" fz_optimisation_model in
      let lines = String.split_on_char '\n' proof in
      let f_line =
        List.find_opt
          (fun l -> String.length l > 1 && String.sub (String.trim l) 0 2 = "f ")
          lines
      in
      let conclusion =
        List.find_opt
          (fun l ->
            String.length (String.trim l) > 10
            && String.sub (String.trim l) 0 10 = "conclusion")
          lines
      in
      (* Which id does the conclusion cite, and WHAT MINTED IT -- read back out of the
         file, never assumed. *)
      let cited =
        match conclusion with
        | None -> None
        | Some l -> (
            String.split_on_char ' ' (String.trim l)
            |> List.filter_map (fun w ->
                   if String.length w > 2 && String.sub w 0 2 = "@c" then
                     int_of_string_opt (String.sub w 2 (String.length w - 2))
                   else None)
            |> function
            | id :: _ -> Some id
            | [] -> None)
      in
      let minted_by id =
        List.find_map
          (fun l ->
            match m5_minted l with Some (i, r) when i = id -> Some r | _ -> None)
          lines
      in
      (match cited with
      | None ->
          incr failures;
          print_endline "FAIL M5 load-bearing: the conclusion cites no constraint"
      | Some id ->
          check
            "M5 load-bearing: the conclusion's cited id was minted by a `rup` -- a \
             CHECKED rule, not a `pol` the checker would wave through"
            (minted_by id = Some "rup"));
      (* BREAK 1. Delete each improving constraint as soon as it is introduced, so the
         objective derivation is gone while every other line stays exactly where it was
         and no id shifts. The first line that uses the bound must be refused. *)
      let neutralised =
        List.concat_map
          (fun l ->
            match m5_minted l with
            | Some (i, "soli") -> [ l; Printf.sprintf "del id @c%d ;" i ]
            | _ -> [ l ])
          lines
      in
      let ok, out = m5_run_lines checker dir "neutralised" opb neutralised in
      check
        "M5 BREAK: with the improving constraints deleted, the proof is REFUSED -- the \
         objective derivation is load-bearing, not decorative"
        (not ok);
      check "M5 BREAK: ... and it is refused on the JUDGEMENT, not on the grammar"
        (m5_says out
           "The constraint is not implied by reverse unit propagation (RUP) from core \
            and derived database.");
      (* BREAK 2, and the one that reaches the CONCLUSION rather than the first bound.
         The model is SATISFIABLE, so the empty clause the conclusion cites cannot come
         from the model rows: it exists only because the objective bound is in the
         database. Asserted by deriving it against the .opb alone. *)
      (match f_line with
      | None ->
          incr failures;
          print_endline "FAIL M5 load-bearing: the proof has no `f` line to reuse"
      | Some f ->
          let ok, out =
            m5_run_lines checker dir "no_objective" opb
              [
                "pseudo-Boolean proof version 3.0";
                String.trim f;
                "rup >= 1 ;";
                "output NONE ;";
                "conclusion UNSAT ;";
                "end pseudo-Boolean proof ;";
              ]
          in
          check
            "M5 load-bearing: the contradiction the conclusion cites is NOT derivable \
             from the model alone -- the model is satisfiable, so the refutation is the \
             objective bound's and nothing else's"
            (not ok);
          check "M5 load-bearing: ... refused on the judgement"
            (m5_says out
               "The constraint is not implied by reverse unit propagation (RUP) from \
                core and derived database."));
      (* ------------------------------------- the cited contradiction, opt_unsat's shape

         An infeasible optimisation model concludes BOUNDS INF INF citing the line that
         refutes the root. Until M8-bits-encoding-T5 (D-0131) that was [int_lin_le]'s
         D-0013 `pol`; it is now the empty clause `rup >= 1`, derived after the root's
         trace. Either way the citation is NOT decorative: the conclusion checks that the
         cited constraint really is a contradiction, and the break below makes it one
         that is not. *)
      let opb2, _, proof2, outcome2 =
        m5_emit dir "inf"
          "var 0..3: x :: output_var;\n\
           constraint int_lin_le([1],[x],1);\n\
           constraint int_lin_le([-1],[x],-3);\n\
           solve minimize x;\n"
      in
      check "M5: an infeasible optimisation model reports no solution"
        (outcome2 = Search.Opt_unsat);
      let lines2 = String.split_on_char '\n' proof2 in
      check "M5: ... and concludes BOUNDS INF INF, the only conclusion available to it"
        (List.exists
           (fun l -> m5_says l "conclusion BOUNDS INF" && m5_says l "INF ;")
           lines2);
      let cited2 =
        List.find_map
          (fun l ->
            if
              String.length (String.trim l) > 10
              && String.sub (String.trim l) 0 10 = "conclusion"
            then
              String.split_on_char ' ' (String.trim l)
              |> List.filter_map (fun w ->
                     if String.length w > 2 && String.sub w 0 2 = "@c" then
                       int_of_string_opt (String.sub w 2 (String.length w - 2))
                     else None)
              |> function
              | id :: _ -> Some id
              | [] -> None
            else None)
          lines2
      in
      (match cited2 with
      | None ->
          incr failures;
          print_endline "FAIL M5: the INF conclusion cites no constraint"
      | Some id ->
          check
            "M5: the INF conclusion's cited id was minted by the empty clause `rup >= 1` \
             (D-0131's root close)"
            (List.find_map
               (fun l ->
                 match m5_minted l with
                 | Some (i, r) when i = id ->
                     Some (r, String.trim (Writer.strip_label (String.trim l)))
                 | _ -> None)
               lines2
            = Some ("rup", "rup >= 1 ;"));
          (* BREAK 3: make the cited line something sound but NOT a contradiction -- a
             tautology, label kept -- leaving the conclusion unchanged. If the conclusion
             did not check its citation this would sail through, which is the whole
             worry. *)
          let corrupted =
            List.map
              (fun l ->
                match m5_minted l with
                | Some (i, "rup") when i = id -> (
                    match String.split_on_char ' ' (String.trim l) with
                    | lbl :: _ -> lbl ^ " rup +1 x_ge_1 +1 ~x_ge_1 >= 1 ;"
                    | [] -> l)
                | _ -> l)
              lines2
          in
          check "M5 BREAK CONTROL: the corruption really changed the cited line"
            (corrupted <> lines2);
          let ok, out = m5_run_lines checker dir "polbad" opb2 corrupted in
          check
            "M5 BREAK: a cited line that is sound but not contradictory is REFUSED by \
             the conclusion -- BOUNDS checks the id it cites"
            (not ok);
          check "M5 BREAK: ... at full strength, naming the citation"
            (m5_says out "is not contradicting, as specified by the hint."));
      List.iter
        (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
        (Array.to_list (Sys.readdir dir));
      try Sys.rmdir dir with _ -> ())

(* ================================================== M4-T3: array_int_element ========

   Obligations (b) and (c) of the row, and they are one lane because (c) is what makes
   (b) mean anything: veripb accepts a [pol] whatever it derives, so a break that
   corrupts a [pol] and stops establishes NOTHING. Only a later line that NEEDS the pol --
   here `conclusion UNSAT : <its id>` -- turns the corruption into a rejection. That is
   D-0057 and D-0060, twice found, and test_prop.ml's alldiff lane says the same thing
   for the same reason.

   Both halves are asserted, because "it cites the derivation" is only informative next
   to a case where it does not. test/models/element_range_unsat.fzn is the positive case
   and test/models/element_moved_unsat.fzn the negative one; the sources are restated
   here rather than read from disk, the same way the alldiff lane does it. *)

let el_solve dir name src =
  let m = Baguette_flatzinc.Builder.of_string ~file:name src in
  let compiled = Baguette_flatzinc.Compile.compile m in
  let opb = Filename.concat dir (name ^ ".opb")
  and pbp = Filename.concat dir (name ^ ".pbp") in
  let oc = open_out opb in
  Encoding.write_opb compiled.Baguette_flatzinc.Compile.encoding oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof compiled.Baguette_flatzinc.Compile.encoding writer;
  let ctx = mk_ctx writer compiled.Baguette_flatzinc.Compile.encoding in
  let check_asn assignment =
    let values = Array.make (Baguette_flatzinc.Model.nvars m) 0 in
    List.iter (fun (v, x) -> values.(Var.to_int v) <- x) assignment;
    Baguette_flatzinc.Model.check_assignment m values
  in
  let outcome =
    Search.solve ~engine:compiled.Baguette_flatzinc.Compile.engine
      ~store:compiled.Baguette_flatzinc.Compile.store ~ctx ~check:check_asn ()
  in
  close_out oc;
  (opb, read_file pbp, outcome)

(* The id `conclusion UNSAT` cites, and the line that minted it -- READ BACK OUT of the
   file, never assumed. *)
let el_cited_line proof =
  let lines = String.split_on_char '\n' proof in
  let cited =
    List.fold_left
      (fun acc l ->
        if m5_says l "conclusion UNSAT" then
          match String.index_opt l ':' with
          | Some i ->
              Some
                (String.trim
                   (List.hd
                      (String.split_on_char ' '
                         (String.trim (String.sub l (i + 1) (String.length l - i - 1))))))
          | None -> acc
        else acc)
      None lines
  in
  match cited with
  | None -> (lines, None, None)
  | Some lbl ->
      ( lines,
        Some lbl,
        List.find_opt (fun l -> m5_says (String.trim l ^ " ") (lbl ^ " ")) lines )

(* The last `pol` line before the one labelled [cited]. Since D-0131 the conclusion
   cites the empty clause `rup >= 1`, and the derivation it rests on -- element's own,
   written ahead of the close because the family is [Needs_derivation] (I-X10) -- is
   the `pol` just before it. *)
let el_last_pol_before lines cited =
  match cited with
  | None -> None
  | Some lbl ->
      let starts p t =
        String.length t >= String.length p && String.sub t 0 (String.length p) = p
      in
      let rec go acc = function
        | [] -> acc
        | l :: rest ->
            let t = String.trim l in
            if starts (lbl ^ " ") t then acc
            else go (if m5_says (" " ^ t) " pol " then Some l else acc) rest
      in
      go None lines

let rup_wording =
  "The constraint is not implied by reverse unit propagation (RUP) from core and derived \
   database."

(* [line] replaced by a tautology that keeps its label, so every later citation still
   parses and the checker judges what rested on it (test_matrix.ml's [blank_rules]
   recipe). [victim] selects the lines. *)
let el_blank ~victim ~taut lines =
  List.map
    (fun l ->
      if victim l then
        match String.split_on_char ' ' (String.trim l) with
        | lbl :: _ -> Printf.sprintf "%s rup +1 %s +1 ~%s >= 1 ;" lbl taut taut
        | [] -> l
      else l)
    lines

let el_is_rup_not_close l =
  let t = String.trim l in
  m5_says (" " ^ t) " rup " && not (m5_says (t ^ " ") " rup >= 1 ; ")

let el_range_src =
  "var 1..3: i;\n\
   var 0..4: c;\n\
   constraint array_int_element(i, [7, 8, 9], c);\n\
   solve satisfy;\n"

let el_moved_src =
  "var 1..2: i;\n\
   var 1..2: j;\n\
   var 0..9: c;\n\
   constraint array_int_element(i, [1, 2], c);\n\
   constraint array_int_element(j, [3, 4], c);\n\
   solve satisfy;\n"

let test_element_derivation_is_load_bearing () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M4-T3 load-bearing: veripb not found, so NOTHING about the element \
         derivation was established. A missing checker is a failure, never a skip."
  | Some checker -> (
      let dir = Filename.temp_file "baguette_el_lb" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      (* ------------------------------------------------ (c) the positive half *)
      let opb, proof, outcome = el_solve dir "elrange" el_range_src in
      check "M4-T3 (c): the declared-range scene is UNSAT" (outcome = Search.Unsat);
      let lines, cited, minting = el_cited_line proof in
      check "M4-T3 (c): the conclusion names an id" (cited <> None);
      (* D-0131: the conclusion cites the empty clause, and element's derivation -- the
         counting argument the empty clause rests on -- is the `pol` written ahead of it
         (the family is [Needs_derivation], so the close is one propagation past it). *)
      (match minting with
      | None -> check "M4-T3 (c): the conclusion names a line THIS proof minted" false
      | Some line ->
          check "M4-T3 (c): the conclusion names a line THIS proof minted" true;
          check
            "M4-T3 (c): `conclusion UNSAT` cites the empty clause `rup >= 1`, D-0131's \
             root close"
            (String.trim (Writer.strip_label (String.trim line)) = "rup >= 1 ;"));
      let derivation = el_last_pol_before lines cited in
      check
        "M4-T3 (c): and the ELEMENT DERIVATION -- a pol -- is on the page ahead of the \
         close, which is what the close rests on"
        (derivation <> None);
      (* ----------------------- (b) what a break can and cannot show on this scene

         Measured on 3.0.2 (M8-bits-encoding-T5, D-0131): with element's pol AND every
         trace line replaced by tautologies, `rup >= 1` is still ACCEPTED here. The
         declared-range scene is refuted by its .opb alone under unit propagation
         (`c <= 4` makes every `~idx_eq_p \/ c >= as[p]` row a unit, and the at-least-one
         closes), which is D-0030's shape: no corruption of the derivation or of the trace
         can be judged on it. The old BREAK -- the pol's last operand dropped, refused at
         `conclusion UNSAT`'s SYNTACTIC check of its citation -- tested that check, not
         the derivation. The fact is pinned so that the day it stops holding (a weaker
         encoding of the guards, say) the lane says so, and the load-bearing break lives
         on the moved-bound scene below, where the checker refuses it. *)
      (match derivation with
      | None -> ()
      | Some line ->
          let ok, _ = m5_run_lines checker dir "elok" opb lines in
          check "M4-T3 BREAK CONTROL: the unmodified proof is accepted" ok;
          let blanked =
            el_blank ~taut:"c_ge_1"
              ~victim:(fun l -> l = line || el_is_rup_not_close l)
              lines
          in
          check "M4-T3 (b) premise: the blanking really changed the file"
            (blanked <> lines);
          let ok, _ = m5_run_lines checker dir "elvac" opb blanked in
          check
            "M4-T3 (b), MEASURED (D-0131): the declared-range scene is refuted by its \
             .opb alone under unit propagation -- with element's pol and the whole trace \
             blanked the empty clause is still ACCEPTED, so no break is judged here and \
             the load-bearing lane is the moved-bound scene's"
            ok);
      (* ---------------------------------- (c) the negative half, INVERTED by M4-T8

         M4-T3 wrote this half asserting `rup >= 1`, deliberately, so that it would go
         red exactly when the swap to [Explanation.Defining] (D-0064) landed -- see
         docs/ROADMAP.md's M4-T8 row and lib/core/prop/element.ml's
         [established_at_root]. The bound `element_moved_src` moves is one element1's
         OWN root-level fixpoint sets (unconditionally, no decision anywhere in this
         scene), so it is establish_at_root-true and now gets the same exact
         [Defining] cancellation as the declared-range half above: the residue
         cancels, `Search.rests_on_a_clause` no longer trips, and `conclusion UNSAT`
         cites element.ml's own [pol] (Route A) rather than the empty clause (Route
         B). This is the CONTROL half of that assertion, not a fresh one -- it is the
         same model, still exercised, with the expectation flipped and a break added,
         exactly like (b) above did for the positive half. *)
      let opb, proof, outcome = el_solve dir "elmoved" el_moved_src in
      check "M4-T3/M4-T8 (c): the moved-bound scene is UNSAT" (outcome = Search.Unsat);
      let lines, cited, minting = el_cited_line proof in
      check "M4-T8 (c): the moved-bound conclusion names an id" (cited <> None);
      (match minting with
      | None ->
          check "M4-T8 (c): the moved-bound conclusion names a line THIS proof minted"
            false
      | Some line ->
          check "M4-T8 (c): the moved-bound conclusion names a line THIS proof minted"
            true;
          check
            "M4-T8 (c): with the bound MOVED, `conclusion UNSAT` cites the empty clause \
             (D-0131's root close, which is also what the pre-M4-T8 Route B wrote -- the \
             difference is now in what the close RESTS on, below)"
            (String.trim (Writer.strip_label (String.trim line)) = "rup >= 1 ;"));
      let derivation = el_last_pol_before lines cited in
      check
        "M4-T8 (c): ... and element.ml's OWN pol is on the page ahead of it -- D-0064's \
         Defining cancels the moved bound exactly, where the old Clause stand-in could \
         not, so the derivation is what the empty clause rests on and it is not \
         decorative for this scene"
        (derivation <> None);
      (* ------------------------- M4-T8 obligation (b): what the empty clause rests on

         Measured on 3.0.2 (M8-bits-encoding-T5, D-0131), and the answer is not a single
         line. The moved bound `c <= 2` is on the page TWICE: as its trace line, and
         inside element's derivation, where D-0064's [Defining] cites that very line so
         the cancellation is exact. Blank the trace alone and the close is still
         ACCEPTED (the derivation, with its citation turned into a tautology, still
         derives a row the element rows then refute by unit propagation); blank the
         derivation alone and it is still ACCEPTED (the trace puts the bound where the
         rows refute it); blank BOTH and the empty clause is REFUSED, at the RUP wording.
         The old BREAK (the pol's last operand dropped, refused at the conclusion's
         syntactic check of its citation) measured the citation check; this measures the
         proof, and what the proof says is that the refutation needs what the solver
         wrote and not only the rows -- which is the D-0030 property, now asserted on
         the moved-bound scene where it holds. *)
      (match derivation with
      | None -> ()
      | Some line ->
          let ok, _ = m5_run_lines checker dir "elmovedok" opb lines in
          check "M4-T8 BREAK CONTROL: the unmodified moved-bound proof is accepted" ok;
          let trace_blanked = el_blank ~taut:"c_ge_1" ~victim:el_is_rup_not_close lines in
          check "M4-T8 BREAK premise: there is a trace to blank" (trace_blanked <> lines);
          let ok, _ = m5_run_lines checker dir "elmovedtrace" opb trace_blanked in
          check
            "M4-T8 (b), MEASURED (D-0131): with the root's trace alone blanked the empty \
             clause is still ACCEPTED -- element's exact derivation carries the bound \
             too"
            ok;
          let pol_blanked = el_blank ~taut:"c_ge_1" ~victim:(fun l -> l = line) lines in
          let ok, _ = m5_run_lines checker dir "elmovedpol" opb pol_blanked in
          check
            "M4-T8 (b), MEASURED (D-0131): with element's derivation alone blanked the \
             empty clause is still ACCEPTED -- the trace carries the bound too"
            ok;
          let both_blanked =
            el_blank ~taut:"c_ge_1"
              ~victim:(fun l -> l = line || el_is_rup_not_close l)
              lines
          in
          let ok, out = m5_run_lines checker dir "elmovedboth" opb both_blanked in
          if ok then
            Printf.printf "     accepted with both blanked; the proof was:\n%s\n"
              (String.concat "\n" both_blanked);
          check
            "M4-T8 BREAK (b): with the trace AND element's derivation blanked the empty \
             clause is REFUSED -- the refutation rests on what the solver wrote, not on \
             the rows"
            (not ok);
          check
            "M4-T8 BREAK (b): ... at full strength -- the checker's RUP wording, not an \
             exit status and not a parse error"
            (m5_says out rup_wording));
      List.iter
        (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
        (Array.to_list (Sys.readdir dir));
      try Sys.rmdir dir with _ -> ())

let check_bool_m6 name cond = check name cond

(* veripb 3.0.2's refusal of a `conclusion UNSAT` the database does not support. Measured
   2026-10-01 on the M6-T9 stopped pigeonhole proof, not recalled. *)
let m6_unsat_wording = "There is no contradicting constraint in the database."

(* ------------------------------------------------------------ M6-T9 time limit *)

(* M6-T9: a search STOPPED by [config.stop] -- the hook `--time-limit` drives -- ends its
   proof with `conclusion NONE`, and that proof is CHECKED. The stop here is a node
   counter, not a clock, so the lane is deterministic: the stop fires at the same node on
   every machine. What is asserted, and why each needs asserting:

   1. The run raises [Search.Stopped] and NOT an answer -- and the CONTROL (same model,
      no stop) does answer, so the stop really interrupted a search that had more to do.
   2. Learned constraints are on the page (the evidence a stopped run exists to keep),
      and the I-X2 audit (on) passed: every id the stopped solve received was deleted.
   3. veripb -c accepts it and says VERIFIED NO CONCLUSION.
   4. THE BREAK: the same proof with `conclusion NONE` replaced by `conclusion UNSAT` is
      REFUSED, in the checker's wording. Without this, (3) could be a checker that
      accepts anything over this file; with it, the stopped proof is known to claim no
      more than it derived -- the contradiction the full search reaches is not on it. *)
let m6_pigeons =
  (* 4 pigeons, 3 holes, 0/1 cells (D-0028: hardness from structure, never width). *)
  let b = Buffer.create 512 in
  for p = 1 to 4 do
    for h = 1 to 3 do
      Buffer.add_string b (Printf.sprintf "var 0..1: x%d%d :: output_var;\n" p h)
    done
  done;
  for p = 1 to 4 do
    Buffer.add_string b
      (Printf.sprintf "constraint int_lin_eq([1,1,1],[x%d1,x%d2,x%d3],1);\n" p p p)
  done;
  for h = 1 to 3 do
    Buffer.add_string b
      (Printf.sprintf "constraint int_lin_le([1,1,1,1],[x1%d,x2%d,x3%d,x4%d],1);\n" h h h
         h)
  done;
  Buffer.add_string b "solve satisfy;\n";
  Buffer.contents b

let m6_setup dir name src =
  let m = Baguette_flatzinc.Builder.of_string ~file:name src in
  let compiled = Baguette_flatzinc.Compile.compile m in
  let opb = Filename.concat dir (name ^ ".opb")
  and pbp = Filename.concat dir (name ^ ".pbp") in
  let encoding = compiled.Baguette_flatzinc.Compile.encoding in
  let oc = open_out opb in
  Encoding.write_opb encoding oc;
  close_out oc;
  let poc = open_out pbp in
  let writer = Writer.create ~audit:true poc in
  Encoding.start_proof encoding writer;
  let ctx = mk_ctx writer encoding in
  let check_asn assignment =
    let values = Array.make (Baguette_flatzinc.Model.nvars m) 0 in
    List.iter (fun (v, x) -> values.(Var.to_int v) <- x) assignment;
    Baguette_flatzinc.Model.check_assignment m values
  in
  (compiled, opb, pbp, poc, writer, ctx, check_asn)

let m6_veripb veripb dir opb pbp =
  let log = Filename.concat dir "m6.log" in
  let rc =
    Sys.command
      (Printf.sprintf "%s -c %s %s > %s 2>&1" (Filename.quote veripb) (Filename.quote opb)
         (Filename.quote pbp) (Filename.quote log))
  in
  (rc, read_file log)

let m6_says out needle =
  let hl = String.length out and nl = String.length needle in
  let rec go i = i + nl <= hl && (String.sub out i nl = needle || go (i + 1)) in
  go 0

let m6_after n =
  let k = ref 0 in
  fun () ->
    incr k;
    !k > n

let test_m6_time_limit () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M6-T9: veripb not found -- the stopped proofs were NOT checked. A missing \
         checker is a failure, never a skip."
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_m6" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      (* (1) control: unstopped, the pigeons are refuted. *)
      (let compiled, _, _, poc, _, ctx, check = m6_setup dir "ctl" m6_pigeons in
       let stats = Search.stats_create () in
       let r =
         Search.solve ~engine:compiled.Baguette_flatzinc.Compile.engine
           ~store:compiled.Baguette_flatzinc.Compile.store ~ctx ~check ~stats ()
       in
       close_out poc;
       check_bool_m6 "M6-T9 CONTROL: unstopped, 4 pigeons in 3 holes is UNSAT"
         (r = Search.Unsat);
       check_bool_m6
         (Printf.sprintf
            "M6-T9 CONTROL: ... and the full search takes more than the 6 nodes the \
             stopped run is allowed (%d)"
            stats.Search.nodes)
         (stats.Search.nodes > 6));
      (* (1)-(4) the stopped satisfaction run. *)
      (let compiled, opb, pbp, poc, writer, ctx, check = m6_setup dir "stop" m6_pigeons in
       let stats = Search.stats_create () in
       (* [m6_after] COUNTS its calls, so this lane asks for M6-T9's contract, the stop
          asked at node entry only, which is [stop_poll_runs = 0] (D-0136). It ran on the
          default config until M6-T23 (D-0149) added polls inside a conflict's trace and
          PB analysis: those ask a counting predicate more often, and on the default
          config this lane then stops inside the first conflict's trace instead of at the
          7th node. *)
       let config =
         { Search.default_config with Search.stop = m6_after 6; stop_poll_runs = 0 }
       in
       let r =
         match
           Search.solve ~engine:compiled.Baguette_flatzinc.Compile.engine
             ~store:compiled.Baguette_flatzinc.Compile.store ~ctx ~check ~stats ~config ()
         with
         | _ -> `Answered
         | exception Search.Stopped { best = None } -> `Stopped
         | exception Search.Stopped { best = Some _ } -> `Stopped_with_incumbent
       in
       let live = Writer.live_ids writer in
       close_out poc;
       check_bool_m6 "M6-T9: the stopped satisfaction run raises Stopped, no incumbent"
         (r = `Stopped);
       check_bool_m6
         "M6-T9: ... AT the 7th node: [stop] is asked on entry, after the node is counted"
         (stats.Search.nodes = 7);
       check_bool_m6
         (Printf.sprintf "M6-T9: ... having learned something to keep (%d learned)"
            stats.Search.n_learned)
         (stats.Search.n_learned > 0);
       check_bool_m6 "M6-T9: ... every id it received is deleted (I-X2, audit on)"
         (live = []);
       let proof = read_file pbp in
       check_bool_m6 "M6-T9: ... and the proof ENDS output NONE / conclusion NONE / end"
         (m6_says proof "output NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n");
       let rc, out = m6_veripb veripb dir opb pbp in
       check_bool_m6 "M6-T9: veripb -c accepts the stopped proof" (rc = 0);
       check_bool_m6 "M6-T9: ... and says VERIFIED NO CONCLUSION"
         (m6_says out "VERIFIED NO CONCLUSION");
       if rc <> 0 then print_endline out;
       (* (4) the break. *)
       let broken =
         let needle = "conclusion NONE ;" in
         let i =
           let rec find i =
             if i + String.length needle > String.length proof then 0
             else if String.sub proof i (String.length needle) = needle then i
             else find (i + 1)
           in
           find 0
         in
         String.sub proof 0 i ^ "conclusion UNSAT ;"
         ^ String.sub proof
             (i + String.length needle)
             (String.length proof - i - String.length needle)
       in
       let pbp2 = Filename.concat dir "broken.pbp" in
       let oc = open_out pbp2 in
       output_string oc broken;
       close_out oc;
       let rc2, out2 = m6_veripb veripb dir opb pbp2 in
       check_bool_m6
         "M6-T9 BREAK: the stopped proof with `conclusion UNSAT` in place of NONE is \
          REFUSED -- the stopped run's database is not already contradictory"
         (rc2 <> 0);
       check_bool_m6
         "M6-T9 BREAK: ... at full strength, the checker's own wording for an unproved \
          UNSAT claim"
         (m6_says out2 m6_unsat_wording);
       if not (m6_says out2 m6_unsat_wording) then print_endline out2);
      (* The optimisation run, stopped at the first node after its first incumbent. *)
      (let compiled, opb, pbp, poc, writer, ctx, check =
         m6_setup dir "opt" fz_optimisation_model
       in
       let objective =
         match compiled.Baguette_flatzinc.Compile.objective with
         | Some o -> o
         | None -> failwith "M6-T9: no objective"
       in
       let printed = ref [] in
       let config =
         { Search.default_config with Search.stop = (fun () -> !printed <> []) }
       in
       let r =
         match
           Search.optimise ~engine:compiled.Baguette_flatzinc.Compile.engine
             ~store:compiled.Baguette_flatzinc.Compile.store ~ctx ~check ~objective
             ~config
             ~on_solution:(fun a -> printed := a :: !printed)
             ()
         with
         | _ -> None
         | exception Search.Stopped { best } -> Some best
       in
       let live = Writer.live_ids writer in
       close_out poc;
       (match r with
       | Some (Some (_, v)) ->
           check_bool_m6
             (Printf.sprintf
                "M6-T9 opt: stopped with the incumbent it printed (%d), which is NOT the \
                 optimum 2 -- so the stop interrupted a search with more to do"
                v)
             (List.length !printed = 1 && v > 2)
       | _ ->
           check_bool_m6 "M6-T9 opt: the stopped run raises Stopped with an incumbent"
             false);
       check_bool_m6 "M6-T9 opt: every id deleted, the soli ids included (I-X2)"
         (live = []);
       let rc, out = m6_veripb veripb dir opb pbp in
       (* M6-T24 (D-0225): the declared floor and the incumbent, where it was NONE. *)
       let v = match r with Some (Some (_, v)) -> v | _ -> -1 in
       check_bool_m6 "M6-T9 opt: veripb -c accepts the stopped optimisation proof"
         (rc = 0 && m6_says out (Printf.sprintf "VERIFIED BOUNDS 0 <= obj <= %d" v));
       if rc <> 0 then print_endline out;
       (* THE BREAKS: a bound that was not derived and a value that was not found are both
          refused, so the line above is a claim the checker weighs. *)
       let proof = read_file pbp in
       let said = Printf.sprintf "conclusion BOUNDS 0 %d ;" v in
       let refuses claim wording =
         let i =
           let rec find i =
             if i + String.length said > String.length proof then
               failwith "M6-T24: no BOUNDS conclusion in the stopped proof"
             else if String.sub proof i (String.length said) = said then i
             else find (i + 1)
           in
           find 0
         in
         let pbp2 = Filename.concat dir "opt_broken.pbp" in
         let oc = open_out pbp2 in
         output_string oc
           (String.sub proof 0 i ^ claim
           ^ String.sub proof
               (i + String.length said)
               (String.length proof - i - String.length said));
         close_out oc;
         let rc, out = m6_veripb veripb dir opb pbp2 in
         if not (rc <> 0 && m6_says out wording) then print_endline out;
         rc <> 0 && m6_says out wording
       in
       check_bool_m6 "M6-T24 BREAK: a value never found is refused as the upper bound"
         (refuses
            (Printf.sprintf "conclusion BOUNDS 0 %d ;" (v - 1))
            (Printf.sprintf
               "The claimed upper bound of %d mismatches the best recorded upper bound \
                of %d."
               (v - 1) v));
       check_bool_m6 "M6-T24 BREAK: optimality of the incumbent is refused"
         (refuses
            (Printf.sprintf "conclusion BOUNDS %d %d ;" v v)
            "Constraint not syntactically implied by any constraint in the database."));
      List.iter
        (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
        (Array.to_list (Sys.readdir dir));
      try Sys.rmdir dir with _ -> ())

(* --------------------------------- M6-T21 / D-0136: the stop poll inside propagation *)

(* M6-T21: [config.stop] is also asked inside [Engine.propagate], after every
   [stop_poll_runs]-th completed propagator run, and a [true] there leaves through M6-T9's
   path. Here the poll is asked after EVERY run ([stop_poll_runs = 1]) and the stop is a
   predicate on the engine's own run counter, so where it lands is deterministic.

   What is asserted, and why each needs asserting:

   1. The run stops INSIDE propagation ([stats.stopped_in_propagation]) and with exactly
      [k] runs taken: the poll fires after the k-th run completes and nothing runs after
      it, which is the "never mid-run, never one more" half of the design.
   2. It stops past the root, with learned constraints on the page, so the conclusion has
      something real to sweep; every id is deleted (I-X2, audit on).
   3. veripb -c accepts the proof and says VERIFIED NO CONCLUSION: a HALF-PROPAGATED node
      concluded NONE is a valid proof.
   4. THE BREAK, as in M6-T9: `conclusion UNSAT` in its place is refused in the checker's
      wording, so (3) is not a checker accepting anything over this file.
   5. THE CONTROL: the same predicate with [stop_poll_runs = 0] (node entry only, M6-T9's
      contract) stops at a node ENTRY and only after MORE than [k] runs -- the node that
      crossed [k] ran on to its end. Without (5), (1) could be a stop that would have
      landed there anyway. *)
let test_m6_t21_stop_in_propagation () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M6-T21: veripb not found -- the stopped proofs were NOT checked. A missing \
         checker is a failure, never a skip."
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_m6t21" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let run ~name ~k ~poll =
        let compiled, opb, pbp, poc, writer, ctx, check = m6_setup dir name m6_pigeons in
        let engine = compiled.Baguette_flatzinc.Compile.engine in
        let stats = Search.stats_create () in
        let config =
          {
            Search.default_config with
            Search.stop = (fun () -> (Engine.counters engine).Engine.c_runs >= k);
            stop_poll_runs = poll;
          }
        in
        let stopped =
          match
            Search.solve ~engine ~store:compiled.Baguette_flatzinc.Compile.store ~ctx
              ~check ~stats ~config ()
          with
          | _ -> false
          | exception Search.Stopped { best = None } -> true
          | exception Search.Stopped { best = Some _ } -> false
        in
        let live = Writer.live_ids writer in
        close_out poc;
        (stopped, stats, (Engine.counters engine).Engine.c_runs, live, opb, pbp)
      in
      (* The first k whose stop lands strictly inside a node PAST the root, once something
         has been learned: a k that a node's propagation happens to end on is caught at
         the next entry instead, and a k inside the root's propagation leaves nothing on
         the page to sweep; neither is this lane's case. Deterministic, so the same k on
         every machine. *)
      let rec pick k =
        if k > 200 then None
        else
          let ((_, st, runs, _, _, _) as r) = run ~name:"t21" ~k ~poll:1 in
          if
            st.Search.stopped_in_propagation && runs = k && st.Search.nodes > 1
            && st.Search.n_learned > 0
          then Some (k, r)
          else pick (k + 1)
      in
      (match pick 1 with
      | None ->
          check_bool_m6
            "M6-T21: some k in 1..200 stops INSIDE propagation, past the root and after \
             a learned constraint, with exactly k runs taken"
            false
      | Some (k, (stopped, st, runs, live, opb, pbp)) ->
          check_bool_m6 "M6-T21: the stopped run raises Stopped, no incumbent" stopped;
          check_bool_m6
            (Printf.sprintf
               "M6-T21: ... INSIDE propagation, after exactly the k = %d-th run (%d \
                taken)"
               k runs)
            (st.Search.stopped_in_propagation && runs = k);
          check_bool_m6
            (Printf.sprintf
               "M6-T21: ... past the root, with learned constraints (%d nodes, %d \
                learned)"
               st.Search.nodes st.Search.n_learned)
            (st.Search.nodes > 1 && st.Search.n_learned > 0);
          check_bool_m6 "M6-T21: ... every id it received is deleted (I-X2, audit on)"
            (live = []);
          let proof = read_file pbp in
          check_bool_m6
            "M6-T21: ... and the proof ENDS output NONE / conclusion NONE / end"
            (m6_says proof
               "output NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n");
          let rc, out = m6_veripb veripb dir opb pbp in
          check_bool_m6
            "M6-T21: veripb -c accepts the proof of a run stopped mid-propagation, and \
             says VERIFIED NO CONCLUSION"
            (rc = 0 && m6_says out "VERIFIED NO CONCLUSION");
          if rc <> 0 then print_endline out;
          let needle = "conclusion NONE ;" in
          let i =
            let rec find i =
              if i + String.length needle > String.length proof then 0
              else if String.sub proof i (String.length needle) = needle then i
              else find (i + 1)
            in
            find 0
          in
          let broken =
            String.sub proof 0 i ^ "conclusion UNSAT ;"
            ^ String.sub proof
                (i + String.length needle)
                (String.length proof - i - String.length needle)
          in
          let pbp2 = Filename.concat dir "t21_broken.pbp" in
          let oc = open_out pbp2 in
          output_string oc broken;
          close_out oc;
          let rc2, out2 = m6_veripb veripb dir opb pbp2 in
          check_bool_m6
            "M6-T21 BREAK: `conclusion UNSAT` in place of NONE is REFUSED, at full \
             strength (the checker's own wording for an unproved UNSAT claim)"
            (rc2 <> 0 && m6_says out2 m6_unsat_wording);
          if not (m6_says out2 m6_unsat_wording) then print_endline out2;
          (* (5) the control. *)
          let stopped0, st0, runs0, live0, opb0, pbp0 = run ~name:"t21ctl" ~k ~poll:0 in
          check_bool_m6
            (Printf.sprintf
               "M6-T21 CONTROL: node entry only, the same stop lands at a node ENTRY and \
                after MORE than k = %d runs (%d)"
               k runs0)
            (stopped0 && (not st0.Search.stopped_in_propagation) && runs0 > k);
          check_bool_m6 "M6-T21 CONTROL: ... every id deleted (I-X2)" (live0 = []);
          let rc0, out0 = m6_veripb veripb dir opb0 pbp0 in
          check_bool_m6 "M6-T21 CONTROL: ... and veripb -c accepts it, NO CONCLUSION"
            (rc0 = 0 && m6_says out0 "VERIFIED NO CONCLUSION");
          if rc0 <> 0 then print_endline out0);
      List.iter
        (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
        (Array.to_list (Sys.readdir dir));
      try Sys.rmdir dir with _ -> ())

(* ------------------------------------- M7-T27 (b) / D-0123: the streamed .opb, end to end *)

(* The CLI's shape: [Encoding.row_sink] set to stream BEFORE [Compile.compile], the
   .opb written from the body file, the proof over it, and veripb over both. Holes, a
   disequality (an aux, renamed) and a bare bool, so that every header input of the
   streamed writer is exercised on the way to the checker; and the .opb compared byte
   for byte with the retained-rows compile of the same source, which is the path every
   file in test/expected/ came from. *)
let m7t27_src =
  "var {1,3,5}: x :: output_var;\n\
   var 0..4: y :: output_var;\n\
   var bool: b :: output_var;\n\
   constraint int_lin_le([1,-1],[x,y],1);\n\
   constraint int_ne(x, y);\n\
   constraint bool2int(b, y);\n\
   solve satisfy;\n"

let test_m7t27_streamed_proof_verifies () =
  match veripb_path () with
  | None ->
      incr failures;
      print_endline
        "FAIL M7-T27 (b): veripb not found, so the streamed .opb was NOT checked against \
         its proof. A missing checker is a failure, never a skip."
  | Some veripb -> (
      let dir = Filename.temp_file "baguette_m7t27" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let rows = Filename.concat dir "streamed.opb.rows" in
      let saved = !Encoding.row_sink in
      Encoding.row_sink := Encoding.Stream_rows_to rows;
      let opb, pbp, outcome =
        Fun.protect
          ~finally:(fun () -> Encoding.row_sink := saved)
          (fun () ->
            let opb, pbp, outcome = el_solve dir "streamed" m7t27_src in
            (opb, pbp, outcome))
      in
      check "M7-T27 (b) e2e: the scene is SAT"
        (match outcome with Search.Sat _ -> true | _ -> false);
      check "M7-T27 (b) e2e: the body file was consumed" (not (Sys.file_exists rows));
      let rc, out = m6_veripb veripb dir opb (Filename.concat dir "streamed.pbp") in
      check "M7-T27 (b) e2e: veripb VERIFIES the proof over the streamed .opb (I-X1)"
        (rc = 0);
      if rc <> 0 then print_endline out;
      ignore pbp;
      let opb_ref, _, _ = el_solve dir "retained" m7t27_src in
      check "M7-T27 (b) e2e: the ambient policy was restored"
        (!Encoding.row_sink = Encoding.Retain_rows);
      let streamed = read_file opb and retained = read_file opb_ref in
      check "M7-T27 (b) e2e: the streamed .opb is byte-identical to the retained one"
        (streamed = retained);
      if streamed <> retained then
        Printf.printf "  streamed:\n%s\n  retained:\n%s\n" streamed retained;
      check "M7-T27 (b) e2e: the renamed aux is in the header"
        (m6_says streamed "* name $ne0 -> _ne0\n");
      List.iter
        (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
        (Array.to_list (Sys.readdir dir));
      try Sys.rmdir dir with _ -> ())

(* ------------------------------------------------- M9-no-proof-T2: solving without a proof

   docs/DECISIONS.md D-0126 (the design) and D-0135 (what landed); docs/SPEC.md section 1's
   amended paragraph. `--no-proof` is a measurement instrument, and this is the ONLY unit
   test allowed to use it, beside the stdout-identity pass of scripts/run_model_tests.sh.
   Two lanes:

   (a) IN PROCESS, the id rule. The same three models compiled under [Retain_rows] with a
       real writer and under [Discard_rows] with the null writer ([Writer.create
       ~null:true]): the same answer, the same tree ([Search.stats]), the same
       [Encoding.n_constraints] and [Encoding.cost], the same rung, hole and
       direct-encoding ids -- every id an [Explanation] can carry, D-0126's rule -- and
       FEWER deferred reasons materialised, which is what the mode is for.

   (b) THROUGH THE CLI, the files. `baguette M.fzn --no-proof` prints the bytes the proved
       run prints, exits as it exits, writes to stderr only what it is asked for and
       creates NO file: none beside the model, none in the temp directory. `--stats` says
       the run is unproved, `--time` counts zero emitted lines, and `--no-proof --proof` is
       refused with exit 2 before anything is opened. test/unit/dune declares bin/main.exe
       as a dependency of the test binaries, so `dune runtest` builds the solver this lane
       runs -- the stale-binary trap CLAUDE.md records does not reach it.

   The three models are test/models/ files verbatim: alldiff_const_sat (a direct encoding,
   so [start_proof] mints ids through the writer), backjump_deep_unsat (learning and
   backjumps, so [Learned.introduce] and [Retention] run through the null writer) and
   opt_min_sat (branch and bound, so `soli` and the conclusion do). *)

let m9_models =
  [
    ( "alldiff_const_sat",
      "var 1..3: p :: output_var;\n\
       var 1..3: q :: output_var;\n\
       constraint all_different_int([p, q, 2]);\n\
       constraint int_le(p, q);\n\
       solve satisfy;\n" );
    ( "backjump_deep_unsat",
      "var 0..1: p :: output_var;\n\
       var 0..1: q :: output_var;\n\
       var 0..1: r :: output_var;\n\
       var 0..3: x :: output_var;\n\
       var 0..3: y :: output_var;\n\
       constraint int_ne(x, y);\n\
       constraint int_eq(x, y);\n\
       solve satisfy;\n" );
    ( "opt_min_sat",
      "var 0..5: x :: output_var;\n\
       var 0..5: y :: output_var;\n\
       constraint int_lin_le([-1,-1],[x,y],-4);\n\
       constraint int_lin_le([1,-2],[x,y],0);\n\
       solve minimize y;\n" );
  ]

(* What the proved and the unproved run of one model must agree on. *)
type m9_run = {
  m9_answer : string; (* the outcome, rendered *)
  m9_tree : int list; (* nodes, decisions, conflicts, max_depth, skipped, learned, pb *)
  m9_n : int; (* Encoding.n_constraints: ids minted by [commit] *)
  m9_cost : Encoding.cost;
  m9_ids : (string * int option) list; (* every id an Explanation can carry, by name *)
  m9_later : int; (* deferred reasons materialised during this solve (D-0124) *)
}

let m9_solve ~null name src =
  let saved = !Encoding.row_sink in
  Encoding.row_sink := if null then Encoding.Discard_rows else Encoding.Retain_rows;
  let m = Baguette_flatzinc.Builder.of_string ~file:name src in
  let compiled =
    Fun.protect
      ~finally:(fun () -> Encoding.row_sink := saved)
      (fun () -> Baguette_flatzinc.Compile.compile m)
  in
  let enc = compiled.Baguette_flatzinc.Compile.encoding in
  let store = compiled.Baguette_flatzinc.Compile.store in
  let path = if null then Filename.null else Filename.temp_file "baguette_m9" ".pbp" in
  let oc = open_out path in
  let writer = Writer.create ~audit:(not null) ~null oc in
  Encoding.start_proof enc writer;
  let ctx = mk_ctx writer enc in
  let stats = Search.stats_create () in
  let check_asn assignment =
    let values = Array.make (Baguette_flatzinc.Model.nvars m) 0 in
    List.iter (fun (v, x) -> values.(Var.to_int v) <- x) assignment;
    Baguette_flatzinc.Model.check_assignment m values
  in
  let render asn =
    String.concat " "
      (List.map (fun (v, x) -> Printf.sprintf "%s=%d" (Store.name store v) x) asn)
  in
  let later0 = !Baguette_core.Reason.materialisations in
  let answer =
    match compiled.Baguette_flatzinc.Compile.objective with
    | None -> (
        match
          Search.solve ~engine:compiled.Baguette_flatzinc.Compile.engine ~store ~ctx
            ~check:check_asn ~stats ?order:compiled.Baguette_flatzinc.Compile.order ()
        with
        | Search.Sat asn -> "SAT " ^ render asn
        | Search.Unsat -> "UNSAT")
    | Some objective -> (
        let printed = ref [] in
        match
          Search.optimise ~engine:compiled.Baguette_flatzinc.Compile.engine ~store ~ctx
            ~check:check_asn ~stats ~objective
            ?order:compiled.Baguette_flatzinc.Compile.order
            ~on_solution:(fun asn -> printed := render asn :: !printed)
            ()
        with
        | Search.Opt (asn, v) ->
            Printf.sprintf "OPT %d %s [%s]" v (render asn)
              (String.concat "; " (List.rev !printed))
        | Search.Opt_unsat -> "OPT_UNSAT")
  in
  let later = !Baguette_core.Reason.materialisations - later0 in
  close_out oc;
  if not null then Sys.remove path;
  let ids =
    List.concat_map
      (fun x ->
        let lo, hi = Encoding.domain enc x in
        List.concat_map
          (fun v ->
            [
              (Printf.sprintf "rung %s>=%d" x v, Encoding.consistency_id enc x v);
              (Printf.sprintf "hole %s<>%d" x v, Encoding.hole_id enc x v);
              (Printf.sprintf "direct-lo %s=%d" x v, Encoding.direct_lo_id enc x v);
              (Printf.sprintf "direct-hi %s=%d" x v, Encoding.direct_hi_id enc x v);
              (Printf.sprintf "direct-fwd %s=%d" x v, Encoding.direct_fwd_id enc x v);
            ])
          (List.init (max 0 (hi - lo + 1)) (fun i -> lo + i))
        @ [ (Printf.sprintf "at-least-one %s" x, Encoding.at_least_one_id enc x) ])
      (Encoding.vars enc)
  in
  {
    m9_answer = answer;
    m9_tree =
      [
        stats.Search.nodes;
        stats.Search.decisions;
        stats.Search.conflicts;
        stats.Search.max_depth;
        stats.Search.skipped;
        stats.Search.n_learned;
        stats.Search.n_pb_learned;
      ];
    m9_n = Encoding.n_constraints enc;
    m9_cost = Encoding.cost enc;
    m9_ids = ids;
    m9_later = later;
  }

let m9_ints xs = String.concat "," (List.map string_of_int xs)
let m9_opt = function None -> "-" | Some i -> string_of_int i

let test_m9_no_proof_in_process () =
  List.iter
    (fun (name, src) ->
      let tag = "M9-no-proof-T2 (a) " ^ name in
      let p = m9_solve ~null:false name src in
      let n = m9_solve ~null:true name src in
      check
        (tag ^ ": the same answer with and without a proof")
        (p.m9_answer = n.m9_answer);
      if p.m9_answer <> n.m9_answer then
        Printf.printf "  proved: %s\n  no-proof: %s\n" p.m9_answer n.m9_answer;
      check
        (tag
       ^ ": the same tree -- nodes, decisions, conflicts, depth, skipped, learned, pb")
        (p.m9_tree = n.m9_tree);
      if p.m9_tree <> n.m9_tree then
        Printf.printf "  proved: %s\n  no-proof: %s\n" (m9_ints p.m9_tree)
          (m9_ints n.m9_tree);
      check
        (tag ^ ": the same number of ids minted by Encoding.commit (D-0126 rule 1)")
        (p.m9_n = n.m9_n);
      check (tag ^ ": the same Encoding.cost") (p.m9_cost = n.m9_cost);
      check
        (tag ^ ": every rung, hole and direct-encoding id identical (D-0126's id rule)")
        (p.m9_ids = n.m9_ids);
      if p.m9_ids <> n.m9_ids then
        List.iter2
          (fun (k, a) (_, b) ->
            if a <> b then
              Printf.printf "  %s: proved %s, no-proof %s\n" k (m9_opt a) (m9_opt b))
          p.m9_ids n.m9_ids;
      if name = "alldiff_const_sat" then
        check
          (tag
         ^ ": the direct encoding WAS minted through the null writer (the control: \
            start_proof ran, D-0126 rule 2)")
          (List.exists
             (fun (k, v) ->
               String.length k > 7 && String.sub k 0 7 = "direct-" && v <> None)
             n.m9_ids);
      check
        (Printf.sprintf
           "%s: --no-proof materialises no more deferred reasons than the proved run (%d \
            vs %d)"
           tag n.m9_later p.m9_later)
        (n.m9_later <= p.m9_later);
      if name <> "alldiff_const_sat" then
        check
          (tag
         ^ ": ...and strictly fewer: the trace's per-entry materialisations are gone \
            (D-0124, D-0126)")
          (n.m9_later < p.m9_later))
    m9_models

(* bin/main.exe, found above the test's own cwd (dune runs a test in
   _build/default/test/unit, and _build/default/bin/main.exe is two levels up). *)
let m9_binary () =
  let exe = Filename.concat "bin" "main.exe" in
  let rec up d n =
    if n > 6 then None
    else
      let p = Filename.concat d exe in
      if Sys.file_exists p then Some p
      else up (Filename.concat d Filename.parent_dir_name) (n + 1)
  in
  up (Sys.getcwd ()) 0

(* Run the solver with [args] from inside [cwd]; return (exit code, stdout, stderr) and
   leave [cwd] as it was apart from what the solver itself created. *)
let m9_run ?tmpdir binary ~cwd args =
  let out = Filename.concat cwd "out" and err = Filename.concat cwd "err" in
  let env =
    match tmpdir with None -> "" | Some d -> "TMPDIR=" ^ Filename.quote d ^ " "
  in
  let rc =
    Sys.command
      (Printf.sprintf "cd %s && %s%s %s > %s 2> %s" (Filename.quote cwd) env
         (Filename.quote binary) args (Filename.quote out) (Filename.quote err))
  in
  let o = read_file out and e = read_file err in
  Sys.remove out;
  Sys.remove err;
  (rc, o, e)

(* The temp directory a run sees: its own, empty, so "--no-proof opened no temp file" is
   a statement about THIS run and not about whatever the other test binaries dune runs in
   parallel create and delete in the shared one. Until M9-no-proof-T5 the CLI opened its
   proof channel without --proof with [Filename.temp_file], which honours TMPDIR; it no
   longer opens any temp file, and the check stays as the guard that it does not. *)
let m9_fresh_dir parent name =
  let d = Filename.concat parent name in
  Sys.mkdir d 0o700;
  d

let rec m9_rm_rf p =
  if Sys.is_directory p then (
    Array.iter (fun f -> m9_rm_rf (Filename.concat p f)) (Sys.readdir p);
    Sys.rmdir p)
  else Sys.remove p

let test_m9_no_proof_cli () =
  match m9_binary () with
  | None ->
      incr failures;
      print_endline
        "FAIL M9-no-proof-T2 (b): bin/main.exe was not found above the test's cwd, so \
         the CLI lane was NOT run. Build bin/ first (`dune build bin/`); test/unit/dune \
         declares the dependency, so under `dune runtest` this cannot happen."
  | Some binary ->
      let binary =
        if Filename.is_relative binary then Filename.concat (Sys.getcwd ()) binary
        else binary
      in
      let dir = Filename.temp_file "baguette_m9cli" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      List.iter
        (fun (name, src) ->
          let tag = "M9-no-proof-T2 (b) " ^ name in
          let fzn = Filename.concat dir (name ^ ".fzn") in
          let oc = open_out fzn in
          output_string oc src;
          close_out oc;
          let q = Filename.quote fzn in
          let proved = Filename.concat dir (name ^ ".proved")
          and unproved = Filename.concat dir (name ^ ".noproof") in
          Sys.mkdir proved 0o700;
          Sys.mkdir unproved 0o700;
          let tmp = m9_fresh_dir dir (name ^ ".tmp") in
          let rc_p, out_p, err_p = m9_run binary ~cwd:proved ("--proof p " ^ q) in
          let rc_n, out_n, err_n =
            m9_run ~tmpdir:tmp binary ~cwd:unproved ("--no-proof " ^ q)
          in
          check (tag ^ ": the proved run exits 0") (rc_p = 0);
          check (tag ^ ": --no-proof exits as the proved run does") (rc_n = rc_p);
          check
            (tag ^ ": --no-proof prints the proved run's bytes, exactly")
            (out_n = out_p);
          if out_n <> out_p then Printf.printf "  proved:\n%s  no-proof:\n%s" out_p out_n;
          check
            (tag ^ ": neither run writes to stderr unasked (M1-T49)")
            (err_p = "" && err_n = "");
          if err_p <> "" || err_n <> "" then
            Printf.printf "  proved:\n%s  no-proof:\n%s" err_p err_n;
          check
            (tag ^ ": the proved run DID write p.opb and p.pbp (the control)")
            (Sys.file_exists (Filename.concat proved "p.opb")
            && Sys.file_exists (Filename.concat proved "p.pbp"));
          check
            (tag ^ ": --no-proof created NO file beside the model")
            (Sys.readdir unproved = [||]);
          check (tag ^ ": ...and none in its temp directory") (Sys.readdir tmp = [||]);
          let _, out_s, err_s =
            m9_run ~tmpdir:tmp binary ~cwd:unproved ("--no-proof --stats " ^ q)
          in
          check
            (tag ^ ": --stats under --no-proof says the run is unproved")
            (m6_says err_s "stats: no-proof" && m6_says err_s "UNVERIFIED");
          check
            (tag ^ ": ...and reports no proof-shape or atom counter")
            ((not (m6_says err_s "pol-tokens")) && not (m6_says err_s "atomlinks"));
          check (tag ^ ": ...with stdout untouched") (out_s = out_p);
          let _, out_t, err_t =
            m9_run ~tmpdir:tmp binary ~cwd:unproved ("--no-proof --time " ^ q)
          in
          check
            (tag ^ ": --time under --no-proof counts zero emitted lines")
            (m6_says err_t (Printf.sprintf "time: %-10s %10d lines" "emitln" 0));
          check (tag ^ ": ...with stdout untouched") (out_t = out_p);
          check
            (tag ^ ": --stats and --time created no file either")
            (Sys.readdir unproved = [||] && Sys.readdir tmp = [||]);
          let rc_x, out_x, err_x =
            m9_run binary ~cwd:unproved ("--no-proof --proof x " ^ q)
          in
          check (tag ^ ": --no-proof beside --proof is a usage error, exit 2") (rc_x = 2);
          check
            (tag ^ ": ...that names both flags")
            (m6_says err_x "--no-proof" && m6_says err_x "--proof");
          check
            (tag ^ ": ...prints nothing on stdout and opens no file")
            (out_x = "" && Sys.readdir unproved = [||]))
        m9_models;
      m9_rm_rf dir

(* M7-T32 (D-0150): the MiniZinc standard flags, through the real binary. Each flag is a
   thin mapping onto an option that already existed, so the lane's main claim is a
   NEGATIVE one: a flag that only asks for what the CLI does anyway (-i, -a on an
   optimisation model, -n 1, -r, -p, -t with room to spare) leaves stdout byte for byte
   as the plain run's, and stderr empty. The positive claims: -i's run prints every
   improving solution with one `soli` per `----------`, and the proof verifies; -s
   appends exactly one `%%%mzn-stat:` block to that stdout; -f becomes the D-0137
   combination with its warning under -v; enumeration on a SATISFACTION model is
   refused with exit 3 before anything is printed; a malformed argument is a usage
   error, exit 2. tools/baguette.msc declares the flags; MiniZinc's own handling of them
   (which it passes, and when) is measured in D-0150, not here. *)
let m7t32_sat_src =
  "var 1..4: a :: output_var;\n\
   var 1..4: b :: output_var;\n\
   constraint int_lt(a, b);\n\
   solve satisfy;\n"

let test_m7t32_std_flags () =
  match m9_binary () with
  | None ->
      incr failures;
      print_endline
        "FAIL M7-T32: bin/main.exe was not found above the test's cwd, so the \
         standard-flags lane was NOT run. Build bin/ first."
  | Some binary ->
      let binary =
        if Filename.is_relative binary then Filename.concat (Sys.getcwd ()) binary
        else binary
      in
      let dir = Filename.temp_file "baguette_m7t32" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let write name src =
        let p = Filename.concat dir (name ^ ".fzn") in
        let oc = open_out p in
        output_string oc src;
        close_out oc;
        Filename.quote p
      in
      let opt = write "opt" fz_optimisation_model and sat = write "sat" m7t32_sat_src in
      (* M9-no-proof-T5: a run without --proof keeps ./opt.opb and ./opt.pbp, so every run
         here that does not name its proof names one, `plain`, rather than leaving the
         default name to be overwritten by the next run; the end of the lane checks that
         no default-named proof appeared. A proved run rather than --no-proof, because
         SPEC 1 says `make check` always proves. *)
      let run args =
        m9_run binary ~cwd:dir
          (if m6_says args "--proof " then args else "--proof plain " ^ args)
      in
      let tag = "M7-T32" in
      (* The plain runs every flag is compared with. *)
      let rc_o, out_o, err_o = run opt and rc_s, out_s, err_s = run sat in
      check
        (tag ^ ": the plain runs exit 0 with stderr empty (the control)")
        (rc_o = 0 && rc_s = 0 && err_o = "" && err_s = "");
      check
        (tag ^ ": the optimisation model prints two improving solutions and the marker")
        (count_substring out_o "----------\n" = 2 && m6_says out_o "==========\n");
      let same name model args out_ref =
        let rc, out, err = run (args ^ " " ^ model) in
        check
          (Printf.sprintf "%s: %s leaves stdout as the plain run's and stderr empty" tag
             name)
          (rc = 0 && out = out_ref && err = "");
        if out <> out_ref || err <> "" then
          Printf.printf "  plain:\n%s  with %s:\n%s  stderr:\n%s" out_ref args out err
      in
      same "-i (optimisation)" opt "-i" out_o;
      same "-a (optimisation)" opt "-a" out_o;
      same "--all (optimisation)" opt "--all" out_o;
      same "-n 3 (optimisation: -n is for satisfaction)" opt "-n 3" out_o;
      same "-i (satisfaction: -i is for optimisation)" sat "-i" out_s;
      same "-n 1 (satisfaction)" sat "-n 1" out_s;
      same "-t 600000" opt "-t 600000" out_o;
      same "-r 7 -p 4 (no -s, no -v: no note)" opt "-r 7 -p 4" out_o;
      (* -i with the proof: one `soli` per printed solution, and it verifies. *)
      let rc_p, out_p, _ = run ("-i --proof ip " ^ opt) in
      let pbp = read_file (Filename.concat dir "ip.pbp") in
      check
        (tag ^ ": -i --proof prints what the plain run prints")
        (rc_p = 0 && out_p = out_o);
      check
        (tag ^ ": ...with one `soli` line per printed solution")
        (count_substring pbp " soli " + count_substring pbp "\nsoli "
        = count_substring out_p "----------\n");
      (match veripb_path () with
      | None ->
          incr failures;
          Printf.printf "FAIL %s: veripb not found -- the -i proof was NOT checked.\n" tag
      | Some veripb ->
          let rc, out =
            m6_veripb veripb dir
              (Filename.concat dir "ip.opb")
              (Filename.concat dir "ip.pbp")
          in
          check
            (tag ^ ": ...and veripb verifies it at the printed optimum")
            (rc = 0 && m6_says out "VERIFIED BOUNDS 2 <= obj <= 2");
          (* -f with the proof, on this small model: the mapping reaches the search and
             the proof closes. The instances D-0137 section 13 refused are M7-T31's, and
             D-0148's 1 233 runs (hrc under -f's combination among them) cover them. *)
          let rc_f, out_f, _ = run ("-f --proof fp " ^ opt) in
          let rc, out =
            m6_veripb veripb dir
              (Filename.concat dir "fp.opb")
              (Filename.concat dir "fp.pbp")
          in
          check
            (tag ^ ": -f solves the model to the same optimum and veripb verifies it")
            (rc_f = 0
            && m6_says out_f "y = 2;\n----------\n==========\n"
            && rc = 0
            && m6_says out "VERIFIED BOUNDS 2 <= obj <= 2"));
      (* -s: the plain stdout, then exactly one block. *)
      let rc_st, out_st, err_st = run ("-s -r 7 -p 4 " ^ opt) in
      let lo = String.length out_o in
      let tail =
        if String.length out_st >= lo && String.sub out_st 0 lo = out_o then
          Some (String.sub out_st lo (String.length out_st - lo))
        else None
      in
      let lines =
        match tail with
        | None -> []
        | Some t -> List.filter (( <> ) "") (String.split_on_char '\n' t)
      in
      check (tag ^ ": -s keeps the plain stdout as its prefix") (rc_st = 0 && tail <> None);
      check
        (tag ^ ": ...and appends one %%%mzn-stat block, ending %%%mzn-stat-end")
        (lines <> []
        && List.for_all
             (fun l -> String.length l >= 11 && String.sub l 0 11 = "%%%mzn-stat")
             lines
        && List.nth lines (List.length lines - 1) = "%%%mzn-stat-end"
        && count_substring out_st "%%%mzn-stat-end" = 1);
      check
        (tag ^ ": ...naming nodes, failures and the objective it reached")
        (List.mem "%%%mzn-stat: objective=2" lines
        && List.exists (fun l -> m6_says l "%%%mzn-stat: nodes=") lines
        && List.exists (fun l -> m6_says l "%%%mzn-stat: failures=") lines);
      check
        (tag ^ ": ...with --stats on stderr and the -p and -r notes")
        (m6_says err_st "stats: nodes" && m6_says err_st "one thread"
        && m6_says err_st "-r 7 accepted and unused");
      (* -f: the combination, with an explicit flag winning in either order. *)
      let _, _, err_f = run ("-f -v " ^ opt) in
      check
        (tag ^ ": -f -v says alternate, luby and phase saving, and no longer warns")
        (m6_says err_f "search=alternate restarts=luby:100 phase-saving=true"
        && (not (m6_says err_f "WARNING"))
        && not (m6_says err_f "M7-T31"));
      let _, _, err_f2 = run ("--search activity -f --restarts geom -v " ^ opt) in
      check
        (tag ^ ": an explicit --search or --restarts wins over -f, in either order")
        (m6_says err_f2 "search=activity restarts=geom:100:1.5 phase-saving=true");
      let _, _, err_t = run ("-t 2500 -v " ^ opt) in
      check (tag ^ ": -t is milliseconds") (m6_says err_t "time-limit=2.5s");
      (* Refused: enumeration of a satisfaction model, exit 3, nothing on stdout. *)
      List.iter
        (fun args ->
          let rc, out, err = run (args ^ " " ^ sat) in
          check
            (Printf.sprintf
               "%s: %s on a satisfaction model is refused, exit 3, stdout empty" tag args)
            (rc = 3 && out = "" && m6_says err "D-0150"))
        [ "-a"; "--all"; "-n 2" ];
      (* Malformed arguments: usage errors, exit 2. *)
      List.iter
        (fun args ->
          let rc, out, _ = run (args ^ " " ^ opt) in
          check
            (Printf.sprintf "%s: `%s` is a usage error, exit 2" tag args)
            (rc = 2 && out = ""))
        [ "-t abc"; "-t -5"; "-n 0"; "-p 0"; "-r x"; "-n" ];
      check
        (tag ^ ": no run of this lane left a default-named proof (M9-no-proof-T5)")
        (List.for_all
           (fun f -> not (Sys.file_exists (Filename.concat dir f)))
           [ "opt.opb"; "opt.pbp"; "sat.opb"; "sat.pbp" ]);
      m9_rm_rf dir

(* M9-no-proof-T5 (D-0163): THE DEFAULT RUN KEEPS ITS PROOF. The user decided on 2026-11-19
   that a run without --proof writes the proof and keeps it, under the name
   bin/main.ml's [default_proof_prefix] takes from the model; the DIRECTORY (the current
   one) is the proposal on record and the user's to confirm, so this lane pins the rule as
   it stands and is the one place to change with it. Through the real binary, each run in
   its own empty cwd with the model elsewhere:
     (a) `baguette DIR/keep.fzn` writes ./keep.opb and ./keep.pbp, veripb accepts them,
         stderr is empty (M1-T49) and nothing appears beside the model;
     (b) a second run overwrites them with the same bytes and leaves nothing else;
     (c) a model without the .fzn extension keeps its whole name: ./bare.opb;
     (d) MiniZinc's temporary `mznfile*.fzn` gives ./baguette-proof.opb and .pbp, which
         veripb accepts, and stderr names both by their full path;
     (e) a model the front end refuses (exit 2) leaves no file at all. *)
let test_m9t5_default_keeps_proof () =
  match (m9_binary (), veripb_path ()) with
  | None, _ ->
      incr failures;
      print_endline
        "FAIL M9-no-proof-T5: bin/main.exe was not found above the test's cwd, so the \
         default-proof lane was NOT run. Build bin/ first."
  | _, None ->
      incr failures;
      print_endline
        "FAIL M9-no-proof-T5: veripb not found -- the kept proofs were NOT checked. A \
         missing checker is a failure, never a skip."
  | Some binary, Some veripb ->
      let binary =
        if Filename.is_relative binary then Filename.concat (Sys.getcwd ()) binary
        else binary
      in
      let tag = "M9-no-proof-T5" in
      let dir = Filename.temp_file "baguette_m9t5" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let models = m9_fresh_dir dir "models" in
      let write name src =
        let p = Filename.concat models name in
        let oc = open_out p in
        output_string oc src;
        close_out oc;
        Filename.quote p
      in
      let sorted d = List.sort compare (Array.to_list (Sys.readdir d)) in
      let verifies cwd prefix =
        let rc, out =
          m6_veripb veripb dir
            (Filename.concat cwd (prefix ^ ".opb"))
            (Filename.concat cwd (prefix ^ ".pbp"))
        in
        rc = 0 && m6_says out "VERIFIED"
      in
      (* (a) *)
      let keep = write "keep.fzn" m7t32_sat_src in
      let cwd_a = m9_fresh_dir dir "a" in
      let rc, out, err = m9_run binary ~cwd:cwd_a keep in
      check
        (tag ^ " (a): the plain run exits 0 and prints a solution")
        (rc = 0 && m6_says out "----------");
      check (tag ^ " (a): ...writes nothing on stderr (M1-T49)") (err = "");
      check
        (tag ^ " (a): ...and keeps exactly ./keep.opb and ./keep.pbp in its cwd")
        (sorted cwd_a = [ "keep.opb"; "keep.pbp" ]);
      check (tag ^ " (a): ...which veripb accepts") (verifies cwd_a "keep");
      check
        (tag ^ " (a): ...and nothing appears beside the model")
        (sorted models = [ "keep.fzn" ]);
      (* (b) *)
      let first = read_file (Filename.concat cwd_a "keep.pbp") in
      let rc2, out2, _ = m9_run binary ~cwd:cwd_a keep in
      check
        (tag ^ " (b): a second run overwrites the proof, the same bytes, nothing else")
        (rc2 = 0 && out2 = out
        && read_file (Filename.concat cwd_a "keep.pbp") = first
        && sorted cwd_a = [ "keep.opb"; "keep.pbp" ]);
      (* (c) *)
      let bare = write "bare" m7t32_sat_src in
      let cwd_c = m9_fresh_dir dir "c" in
      let rc, _, _ = m9_run binary ~cwd:cwd_c bare in
      check
        (tag ^ " (c): a model without .fzn keeps its whole name: ./bare.opb, ./bare.pbp")
        (rc = 0 && sorted cwd_c = [ "bare.opb"; "bare.pbp" ]);
      (* (d) *)
      let mzn = write "mznfileQ1w2E3.fzn" m7t32_sat_src in
      let cwd_d = m9_fresh_dir dir "d" in
      let rc, _, err = m9_run binary ~cwd:cwd_d mzn in
      check
        (tag ^ " (d): MiniZinc's temporary model gives ./baguette-proof.opb and .pbp")
        (rc = 0 && sorted cwd_d = [ "baguette-proof.opb"; "baguette-proof.pbp" ]);
      check (tag ^ " (d): ...which veripb accepts") (verifies cwd_d "baguette-proof");
      check
        (tag ^ " (d): ...and stderr names both by their full path")
        (m6_says err (Filename.concat cwd_d "baguette-proof.opb")
        && m6_says err (Filename.concat cwd_d "baguette-proof.pbp"));
      if not (m6_says err (Filename.concat cwd_d "baguette-proof.opb")) then
        Printf.printf "  stderr:\n%s" err;
      (* (e) *)
      let bad = write "bad.fzn" "this is not flatzinc;\n" in
      let cwd_e = m9_fresh_dir dir "e" in
      let rc, _, _ = m9_run binary ~cwd:cwd_e bad in
      check
        (tag ^ " (e): a refused model exits 2 and leaves no file")
        (rc = 2 && sorted cwd_e = []);
      m9_rm_rf dir

(* ------------------------------------------- D-0200: the heap budget is timely *)

(* The M7-T8 budget used to be read only at the end of a major cycle, and a cycle lasts
   longer the larger the heap is: Challenge runs at --max-heap-mb 8192 grew from 6.6 GB at
   one cycle end to the 16 GiB address-space limit before the next, and died on "Fatal
   error: allocation failure during minor GC" instead of the refusal. The same lag, on a
   heap small enough for a test: a 10-into-9 pigeonhole over clauses (Boolean cells, no
   width), whose learned clauses grow the heap, under OCAMLRUNPARAM's [o=100000], a GC
   pacing that makes major cycles rare. [s=256k] pins the minor heap, which bin/main.ml
   otherwise sizes from `ulimit -v`. Measured on f365c1e, before D-0200: exit 5 at 16 MB
   past an 8 MB budget (and exit 0, budget never enforced, without [s=]); after it, 9 MB
   on 30 runs out of 30. Asserted here: exit 5, the refusal's wording, the heap it names
   at most 12 MB -- the poll is a CPU-time ticker, so what the heap gains in one tick
   depends on the machine, and the bound leaves room for that while staying well under
   the 16 MB the old guard reached -- and no runtime abort. *)
let d0200_pigeons =
  let b = Buffer.create 4096 in
  let p = 10 and h = 9 in
  for i = 1 to p do
    for j = 1 to h do
      Buffer.add_string b (Printf.sprintf "var bool: x%d_%d :: output_var;\n" i j)
    done
  done;
  for i = 1 to p do
    Buffer.add_string b
      (Printf.sprintf "constraint bool_clause([%s],[]);\n"
         (String.concat "," (List.init h (fun j -> Printf.sprintf "x%d_%d" i (j + 1)))))
  done;
  for j = 1 to h do
    for i = 1 to p do
      for k = i + 1 to p do
        Buffer.add_string b
          (Printf.sprintf "constraint bool_clause([],[x%d_%d,x%d_%d]);\n" i j k j)
      done
    done
  done;
  Buffer.add_string b "solve satisfy;\n";
  Buffer.contents b

(* M6-T24 (D-0225): REAL signals to the real binary, at instants nothing controls. A
   knapsack whose proof of optimality takes far longer than the test, so every stop lands
   in the search with an incumbent printed. One signal is the clean stop, two at once end
   the proof where it stands, and the heap budget does the same from its own handler.
   Asserted for each: exit 0, a proof veripb accepts with BOUNDS, whose upper bound is the
   last objective value printed, and no `==========`. Which of the two stop paths a pair
   of signals took is not asserted: the first may have stopped the run already. *)
let m6_t24_knapsack =
  let n = 40 and rows = 8 in
  let seed = ref 12345 in
  let next lo hi =
    seed := ((!seed * 1103515245) + 12345) land 0x3fffffff;
    lo + ((!seed lsr 8) mod (hi - lo + 1))
  in
  let b = Buffer.create 4096 in
  let vars = String.concat "," (List.init n (Printf.sprintf "x%d")) in
  let ints l = String.concat "," (List.map string_of_int l) in
  for i = 0 to n - 1 do
    Buffer.add_string b (Printf.sprintf "var 0..1: x%d :: output_var;\n" i)
  done;
  let value = List.init n (fun _ -> next 1 4) in
  Buffer.add_string b
    (Printf.sprintf "var 0..%d: obj :: output_var;\n" (List.fold_left ( + ) 0 value));
  for _ = 1 to rows do
    let w = List.init n (fun _ -> next 3 30) in
    Buffer.add_string b
      (Printf.sprintf "constraint int_lin_le([%s],[%s],%d);\n" (ints w) vars
         (List.fold_left ( + ) 0 w / 2))
  done;
  Buffer.add_string b
    (Printf.sprintf "constraint int_lin_eq([%s,-1],[%s,obj],0);\n" (ints value) vars);
  Buffer.add_string b
    (Printf.sprintf
       "solve :: int_search([%s],first_fail,indomain_min,complete) maximize obj;\n" vars);
  Buffer.contents b

let test_m6_t24_interrupt_cli () =
  match (m9_binary (), veripb_path ()) with
  | None, _ ->
      incr failures;
      print_endline
        "FAIL M6-T24: bin/main.exe was not found above the test's cwd, so the signal \
         lane was NOT run. Build bin/ first (`dune build bin/`)."
  | _, None ->
      incr failures;
      print_endline "FAIL M6-T24: veripb not found. A missing checker is a failure."
  | Some binary, Some veripb ->
      let binary =
        if Filename.is_relative binary then Filename.concat (Sys.getcwd ()) binary
        else binary
      in
      let dir = Filename.temp_file "baguette_m6t24" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let file f = Filename.concat dir f in
      let oc = open_out (file "k.fzn") in
      output_string oc m6_t24_knapsack;
      close_out oc;
      let last_obj o =
        List.fold_left
          (fun acc l -> try Scanf.sscanf l "obj = %d;" (fun v -> Some v) with _ -> acc)
          None (String.split_on_char '\n' o)
      in
      let case name flags how =
        let cmd =
          Printf.sprintf "%s %s %s --proof %s > %s 2> %s" (Filename.quote binary) flags
            (Filename.quote (file "k.fzn"))
            (Filename.quote (file "p"))
            (Filename.quote (file "out"))
            (Filename.quote (file "err"))
        in
        let rc = Sys.command (how cmd) in
        let o = read_file (file "out") and e = read_file (file "err") in
        check
          (Printf.sprintf "M6-T24 %s: the stopped run exits 0 (got %d)" name rc)
          (rc = 0);
        check
          (Printf.sprintf "M6-T24 %s: an answer was printed, and not as optimal" name)
          (last_obj o <> None && not (m6_says o "=========="));
        check
          (Printf.sprintf "M6-T24 %s: stderr says it was stopped" name)
          (m6_says e "limit: ");
        let vrc, out = m6_veripb veripb dir (file "p.opb") (file "p.pbp") in
        let want =
          match last_obj o with
          | Some v -> Printf.sprintf "<= obj <= %d" (-v)
          | None -> "no value printed"
        in
        check
          (Printf.sprintf "M6-T24 %s: veripb -c accepts the proof, BOUNDS ... %s" name
             want)
          (vrc = 0 && m6_says out "VERIFIED BOUNDS" && m6_says out want);
        if vrc <> 0 then print_endline out
      in
      (* [exec] so that $! is baguette's own pid. The signal waits for a first printed
         solution and not for a fixed time, so a loaded machine cannot make it early. *)
      let signalled sigs cmd =
        Printf.sprintf
          "(exec %s) & p=$!; n=0; until grep -q -e ---------- %s 2>/dev/null || [ $n -ge \
           600 ]; do sleep 0.1; n=$((n+1)); done; sleep 0.3; %s wait $p"
          cmd
          (Filename.quote (file "out"))
          (String.concat " "
             (List.map (fun s -> Printf.sprintf "kill -%s $p 2>/dev/null;" s) sigs))
      in
      case "one SIGTERM" "" (signalled [ "TERM" ]);
      case "one SIGINT" "" (signalled [ "INT" ]);
      case "one SIGXCPU, -f" "-f" (signalled [ "XCPU" ]);
      case "SIGINT then SIGTERM" "" (signalled [ "INT"; "TERM" ]);
      case "SIGTERM twice, order encoding" "--bits-above none"
        (signalled [ "TERM"; "TERM" ]);
      (* The grace timer's own signal, sent by hand: the handler it shares. *)
      case "SIGTERM then SIGALRM" "" (signalled [ "TERM"; "ALRM" ]);
      case "--time-limit" "--time-limit 2" Fun.id;
      case "the heap budget" "--max-heap-mb 16" (fun cmd -> "OCAMLRUNPARAM=s=256k " ^ cmd);
      List.iter
        (fun f -> Sys.remove (Filename.concat dir f))
        (Array.to_list (Sys.readdir dir));
      Sys.rmdir dir

let test_d0200_heap_budget_cli () =
  match m9_binary () with
  | None ->
      incr failures;
      print_endline
        "FAIL D-0200: bin/main.exe was not found above the test's cwd, so the \
         heap-budget lane was NOT run. Build bin/ first (`dune build bin/`)."
  | Some binary ->
      let binary =
        if Filename.is_relative binary then Filename.concat (Sys.getcwd ()) binary
        else binary
      in
      let dir = Filename.temp_file "baguette_d0200" "" in
      Sys.remove dir;
      Sys.mkdir dir 0o700;
      let fzn = Filename.concat dir "pigeons.fzn" in
      let oc = open_out fzn in
      output_string oc d0200_pigeons;
      close_out oc;
      let out = Filename.concat dir "out" and err = Filename.concat dir "err" in
      let rc =
        Sys.command
          (Printf.sprintf
             "OCAMLRUNPARAM=s=256k,o=100000 timeout 300 %s --no-proof --max-heap-mb 8 %s \
              > %s 2> %s"
             (Filename.quote binary) (Filename.quote fzn) (Filename.quote out)
             (Filename.quote err))
      in
      let o = read_file out and e = read_file err in
      let reached =
        let needle = "heap has reached " in
        let nl = String.length needle in
        let rec find i =
          if i + nl > String.length e then -1
          else if String.sub e i nl = needle then
            try
              Scanf.sscanf
                (String.sub e (i + nl) (String.length e - i - nl))
                "%d MB" Fun.id
            with _ -> -1
          else find (i + 1)
        in
        find 0
      in
      check "D-0200: a heap budget crossed during the search ends in exit 5" (rc = 5);
      check "D-0200: with the refusal's wording"
        (m6_says e "baguette: the heap budget is exhausted");
      check
        (Printf.sprintf
           "D-0200: naming a heap past the 8 MB budget and at most 12 MB (named %d MB)"
           reached)
        (reached >= 8 && reached <= 12);
      (* At the start of a line: the refusal itself QUOTES the runtime's abort, in
         backquotes, to say what a run without a budget ends in. *)
      check "D-0200: and no runtime abort" (not (m6_says ("\n" ^ e) "\nFatal error"));
      check "D-0200: and no answer printed" (not (m6_says o "=========="));
      if rc <> 5 then Printf.printf "  stderr:\n%s" e;
      List.iter
        (fun f -> Sys.remove (Filename.concat dir f))
        (Array.to_list (Sys.readdir dir));
      Sys.rmdir dir

(* M11-complexity-T18 (D-0216): an all_different's Hall derivations are rebuilt per
   pruning, and on 2011_black-hole_10 under native `table` 156 removals under a 47-variable
   Hall set rebuilt 8.3 M pairwise at-most-one nodes at the root, nearly all of them
   hash-consing hits (55 G instructions; the element decomposition before it, 12.7 G).
   [Alldiff.reuse] hands a node back when building it again would return it. The scene: six
   variables confined to 1..6 (the Hall set) and four more over 1..7, each pushed to 7 by a
   derivation over the six plus itself, so the four meet on 7 and the root is refuted, and
   every derivation is forced. With reuse the Hall set's pairs are built once, without it
   every pruning rebuilds them; the proof must be the same bytes either way, and veripb
   must accept it. *)
let d0216_src =
  let b = Buffer.create 512 in
  for i = 1 to 6 do
    Buffer.add_string b (Printf.sprintf "var 1..6: h%d;\n" i)
  done;
  for i = 1 to 4 do
    Buffer.add_string b (Printf.sprintf "var 1..7: y%d;\n" i)
  done;
  Buffer.add_string b
    "constraint all_different_int([h1,h2,h3,h4,h5,h6,y1,y2,y3,y4]);\nsolve satisfy;\n";
  Buffer.contents b

let test_d0216_amo_reuse () =
  let dir = Filename.temp_file "baguette_d0216" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o755;
  let saved_hc = !Explanation.hashcons and saved_reuse = !Alldiff.amo_reuse in
  let run reuse =
    Explanation.set_hashcons true;
    Alldiff.amo_reuse := reuse;
    Alldiff.pair_builds := 0;
    let name = if reuse then "reuse" else "rebuild" in
    let opb, proof, outcome = el_solve dir name d0216_src in
    (opb, proof, outcome, !Alldiff.pair_builds)
  in
  Fun.protect
    ~finally:(fun () ->
      Explanation.set_hashcons saved_hc;
      Alldiff.amo_reuse := saved_reuse)
    (fun () ->
      let _, proof_off, out_off, pairs_off = run false in
      let opb, proof_on, out_on, pairs_on = run true in
      let unsat = function Search.Unsat -> true | _ -> false in
      check "D-0216: the scene is refuted at the root, both ways"
        (unsat out_off && unsat out_on);
      check "D-0216: the proof is the same bytes with and without reuse"
        (String.equal proof_off proof_on);
      (* The three prunings after the first find the Hall set's own pairs, C(6,2) per
         value over six values, instead of building them: 3 * 6 * 15 = 270 fewer builds
         (673 against 403 when written; the rest is the first pruning and the conflict,
         built once either way). *)
      check
        (Printf.sprintf
           "D-0216: reuse skips the Hall set's pairs in the three later prunings (%d \
            against %d, want at least 270 fewer)"
           pairs_on pairs_off)
        (pairs_off - pairs_on >= 3 * 6 * 15);
      match veripb_path () with
      | None ->
          incr failures;
          Printf.printf "FAIL D-0216: veripb not found -- the proof was NOT checked.\n"
      | Some veripb ->
          let pbp = Filename.concat dir "reuse.pbp" in
          let rc, log = m6_veripb veripb dir opb pbp in
          check "D-0216: veripb accepts the proof" (rc = 0);
          if rc <> 0 then Printf.printf "  veripb said:\n%s\n" log);
  List.iter
    (fun f -> Sys.remove (Filename.concat dir f))
    (Array.to_list (Sys.readdir dir));
  Sys.rmdir dir

(* M20-pernode-T4 (D-0242): the removals one Regin set justifies share its at-least-one
   lines ([Alldiff.alo_lines]), handed back when building them again would return them.
   The scene: h1..h3 over 1..5 lose 2 and 4 at the root, so they are a Hall set over the
   value SET {1, 3, 5}, which no interval states (stage 1 sees [1, 5] with three
   variables); y1..y3 over 1..6 lose 1, 3 and 5 to Regin under that one set. Their sum
   at most 8 then leaves them {2, 4} between three, and the root conflict cites the
   removals of 1 and 3 from each, which forces their derivations. The proof must be the
   same bytes with and without the memo, the memo must be what the later removals used,
   and veripb must accept the proof. *)
let d0242_src =
  "var 1..5: h1;\n\
   var 1..5: h2;\n\
   var 1..5: h3;\n\
   var 1..6: y1;\n\
   var 1..6: y2;\n\
   var 1..6: y3;\n\
   constraint int_ne(h1, 2);\n\
   constraint int_ne(h1, 4);\n\
   constraint int_ne(h2, 2);\n\
   constraint int_ne(h2, 4);\n\
   constraint int_ne(h3, 2);\n\
   constraint int_ne(h3, 4);\n\
   constraint int_lin_le([1,1,1],[y1,y2,y3],8);\n\
   constraint all_different_int([h1,h2,h3,y1,y2,y3]);\n\
   solve satisfy;\n"

let test_d0242_alo_reuse () =
  let dir = Filename.temp_file "baguette_d0242" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o755;
  let saved_hc = !Explanation.hashcons and saved_reuse = !Alldiff.amo_reuse in
  let run reuse =
    Explanation.set_hashcons true;
    Alldiff.amo_reuse := reuse;
    Alldiff.alo_hits := 0;
    let name = if reuse then "reuse" else "rebuild" in
    let opb, proof, outcome = el_solve dir name d0242_src in
    (opb, proof, outcome, !Alldiff.alo_hits)
  in
  Fun.protect
    ~finally:(fun () ->
      Explanation.set_hashcons saved_hc;
      Alldiff.amo_reuse := saved_reuse)
    (fun () ->
      let _, proof_off, out_off, hits_off = run false in
      let opb, proof_on, out_on, hits_on = run true in
      let unsat = function Search.Unsat -> true | _ -> false in
      check "D-0242: the scene is refuted at the root, both ways"
        (unsat out_off && unsat out_on);
      check "D-0242: the proof is the same bytes with and without the memo"
        (String.equal proof_off proof_on);
      check
        (Printf.sprintf
           "D-0242: the eight removals after the first reuse the set's at-least-one \
            lines (%d hits with the memo, %d without)"
           hits_on hits_off)
        (hits_on >= 8 && hits_off = 0);
      match veripb_path () with
      | None ->
          incr failures;
          Printf.printf "FAIL D-0242: veripb not found -- the proof was NOT checked.\n"
      | Some veripb ->
          let pbp = Filename.concat dir "reuse.pbp" in
          let rc, log = m6_veripb veripb dir opb pbp in
          check "D-0242: veripb accepts the proof" (rc = 0);
          if rc <> 0 then Printf.printf "  veripb said:\n%s\n" log);
  List.iter
    (fun f -> Sys.remove (Filename.concat dir f))
    (Array.to_list (Sys.readdir dir));
  Sys.rmdir dir

let () =
  print_endline "";
  List.iter run_model models;
  test_proof_comments_noop ();
  test_m5_branch_and_bound ();
  test_m5_derivation_is_load_bearing ();
  test_element_derivation_is_load_bearing ();
  test_m6_time_limit ();
  test_m6_t21_stop_in_propagation ();
  test_m7t27_streamed_proof_verifies ();
  test_m9_no_proof_in_process ();
  test_m9_no_proof_cli ();
  test_m7t32_std_flags ();
  test_m9t5_default_keeps_proof ();
  test_d0200_heap_budget_cli ();
  test_m6_t24_interrupt_cli ();
  test_d0216_amo_reuse ();
  test_d0242_alo_reuse ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nend-to-end tests passed"
