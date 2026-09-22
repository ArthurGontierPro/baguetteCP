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
      (* ------------------------------------- the `pol`-minted citation, opt_unsat's shape

         An infeasible optimisation model concludes BOUNDS INF INF citing a `pol`, which
         is exactly the shape the decorative-`pol` warning is about. It is NOT decorative:
         the conclusion checks that the cited constraint really is a contradiction. *)
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
          check "M5: the INF conclusion's cited id was minted by a `pol`"
            (List.find_map
               (fun l ->
                 match m5_minted l with Some (i, r) when i = id -> Some r | _ -> None)
               lines2
            = Some "pol");
          (* BREAK 3: corrupt that `pol` so it derives something sound but NOT a
             contradiction, leaving the claim unchanged. If the conclusion did not check
             its citation this would sail through, which is the whole worry. *)
          let corrupted =
            List.map
              (fun l ->
                match m5_minted l with
                | Some (i, "pol") when i = id -> (
                    (* `pol @cA @cB +` -> `pol @cA @cA +`: still a valid derivation, no
                       longer a contradiction. *)
                    match String.split_on_char ' ' (String.trim l) with
                    | lbl :: "pol" :: a :: _ :: rest ->
                        String.concat " " (lbl :: "pol" :: a :: a :: rest)
                    | _ -> l)
                | _ -> l)
              lines2
          in
          check "M5 BREAK CONTROL: the corruption really changed the pol"
            (corrupted <> lines2);
          let ok, out = m5_run_lines checker dir "polbad" opb2 corrupted in
          check
            "M5 BREAK: a `pol` that derives something sound but not contradictory is \
             REFUSED by the conclusion -- BOUNDS checks the id it cites"
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

(* Drop the last operand of a reverse-Polish [pol], which leaves a pol that is still
   SOUND -- it derives something the database really entails -- but no longer
   contradictory. That is precisely D-0057's failure mode, so it is the break worth
   making: a proof that goes on being accepted after it is exactly a proof whose pol was
   decorative. *)
(* M4-T8: a summand may be scaled ("@cN k *") rather than added bare ("@cN"), which
   [Defining]'s multiplicity introduces and the older Clause-only lines this helper was
   first written against never did. Dropping only the id and the immediately-following
   token left a dangling "k *" for a scaled summand -- a syntax error, not the "sound
   but not contradictory" pol this break wants -- so the coefficient, if present, is
   consumed too. *)
let el_drop_last_operand line =
  let ws = Array.of_list (String.split_on_char ' ' (String.trim line)) in
  let n = Array.length ws in
  let is_id w = String.length w > 2 && String.sub w 0 2 = "@c" in
  let idx_last_op =
    let best = ref (-1) in
    for i = 2 to n - 1 do
      if is_id ws.(i) then best := i
    done;
    !best
  in
  if idx_last_op < 0 then None
  else
    let j = ref (idx_last_op + 1) in
    if
      !j + 1 < n
      && (match int_of_string_opt ws.(!j) with Some _ -> true | None -> false)
      && ws.(!j + 1) = "*"
    then j := !j + 2;
    if !j >= n then None
    else
      let last_dropped = !j in
      Some
        (String.concat " "
           (List.filteri
              (fun i _ -> i < idx_last_op || i > last_dropped)
              (Array.to_list ws)))

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
      (match minting with
      | None -> check "M4-T3 (c): the conclusion names a line THIS proof minted" false
      | Some line ->
          check "M4-T3 (c): the conclusion names a line THIS proof minted" true;
          if not (m5_says (" " ^ String.trim line) " pol ") then
            Printf.printf "     conclusion cites: %s\n" (String.trim line);
          check
            "M4-T3 (c): `conclusion UNSAT` cites the ELEMENT DERIVATION -- a pol, not \
             the empty clause a D-0022 close would put there"
            (m5_says (" " ^ String.trim line) " pol "));
      (* --------------------------------- (b) the break, on the very line it cites *)
      (match minting with
      | None -> ()
      | Some line -> (
          let ok, _ = m5_run_lines checker dir "elok" opb lines in
          check "M4-T3 BREAK CONTROL: the unmodified proof is accepted" ok;
          match el_drop_last_operand line with
          | None ->
              check
                "M4-T3 BREAK: the cited pol has operands to drop (a one-operand pol \
                 would make this lane vacuous)"
                false
          | Some broken ->
              let lines2 = List.map (fun l -> if l = line then broken else l) lines in
              check "M4-T3 BREAK CONTROL: the corruption really changed the file"
                (lines2 <> lines);
              let ok, out = m5_run_lines checker dir "elbad" opb lines2 in
              check
                "M4-T3 BREAK (b): a cited pol that is SOUND but no longer contradictory \
                 is REFUSED"
                (not ok);
              check
                "M4-T3 BREAK (b): ... at full strength -- the checker's own wording, not \
                 an exit status and not a parse error"
                (m5_says out "is not contradicting, as specified by the hint.")));
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
          if not (m5_says (" " ^ String.trim line) " pol ") then
            Printf.printf "     conclusion cites: %s\n" (String.trim line);
          check
            "M4-T8 (c): with the bound MOVED, `conclusion UNSAT` now cites element.ml's \
             OWN pol (Route A) -- D-0064's Defining cancels it exactly, where the old \
             Clause stand-in could not, and element.ml's [pol] is no longer decorative \
             for this scene"
            (m5_says (" " ^ String.trim line) " pol ");
          check
            "M4-T8 (c): ... and it is NOT `rup >= 1` -- the empty-clause Route B this \
             scene used to take before the swap"
            (not (m5_says (String.trim line) "rup >= 1")));
      (* ------------------------- M4-T8 obligation (b): the break, on this cited line

         Same recipe as the positive half's BREAK above: drop the pol's last operand,
         which leaves it SOUND but no longer contradictory, and check that `conclusion
         UNSAT` -- which now names this line -- is refused, at the checker's full
         wording rather than an exit status. *)
      (match minting with
      | None -> ()
      | Some line -> (
          let ok, _ = m5_run_lines checker dir "elmovedok" opb lines in
          check "M4-T8 BREAK CONTROL: the unmodified moved-bound proof is accepted" ok;
          match el_drop_last_operand line with
          | None ->
              check
                "M4-T8 BREAK: the cited pol has operands to drop (a one-operand pol \
                 would make this lane vacuous)"
                false
          | Some broken ->
              let lines2 = List.map (fun l -> if l = line then broken else l) lines in
              check "M4-T8 BREAK CONTROL: the corruption really changed the file"
                (lines2 <> lines);
              let ok, out = m5_run_lines checker dir "elmovedbad" opb lines2 in
              check
                "M4-T8 BREAK (b): a cited pol that is SOUND but no longer contradictory \
                 is REFUSED"
                (not ok);
              check
                "M4-T8 BREAK (b): ... at full strength -- the checker's own wording, not \
                 an exit status and not a parse error"
                (m5_says out "is not contradicting, as specified by the hint.")));
      List.iter
        (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
        (Array.to_list (Sys.readdir dir));
      try Sys.rmdir dir with _ -> ())

let () =
  print_endline "";
  List.iter run_model models;
  test_proof_comments_noop ();
  test_m5_branch_and_bound ();
  test_m5_derivation_is_load_bearing ();
  test_element_derivation_is_load_bearing ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\nend-to-end tests passed"
