(* M1-T13 / docs/DECISIONS.md D-0018: the branch's propagation trace, and the nogood
   that is plain RUP over it.

   ---------------------------------------------------------------------------
   Why this file exists at all, and what would make it worthless
   ---------------------------------------------------------------------------

   D-0018's last consequence, taken from the Glasgow Constraint Solver's own framework
   notes: *a RUP line asserting the fact one cares about tests nothing*. Only a
   backtracking justification, checked after the decisions have been asserted,
   discriminates. A root-level UNSAT model cannot catch a regression here, because a
   root refutation never asserts a decision and so never exercises the replay that this
   whole mechanism exists to make possible. So every model below **branches, propagates
   to a failure, backtracks**, and its proof is handed to veripb -- never as an xfail.

   And every model is deliberately one step past the smallest thing that exercises the
   feature. This project has had five findings that were invisible on the instance
   chosen to test the thing they broke (D-0009, D-0010, D-0012, D-0017, D-0018), and the
   shape is always the same: the failing case needed one more step than the test
   instance had. What "one more step" means here, concretely:

   - [chain] is the smallest useful shape (one decision, whose first child fails, whose
     second child succeeds), and it is here as the *byte-level* contract -- the exact
     text a branch emits -- not as the regression net. It is test/models/chain_sat.fzn,
     the model D-0017 found and M1-T13 exists to fix, rebuilt so this file does not
     depend on a path the orchestrator owns.
   - [even_sum] drives the search three levels deep and refutes the whole tree, so the
     trace spans several levels at once. A level-1 line has to survive the [w] that
     retires level 2 and still be there when level 1's second branch is explored, which
     is the difference between tagging each line with the level of the trail entry that
     produced it and tagging everything with whatever level the writer is on. A
     one-level model cannot tell those two apart; this one can.
   - [reused_slots] is the same trick on wider domains: five levels, and at every one of
     them the first branch is refuted and the second is then entered *at the same trail
     positions*. A watermark that trusted a length rather than the entries themselves
     would think those prunings had already been written down, skip them, and the
     nogood would be rejected. Seeing that needs a failure on the second branch of a
     level, not just the first.
   - [offset] has domains that neither start at zero nor stay positive, and
     coefficients other than 1, so the order-encoding expansion's constant is non-zero
     and a bound fact is several literals from its declared bound (the D-0010 shape).
   - [sat_after_failures] succeeds, but only after failing first: the SAT path has to
     retire the level-0 trace lines it wrote on the way, which no [w] covers, or the
     I-X2 audit fires at [conclusion].

   ---------------------------------------------------------------------------
   The three checks that actually discriminate
   ---------------------------------------------------------------------------

   1. **veripb accepts the whole proof.** Necessary, and on its own the weakest of the
      three: a proof can be accepted because its steps are trivially valid rather than
      because they say anything (that is exactly how D-0009 shipped).

   2. **Every trace line verifies on its own, against the .opb and nothing else.** Each
      one is extracted from the emitted proof and re-checked as a one-rule proof
      (`f N`, the line, `conclusion NONE`). This is the D-0018 contract stated in a form
      that cannot be satisfied by accident: a trace line claims "these bound facts imply
      this bound", which is a consequence of one model row, so it must check with an
      empty database. The nogoods must NOT -- they are true only under the decisions --
      and that is asserted too, in the same loop. A change that quietly folded a
      decision into a trace line would pass check 1 and fail this one.

   3. **Blanking the trace makes veripb reject.** The trace lines of the [chain] proof
      are replaced by a tautology of the same shape -- which keeps every constraint id
      exactly where it was, so nothing downstream shifts -- and the checker must then
      refuse the nogood. Without this, "the proof verifies" would not distinguish
      "because of the trace" from "despite it". *)

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
module Trace = Baguette_core.Trace

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

(* ------------------------------------------------------------------- models *)

type cstr = Le of (int * int) list * int | Eq of (int * int) list * int

type model = {
  title : string;
  vars : (string * int * int) array; (* name, lo, hi *)
  cstrs : cstr list;
  min_depth : int; (* how deep the search must actually go *)
}

let models =
  [
    {
      (* test/models/chain_sat.fzn, rebuilt here: the model M1-T13 exists to fix. One
         decision (indomain_min tries a = 0), that branch fails, the second succeeds.
         The unique solution is a = 1, b = 2, c = 3. *)
      title = "chain: a+b+c=6, b=a+1, c=b+1 over [0,9]";
      vars = [| ("a", 0, 9); ("b", 0, 9); ("c", 0, 9) |];
      cstrs =
        [
          Eq ([ (1, 0); (1, 1); (1, 2) ], 6);
          Eq ([ (1, 1); (-1, 0) ], 1);
          Eq ([ (1, 2); (-1, 1) ], 1);
        ];
      min_depth = 1;
    };
    {
      (* Even left-hand side, odd right-hand side: UNSAT by parity, which bounds
         reasoning cannot see at the root, so the search has to branch and keep
         branching -- three nested levels, each refuted on both sides, chaining the
         nogoods back to the empty clause at level 0. *)
      title = "even_sum: 2x1+2x2+2x3 = 9 over [0,3]^3";
      vars = [| ("x1", 0, 3); ("x2", 0, 3); ("x3", 0, 3) |];
      cstrs = [ Eq ([ (2, 0); (2, 1); (2, 2) ], 9) ];
      min_depth = 3;
    };
    {
      (* Wider domains on the same parity trick: five levels, and at each one the first
         branch is refuted, the second is entered at the *same* trail positions, and it
         is refuted too -- the case a length-only watermark gets wrong. *)
      title = "reused_slots: 2x1+2x2+2x3 = 11 over [0,5]^3";
      vars = [| ("x1", 0, 5); ("x2", 0, 5); ("x3", 0, 5) |];
      cstrs = [ Eq ([ (2, 0); (2, 1); (2, 2) ], 11) ];
      min_depth = 5;
    };
    {
      (* Offset and negative domains, coefficients other than +-1: the expansion's
         constant is non-zero and every bound fact is several order literals from its
         declared bound (D-0010). Still UNSAT by parity, still needs to branch. *)
      title = "offset: 2x1-2x2+4x3 = 7, domains offset and negative";
      vars = [| ("x1", -2, 3); ("x2", 1, 5); ("x3", -3, 2) |];
      cstrs = [ Eq ([ (2, 0); (-2, 1); (4, 2) ], 7) ];
      min_depth = 1;
    };
    {
      (* A satisfiable model whose search fails before it succeeds: the SAT path has to
         retire the trace it wrote on the way (I-X2) rather than leave level-0 lines
         live at [conclusion], which [~audit:true] below turns into an exception. *)
      title = "sat_after_failures: x1+x2+x3=7, x2=x1+2, x3 <= x2, over [0,4]";
      vars = [| ("x1", 0, 4); ("x2", 0, 4); ("x3", 0, 4) |];
      cstrs =
        [
          Eq ([ (1, 0); (1, 1); (1, 2) ], 7);
          Eq ([ (1, 1); (-1, 0) ], 2);
          Le ([ (1, 2); (-1, 1) ], 0);
        ];
      min_depth = 2;
    };
  ]

(* ------------------------------------------------------- the independent oracle *)

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

let independent_check m (assignment : Search.assignment) =
  let n = Array.length m.vars in
  let assign = Array.make n 0 in
  List.iter (fun (v, value) -> assign.(Var.to_int v) <- value) assignment;
  let in_box = ref true in
  Array.iteri
    (fun i (_, lo, hi) -> if assign.(i) < lo || assign.(i) > hi then in_box := false)
    m.vars;
  !in_box && evaluate m.cstrs assign

(* --------------------------------------------------------------- the harness *)

let pack ~id (lin : Linear.t) =
  Propagator.pack ~id (module Linear : Propagator.S with type t = Linear.t) lin

let build_store m =
  Store.create
    ~names:(Array.map (fun (n, _, _) -> n) m.vars)
    ~domains:(Array.map (fun (_, lo, hi) -> Domain.make lo hi) m.vars)

(* An equality is two rows and two instances, each justifying against its own row
   (D-0011). An .opb line with `=` would count as two constraints for the `f` rule and
   shift every id, so the two halves are posted as separate `>=` rows. *)
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

(* ------------------------------------------------------------------- veripb *)

let veripb_path () =
  let p = Filename.concat (Sys.getenv "HOME") ".local/bin/veripb" in
  if Sys.file_exists p then Some p
  else if Sys.command "command -v veripb >/dev/null 2>&1" = 0 then Some "veripb"
  else None

let veripb = veripb_path ()

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let write_file path s =
  let oc = open_out_bin path in
  output_string oc s;
  close_out oc

(* [Some true] accepted, [Some false] rejected, [None] veripb is missing. *)
let run_veripb ~dir ~opb proof_text =
  match veripb with
  | None -> None
  | Some exe ->
      let pbp = Filename.concat dir "check.pbp" in
      let log = Filename.concat dir "check.log" in
      write_file pbp proof_text;
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote exe) (Filename.quote opb)
             (Filename.quote pbp) (Filename.quote log))
      in
      Some (rc = 0)

(* ------------------------------------------- reading ids back out of a proof *)

let lines_of s = String.split_on_char '\n' s

let starts_with pre s =
  String.length s >= String.length pre && String.sub s 0 (String.length pre) = pre

let contains needle s =
  let n = String.length needle and m = String.length s in
  let rec go i = i + n <= m && (String.sub s i n = needle || go (i + 1)) in
  n = 0 || go 0

(* Which rules mint a constraint id, in [Writer]'s own order (writer.ml calls [fresh]
   in exactly these). Everything else -- [#], [w], [del], [*], [output], [conclusion] --
   mints nothing, so walking the file with this counter reproduces the checker's
   numbering and lets a line be matched to the id the solver got back for it. *)
let mints_id line =
  List.exists
    (fun p -> starts_with p line)
    [ "pol "; "rup "; "red "; "solx "; "soli "; "obju " ]

(* Every rule line of the proof, as (id, text). *)
let numbered_rules ~n_model proof =
  let id = ref n_model in
  List.filter_map
    (fun line ->
      if mints_id line then (
        incr id;
        Some (!id, line))
      else None)
    (lines_of proof)

(* ------------------------------------------------- checking one line in isolation *)

(* A one-rule proof: load the model, state this constraint, conclude nothing. VeriPB
   accepts `conclusion NONE` and reports "VERIFIED NO CONCLUSION", which is exactly the
   question being asked -- is this line derivable from the model alone? -- with no
   search, no decisions and no other derived constraint in the database. *)
let standalone ~dir ~opb ~n_model rule_line =
  run_veripb ~dir ~opb
    (String.concat "\n"
       [
         "pseudo-Boolean proof version 2.0";
         Printf.sprintf "f %d" n_model;
         rule_line;
         "output NONE";
         "conclusion NONE";
         "end pseudo-Boolean proof";
         "";
       ])

(* ------------------------------------------- blanking the trace, keeping the ids *)

(* Replace [victims] (a predicate on the id a rule line was given) with a tautology over
   an existing variable. The replacement still mints an id, so every later [pol], [del]
   and [conclusion] reference stays correct and the checker's complaint, when it comes,
   is about the nogood rather than about a dangling id. *)
let blank_rules ~n_model ~victim ~taut proof =
  let id = ref n_model in
  String.concat "\n"
    (List.map
       (fun line ->
         if mints_id line then (
           incr id;
           if victim !id then taut else line)
         else line)
       (lines_of proof))

(* ---------------------------------------------------------------- one model *)

let run_model m =
  let tag = m.title in
  let expected = brute_force m in
  let expect_sat = expected <> None in
  let dir = Filename.temp_file "baguette_trace" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "model.opb" in
  let pbp = Filename.concat dir "model.pbp" in
  let store = build_store m in
  let encoding, ids = build_encoding m in
  let engine = build_engine m store ids in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ tag ] encoding oc;
  close_out oc;
  let n_model = Encoding.n_constraints encoding in
  let oc = open_out pbp in
  (* audit:true puts invariant I-X2 under test. The level-0 trace lines are the one
     class of rule no [w] retires, so if [Search.solve] stopped deleting them
     [Writer.conclusion] would raise here rather than quietly shipping the leak. *)
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx =
    Justify.create ~writer ~encoding ~model_id:(fun () ->
        failwith "test_trace: search demanded Explanation.Trivial (D-0011)")
  in
  let trace = Trace.create () in
  let entry_level = Store.level store in
  let outcome = Search.solve ~engine ~store ~ctx ~check:(independent_check m) ~trace () in
  close_out oc;
  let exit_level = Store.level store in
  let proof = read_file pbp in
  let rules = numbered_rules ~n_model proof in
  let trace_ids = Trace.emitted_ids trace in
  let is_trace id = List.mem id trace_ids in

  (* ---- the answer, from brute force, never hand-written *)
  (match outcome with
  | Search.Sat assignment ->
      check (tag ^ ": agrees with brute force (SAT)") expect_sat;
      check
        (tag ^ ": the solution independently satisfies the model (I-S1)")
        (independent_check m assignment)
  | Search.Unsat -> check (tag ^ ": agrees with brute force (UNSAT)") (not expect_sat));
  check (tag ^ ": decision level restored on return (I-S3)") (entry_level = exit_level);

  (* ---- the search went as deep as this model is here to make it go, and a branch
     really failed: no trace line means nothing below tests anything. *)
  check
    (Printf.sprintf "%s: the search reached depth %d" tag m.min_depth)
    (contains (Printf.sprintf "# %d" m.min_depth) proof);
  check (tag ^ ": a branch failed, so a trace was written") (List.length trace_ids > 0);

  (* ---- ordering (D-0018 point 4): no [w] appears before the last trace line, i.e.
     every line the nogood propagates along is still in the database when it is
     checked. Stated over the text because that is what the checker reads. *)
  let idx_of_last_trace =
    let id = ref n_model and best = ref (-1) in
    List.iteri
      (fun i line ->
        if mints_id line then (
          incr id;
          if is_trace !id then best := i))
      (lines_of proof);
    !best
  in
  let idx_of_first_wipe =
    let best = ref max_int in
    List.iteri
      (fun i line -> if starts_with "w " line && !best = max_int then best := i)
      (lines_of proof);
    !best
  in
  check
    (tag ^ ": D-0018.4 -- nothing is wiped before the trace is written")
    (idx_of_last_trace < idx_of_first_wipe);

  (* ---- the whole proof, for real. Never an xfail: this is the check M1-T13 exists
     to turn green, and a model here that cannot pass it is a bug, not a marker. *)
  (match run_veripb ~dir ~opb proof with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- I-X1 was NOT checked. Do not read this as a pass.\n"
        tag
  | Some ok ->
      check (tag ^ ": veripb accepts the branch proof (I-X1)") ok;
      if not ok then Printf.printf "  model:\n%s\n  proof:\n%s\n" (read_file opb) proof);

  (* ---- the discriminating check: each trace line on its own, against the .opb and
     nothing else. A trace line MUST verify that way (it is a consequence of one model
     row, with no decision in it); a nogood MUST NOT (it is true only under the
     decisions, which is why it needs the trace to be RUP at all). *)
  let bad_trace = ref [] and bad_nogood = ref [] in
  List.iter
    (fun (id, line) ->
      match standalone ~dir ~opb ~n_model line with
      | None -> ()
      | Some ok ->
          if is_trace id then (if not ok then bad_trace := (id, line) :: !bad_trace)
          else if ok then bad_nogood := (id, line) :: !bad_nogood)
    rules;
  check
    (Printf.sprintf "%s: all %d trace lines verify standalone against the .opb" tag
       (List.length trace_ids))
    (!bad_trace = []);
  List.iter
    (fun (id, line) -> Printf.printf "  not standalone-valid: id %d  %s\n" id line)
    !bad_trace;
  (* The mirror half of that check is only meaningful on a *satisfiable* model. In an
     UNSAT one the model rows are jointly contradictory, so every clause whatsoever is
     entailed by them and whether veripb happens to reach one by unit propagation
     measures the checker's luck, not our proof. On a satisfiable model a nogood is a
     real restriction on the solution set that only the decisions justify, and it must
     not check standalone -- if it did, the trace above would not be what makes it
     reachable and this file would be testing nothing. *)
  if expect_sat then (
    check
      (tag ^ ": every nogood needs the trace -- none is standalone-RUP")
      (!bad_nogood = []);
    List.iter
      (fun (id, line) ->
        Printf.printf "  unexpectedly standalone-valid nogood: id %d  %s\n" id line)
      !bad_nogood);

  (* ---- and the negative control: blank every trace line into a tautology, keeping
     all the ids, and the checker must refuse. If this passes, the trace is decoration
     and every check above was measuring something else. *)
  let name0, lo0, _ = m.vars.(0) in
  let taut =
    Printf.sprintf "rup +1 %s_ge_%d +1 ~%s_ge_%d >= 1 ;" name0 (lo0 + 1) name0 (lo0 + 1)
  in
  let blanked = blank_rules ~n_model ~victim:is_trace ~taut proof in
  (match run_veripb ~dir ~opb blanked with
  | None -> ()
  | Some ok ->
      check (tag ^ ": with the trace blanked out, veripb rejects the proof") (not ok);
      if ok then Printf.printf "  blanked proof still verified:\n%s\n" blanked);

  List.iter
    (fun f -> try Sys.remove f with _ -> ())
    [ opb; pbp; Filename.concat dir "check.pbp"; Filename.concat dir "check.log" ];
  (try Sys.rmdir dir with _ -> ());
  (proof, n_model)

(* ------------------------------------------------ the byte-level contract *)

(* D-0009's lesson, applied: a shared idea of what a line *means* is worth nothing
   unless someone writes down the bytes. These are the exact lines the [chain] model's
   failing branch emits -- the claim literal, the negated reason literals, the nogood --
   quoted from a run rather than reconstructed. If the shape of a trace line changes,
   this is where it is noticed, and a deliberate change to it belongs in
   docs/PROOF-FORMAT.md before it belongs here. *)
let byte_contract proof =
  let expect what line =
    check (Printf.sprintf "chain bytes: %s -- %s" what line) (contains line proof)
  in
  (* Root prunings: b >= 1 from b - a = 1 with a at its declared lo (no literal for a
     declared bound, so the clause is a unit), then c >= 2 given b >= 1. *)
  expect "a root pruning, no facts to negate" "rup +1 b_ge_1 >= 1 ;";
  expect "a root pruning with one fact" "rup +1 c_ge_2 +1 ~b_ge_1 >= 1 ;";
  (* Under the decision a <= 0: b <= 1 because a <= 0, then c <= 2 because b <= 1.
     The decision literal appears *negated into the tail*, never as a claim. *)
  expect "a pruning under the decision" "rup +1 ~b_ge_2 +1 a_ge_1 >= 1 ;";
  expect "the pruning that follows it" "rup +1 ~c_ge_3 +1 b_ge_2 >= 1 ;";
  (* The conflict's own reason line (D-0018 point 3), then the nogood. *)
  expect "the conflict's reason line" "rup +1 a_ge_1 +1 b_ge_2 +1 c_ge_3 >= 1 ;";
  expect "the nogood over the negated decision" "rup +1 a_ge_1 >= 1 ;";
  (* Order: the whole trace, then the conflict line, then the nogood, then the wipe. *)
  let ls = lines_of proof in
  let pos needle =
    let best = ref (-1) in
    List.iteri (fun i l -> if !best < 0 && l = needle then best := i) ls;
    !best
  in
  let p_trace = pos "rup +1 ~c_ge_3 +1 b_ge_2 >= 1 ;" in
  let p_conflict = pos "rup +1 a_ge_1 +1 b_ge_2 +1 c_ge_3 >= 1 ;" in
  let p_nogood = pos "rup +1 a_ge_1 >= 1 ;" in
  let p_wipe = pos "w 1" in
  check "chain bytes: trace, then conflict line, then nogood, then the wipe"
    (p_trace >= 0 && p_trace < p_conflict && p_conflict < p_nogood && p_nogood < p_wipe)

let () =
  print_endline "";
  (match veripb with
  | None ->
      print_endline
        "  (veripb is not on PATH and not at ~/.local/bin/veripb -- every I-X1 check \
         below will FAIL, which is the intended behaviour: see docs/INVARIANTS.md.)"
  | Some _ -> ());
  let chain_proof = ref "" in
  List.iteri
    (fun i m ->
      let proof, _ = run_model m in
      if i = 0 then chain_proof := proof)
    models;
  byte_contract !chain_proof;
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ntrace unit tests passed"
