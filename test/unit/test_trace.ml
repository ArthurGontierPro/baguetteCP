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

(* M1-T53: the inner heap guard; see mem_guard.ml for what it cannot see. *)
let () = Mem_guard.install ()
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

(* Which checker to run: lib/proof/checker.ml, shared with scripts/checker.sh.
   Every test module open-coded this search, and every copy resolved it differently --
   so a project-wide choice of checker lived in nine places and could silently mean a
   build nobody intended (M1-T18). [None] is a FAILURE at every
   call site below, never a skip. *)
let veripb_path () = Baguette_proof.Checker.find ()
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

(* What the checker printed on the most recent [run_veripb]. M2-T14: an exit code alone
   cannot tell a JUDGEMENT from a parse error, and a negative control that accepts any
   non-zero exit is green the moment the file stops parsing -- which is exactly how the
   M2-L0 break lane came to pass on `:3:1: Expected number` under format 2.0. Every lane
   below that asserts a rejection also asserts what the rejection SAYS, off this. *)
let last_veripb_log = ref ""

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
      (last_veripb_log := try read_file log with _ -> "");
      Some (rc = 0)

(* ------------------------------------------- reading ids back out of a proof *)

let lines_of s = String.split_on_char '\n' s

let starts_with pre s =
  String.length s >= String.length pre && String.sub s 0 (String.length pre) = pre

let contains needle s =
  let n = String.length needle and m = String.length s in
  let rec go i = i + n <= m && (String.sub s i n = needle || go (i + 1)) in
  n = 0 || go 0

(* M2-T14. A negative control that accepts ANY non-zero exit is green the moment the
   file stops parsing, and a proof that does not parse says nothing whatever about the
   reasoning it contains. That is not hypothetical: the M2-L0 break lane in
   test_justify.ml once passed on `:3:1: Expected number` without the checker ever
   judging a derivation, which is the rule D-0020/D-0030 state outright.

   So every lane here that asserts a rejection also asserts WHAT the rejection says.
   Blanking a trace line into a tautology leaves the nogood underivable, so the rejection
   must be the RUP check, and the checker's wording is matched at FULL strength. The
   fragment "reverse unit propagation" is deliberately not what is matched: it is the
   least specific thing the checker says about this class, and it would equally match a
   RUP failure anywhere else in the proof. Measured 2026-09-18. *)
let rup_rejection_wordings =
  [
    ( "\"not implied by reverse unit propagation (RUP) from core and derived database\"",
      "not implied by reverse unit propagation (RUP) from core and derived database" );
  ]

(* Assert that the last rejection is the one named, not a parse error or a dangling
   label. [what] describes the judgement the lane expects. *)
let check_rejection_is ~tag ~what wordings =
  let out = !last_veripb_log in
  let hit = List.filter (fun (_, needle) -> contains needle out) wordings in
  check
    (Printf.sprintf
       "%s: %s -- the rejection is that JUDGEMENT in the checker's own words, not a \
        parse error"
       tag what)
    (hit <> []);
  if hit = [] then Printf.printf "       checker said: %s\n" (String.trim out)

(* Which rules mint a constraint id, in [Writer]'s own order (writer.ml calls [fresh]
   in exactly these). Everything else -- [#], [w], [del], [*], [output], [conclusion] --
   mints nothing, so walking the file with this counter reproduces the checker's
   numbering and lets a line be matched to the id the solver got back for it. *)
(* A 3.0 rule that yields an id is prefixed with its label, `@c7 rup ... ;` (D-0023),
   so the rule name is not always the start of the line. Splitting the label off keeps
   every predicate below reading one format or the other without knowing which -- and
   without it [mints_id] silently matches nothing under 3.0, which would make the
   blanking control blank NOTHING and then "fail" for a reason that has nothing to do
   with the trace. *)
let label_prefix line =
  if String.length line > 0 && line.[0] = '@' then
    match String.index_opt line ' ' with
    | Some i -> String.sub line 0 (i + 1)
    | None -> ""
  else ""

let strip_label line =
  let n = String.length (label_prefix line) in
  String.sub line n (String.length line - n)

let mints_id line =
  List.exists
    (fun p -> starts_with p (strip_label line))
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
  (* The wrapper is written in the same grammar as the line it wraps -- every rule
     terminated by `;` -- or the checker rejects the *wrapper* and the test reads that as
     the trace line failing. *)
  let t s = s ^ " ;" in
  run_veripb ~dir ~opb
    (String.concat "\n"
       [
         "pseudo-Boolean proof version 3.0";
         t (Printf.sprintf "f %d" n_model);
         rule_line;
         t "output NONE";
         t "conclusion NONE";
         t "end pseudo-Boolean proof";
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
           (* Keep the label: under 3.0 it is the NAME later rules cite, so dropping it
              turns every later citation into a parse error and the control would then
              be green because the proof no longer parses. *)
           if victim !id then label_prefix line ^ taut else line)
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
  (* M1-T31: no ambient row to install, so no thunk to fail. *)
  let ctx = Justify.create ~writer ~encoding in
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
  (* A decision level is `# N` in a 2.0 proof and the comment `% level N` in a 3.0 one,
     which has no set-level rule (D-0024). Checking only for `# N` would make this
     vacuously FALSE under 3.0, so the check would fail rather than silently pass --
     but the neighbouring checks that count on the search having gone deep would then
     be running on an instance nobody had confirmed. Accept either spelling. *)
  check
    (Printf.sprintf "%s: the search reached depth %d" tag m.min_depth)
    (contains (Printf.sprintf "# %d" m.min_depth) proof
    || contains (Printf.sprintf "%% level %d" m.min_depth) proof);
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
      if ok then Printf.printf "  blanked proof still verified:\n%s\n" blanked
      else
        check_rejection_is ~tag
          ~what:
            "with the trace blanked out the nogood is not reachable by unit propagation"
          rup_rejection_wordings);

  List.iter
    (fun f -> try Sys.remove f with _ -> ())
    [ opb; pbp; Filename.concat dir "check.pbp"; Filename.concat dir "check.log" ];
  (try Sys.rmdir dir with _ -> ());
  (proof, n_model)

(* --------------------------------- the hole and the settle (M1-T56, M1-T57) *)

(* Two things this file could not see before, both found by M1-T44 and both about
   [Trace.claims] reading [Store.entry]'s [now]:

   - **M1-T56.** A removal strictly inside the interval moves no bound, and [claims]
     wrote no line for it on the premise that "M1 is bounds-only". [int_ne] has punched
     such holes since M1-T9. The claim is a two-literal clause rather than a literal,
     which is the only reason it was ever thought impossible in the order encoding.

   - **M1-T57.** [Domain.set_lo] settles past holes, so the recorded bound can be
     strictly stronger than the propagator's facts derive (D-0035, I-X9), and the line
     claimed the recorded one from those facts alone.

   The models above cannot reach either: they are [Linear]/[Lin_eq] only, so no hole is
   ever punched. These two come through the FlatZinc front end because the whole point is
   [int_ne] interacting with a bounds propagator, and writing that by hand here would be
   writing the interaction rather than testing it. They are the same sources as
   test/models/trace_settle_sat.fzn and test/models/trace_settle_holes_sat.fzn -- kept
   here as well, not referenced by path, so this binary tests what it says it tests when
   run from anywhere.

   What makes them detectors rather than decoration: both are **satisfiable**, and the
   pre-M1-T57 line is *violated by the model's own solution*. root_hole_unsat.fzn has the
   same defect at the root and verified anyway, because in an UNSAT model every clause is
   entailed and the checker re-derived the missing hole from the .opb's big-M rows on its
   own. That is what made the defect invisible across ~111k runs, and it is why
   [pre_fix_rejected] below is the check that matters most in this section. *)

module F = Baguette_flatzinc

type fzn_case = {
  fzn : string; (* the model's name in test/models/, for the messages *)
  source : string;
  (* The exact bytes of the two lines under test. Quoted from a run, as the [chain]
     byte contract above is, and for the same reason: a shared idea of what a line
     means is worth nothing until someone writes the bytes down. *)
  hole_line : string;
  settle_line : string;
  (* The literal M1-T57 adds to [settle_line]: the fact behind the hole the settle
     walked over. Removing it from the line reconstructs exactly what this module
     emitted before the fix, which must not verify. *)
  settle_hole_fact : string;
  (* How many trace lines are NOT consequences of one model row on their own. A settle's
     line is RUP against the *hole's* line, which is a line this module wrote itself --
     so docs/PROOF-FORMAT.md section 4's "a trace line must verify [standalone]" does not
     hold for it, and this number says so per model rather than leaving the weaker
     property unstated. It is 0 where the checker can still re-derive the single hole
     from the .opb by itself and 1 where two holes in a row put that out of its reach. *)
  needs_prefix : int;
}

let fzn_cases =
  [
    {
      fzn = "trace_settle_sat";
      source =
        {|
var 2..3: y :: output_var;
var 0..4: x :: output_var;
var 0..4: w :: output_var;
var 0..1: z :: output_var;
constraint int_ne(x, y);
constraint int_lin_le([-1,-1],[x,w],-4);
constraint int_lin_le([1,-1],[w,y],0);
constraint int_lin_le([1,-1],[x,z],2);
constraint int_lin_le([1,-1],[z,y],-2);
solve satisfy;
|};
      (* x <> 2, under the decision y = 2. Two claim literals, one negated fact. *)
      hole_line = "rup +1 ~x_ge_2 +1 x_ge_3 +1 y_ge_3 >= 1 ;";
      (* lo(x) asked for 2 and settled to 3. `w_ge_3` is the propagator's own fact
         ("w <= 2") negated; `y_ge_3` is the hole's. *)
      settle_line = "rup +1 x_ge_3 +1 w_ge_3 +1 y_ge_3 >= 1 ;";
      settle_hole_fact = "+1 y_ge_3 ";
      needs_prefix = 0;
    };
    {
      fzn = "trace_settle_holes_sat";
      source =
        {|
var 2..4: y :: output_var;
var 0..5: x :: output_var;
var 0..4: w :: output_var;
var 0..2: z :: output_var;
var 3..3: p :: output_var;
constraint int_ne(x, y);
constraint int_ne(x, p);
constraint int_lin_le([-1,-1],[x,w],-4);
constraint int_lin_le([1,-1],[w,y],0);
constraint int_lin_le([1,-1],[x,z],2);
constraint int_lin_le([1,-1],[z,y],-2);
solve satisfy;
|};
      (* The level-1 hole. The root one, `~x_ge_3 \/ x_ge_4`, has no facts at all
         because p is at both its declared bounds; it is checked by the
         standalone/prefix sweep below rather than quoted twice. *)
      hole_line = "rup +1 ~x_ge_2 +1 x_ge_3 +1 y_ge_3 >= 1 ;";
      (* Settled over BOTH holes, 2 and 3, so lo(x) landed on 4. The hole at 3
         contributed no fact, which is why only one literal is added here. *)
      settle_line = "rup +1 x_ge_4 +1 w_ge_3 +1 y_ge_3 >= 1 ;";
      settle_hole_fact = "+1 y_ge_3 ";
      needs_prefix = 1;
    };
  ]

(* Like [standalone], but with [prefix] (trace lines, in file order, labels stripped)
   stated first. That is the honest form of the D-0018 property once a settle exists: a
   trace line is RUP against the model rows *and the trace lines this module already
   wrote*, and nothing else -- no decision, no nogood, no conflict line.

   Labels are stripped from every line including the one under test, because a subset of
   a proof's rules carries a subset of its auto-numbered [@cN] names and re-stating
   `@c20` as the checker's own `@c19` is a duplicate-name parse error, which would make
   this whole check fail for a reason that has nothing to do with the trace. Nothing
   here cites anything by name, so the names are not needed. *)
let standalone_after ~dir ~opb ~n_model ~prefix rule_line =
  let t s = s ^ " ;" in
  run_veripb ~dir ~opb
    (String.concat "\n"
       ([ "pseudo-Boolean proof version 3.0"; t (Printf.sprintf "f %d" n_model) ]
       @ List.map strip_label prefix
       @ [
           strip_label rule_line;
           t "output NONE";
           t "conclusion NONE";
           t "end pseudo-Boolean proof";
           "";
         ]))

let run_fzn c =
  let tag = c.fzn in
  let dir = Filename.temp_file "baguette_trace_fzn" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "model.opb" in
  let pbp = Filename.concat dir "model.pbp" in
  let m = F.Builder.of_string ~file:tag c.source in
  let comp = F.Compile.compile m in
  let store = comp.F.Compile.store in
  let encoding = comp.F.Compile.encoding in
  let engine = comp.F.Compile.engine in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ tag ] encoding oc;
  close_out oc;
  let n_model = Encoding.n_constraints encoding in
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = Justify.create ~writer ~encoding in
  let trace = Trace.create () in
  (* I-S1 the same way bin/main.ml does it: the model re-checks the assignment, the
     propagators are not trusted. [Compile] builds the store in [Model.vars] order, which
     is the promise that makes this index-for-index. *)
  let independent (a : Search.assignment) =
    let values = Array.make (F.Model.nvars m) 0 in
    List.iter (fun (v, value) -> values.(Var.to_int v) <- value) a;
    F.Model.check_assignment m values
  in
  let outcome = Search.solve ~engine ~store ~ctx ~check:independent ~trace () in
  close_out oc;
  let proof = read_file pbp in
  let rules = numbered_rules ~n_model proof in
  let trace_ids = Trace.emitted_ids trace in
  let is_trace id = List.mem id trace_ids in

  (match outcome with
  | Search.Sat a ->
      check
        (tag ^ ": the solution independently satisfies the model (I-S1)")
        (independent a)
  | Search.Unsat ->
      incr failures;
      Printf.printf
        "FAIL %s: answered UNSATISFIABLE, but this model is satisfiable -- the checks \
         below would then all be about the wrong instance\n"
        tag);
  check (tag ^ ": a branch failed, so a trace was written") (List.length trace_ids > 0);

  (* ---- I-S4, on a real run. Both models settle over a hole, so both must record at
     least one citation: a settle line resting on the hole line M1-T56 wrote. A zero here
     would make the verdict below vacuous, which is the one way this gate could pass
     forever while I-S4 was false, so it is asserted first and separately. *)
  let cites = Trace.citations trace in
  check
    (Printf.sprintf "%s: I-S4 -- a settle line cites a hole line (%d edge(s))" tag
       (List.length cites))
    (cites <> []);
  check
    (tag ^ ": I-S4 -- every edge names two lines this module wrote")
    (List.for_all
       (fun (c : Trace.citation) -> is_trace c.Trace.citing && is_trace c.Trace.cited)
       cites);
  let viol = Trace.i_s4_violations trace in
  check
    (tag ^ ": I-S4 -- every cited hole line is live and no deeper than its citer")
    (viol = []);
  List.iter (fun m -> Printf.printf "     %s\n" m) viol;

  (* ---- M1-T56 and M1-T57, as bytes. The hole's line did not exist before M1-T56;
     the settle's line existed without its last literal and was false. *)
  check
    (tag ^ ": M1-T56 -- the interior hole gets its own line, " ^ c.hole_line)
    (contains c.hole_line proof);
  check
    (tag ^ ": M1-T57 -- the settled bound cites the hole's reason, " ^ c.settle_line)
    (contains c.settle_line proof);

  (* ---- the whole proof. This is the check the two models exist for: before M1-T57
     VeriPB 3.0.2 refused the settle line outright. *)
  (match run_veripb ~dir ~opb proof with
  | None ->
      incr failures;
      Printf.printf
        "FAIL %s: veripb not found -- I-X1 was NOT checked. Do not read this as a pass.\n"
        tag
  | Some ok ->
      check (tag ^ ": veripb accepts the proof (I-X1)") ok;
      if not ok then Printf.printf "  model:\n%s\n  proof:\n%s\n" (read_file opb) proof);

  (* ---- every trace line, against the .opb plus the trace lines before it. That is
     the D-0018 property in the form that survives a settle: a settle's line is RUP
     against the *hole's* line, which this module wrote itself, so "one model row" is
     too narrow for it while "the whole proof" would be too wide to mean anything. No
     decision, no nogood and no conflict line is ever in the prefix.

     The mirror half is deliberately NOT the same question. A nogood *must* be RUP once
     the trace is in the database -- that is the entire claim of D-0018 -- so it is
     checked against the .opb ALONE, where it must fail. Asking it against the trace as
     well would assert the opposite of the design and would have this section reporting
     a defect every time the module worked. *)
  let bad_trace = ref [] and bad_nogood = ref [] in
  let prefix = ref [] in
  List.iter
    (fun (id, line) ->
      if is_trace id then (
        (match standalone_after ~dir ~opb ~n_model ~prefix:(List.rev !prefix) line with
        | None -> ()
        | Some ok -> if not ok then bad_trace := (id, line) :: !bad_trace);
        prefix := line :: !prefix)
      else
        match standalone ~dir ~opb ~n_model line with
        | None -> ()
        | Some ok -> if ok then bad_nogood := (id, line) :: !bad_nogood)
    rules;
  check
    (Printf.sprintf "%s: all %d trace lines verify against the .opb and the trace so far"
       tag (List.length trace_ids))
    (!bad_trace = []);
  List.iter
    (fun (id, line) ->
      Printf.printf "  not valid even with the trace before it: %d  %s\n" id line)
    !bad_trace;
  check
    (tag ^ ": no non-trace rule is RUP from the .opb alone -- the trace is load-bearing")
    (!bad_nogood = []);
  List.iter
    (fun (id, line) -> Printf.printf "  unexpectedly standalone-valid: %d  %s\n" id line)
    !bad_nogood;

  (* ---- and how many of those lines are NOT consequences of one model row on their
     own. PROOF-FORMAT section 4 says a trace line must verify standalone; a settle's
     line rests on the hole's line and does not, and this counts them rather than
     leaving the deviation unrecorded. The count is per model and asserted exactly:
     drifting either way is a change in what the trace rests on. *)
  let not_standalone =
    List.filter
      (fun (id, line) ->
        is_trace id
        &&
        match standalone ~dir ~opb ~n_model line with Some ok -> not ok | None -> false)
      rules
  in
  check
    (Printf.sprintf "%s: exactly %d trace line(s) need an earlier trace line (got %d)" tag
       c.needs_prefix (List.length not_standalone))
    (List.length not_standalone = c.needs_prefix);

  (* ---- the detector. Take the settle line as emitted, delete the hole fact M1-T57
     added, and the result must be refused even with the whole trace in front of it: it
     is the pre-fix line, and it is false in a model that has a solution. The removal is
     asserted to have changed something first -- a no-op edit would make this check pass
     by testing the correct line twice. *)
  let pre_fix =
    let n = String.length c.settle_hole_fact in
    let rec go i =
      if i + n > String.length c.settle_line then c.settle_line
      else if String.sub c.settle_line i n = c.settle_hole_fact then
        String.sub c.settle_line 0 i
        ^ String.sub c.settle_line (i + n) (String.length c.settle_line - i - n)
      else go (i + 1)
    in
    go 0
  in
  check
    (tag ^ ": the pre-M1-T57 line is a different line from the one emitted")
    (not (String.equal pre_fix c.settle_line));
  (match standalone_after ~dir ~opb ~n_model ~prefix:(List.rev !prefix) pre_fix with
  | None -> ()
  | Some ok ->
      check
        (tag ^ ": without the hole's fact the settle line is REFUSED, " ^ pre_fix)
        (not ok));

  (* ---- the negative control: blank every trace line into a tautology and the proof
     must fail. Without this, everything above could be measuring a decorative trace. *)
  let taut = "rup +1 x_ge_1 +1 ~x_ge_1 >= 1 ;" in
  let blanked = blank_rules ~n_model ~victim:is_trace ~taut proof in
  (match run_veripb ~dir ~opb blanked with
  | None -> ()
  | Some ok ->
      check (tag ^ ": with the trace blanked out, veripb rejects the proof") (not ok);
      if ok then Printf.printf "  blanked proof still verified:\n%s\n" blanked
      else
        check_rejection_is ~tag
          ~what:
            "with the trace blanked out the nogood is not reachable by unit propagation"
          rup_rejection_wordings);

  List.iter
    (fun f -> try Sys.remove f with _ -> ())
    [ opb; pbp; Filename.concat dir "check.pbp"; Filename.concat dir "check.log" ];
  try Sys.rmdir dir with _ -> ()

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
  (* Substring, not whole-line: a 3.0 rule carries a `@cN ` label in front of it. *)
  let pos_if f =
    let best = ref (-1) in
    List.iteri (fun i l -> if !best < 0 && f l then best := i) ls;
    !best
  in
  let pos needle = pos_if (fun l -> contains needle l) in
  let p_trace = pos "rup +1 ~c_ge_3 +1 b_ge_2 >= 1 ;" in
  let p_conflict = pos "rup +1 a_ge_1 +1 b_ge_2 +1 c_ge_3 >= 1 ;" in
  let p_nogood = pos "rup +1 a_ge_1 >= 1 ;" in
  (* The backtrack. `w 1` in 2.0; in 3.0 there is no wipe rule and the backtrack is the
     explicit deletion the writer emits in its place (D-0024). Either way it is the
     first retiring line in the file, and D-0018 point 4 is that nothing is retired
     before the nogood is written -- which is the property under test here and is
     unchanged by the format. *)
  let p_wipe =
    pos_if (fun l ->
        let l = String.trim l in
        l = "w 1" || (String.length l >= 4 && String.sub l 0 4 = "del "))
  in
  check "chain bytes: trace, then conflict line, then nogood, then the backtrack"
    (p_trace >= 0 && p_trace < p_conflict && p_conflict < p_nogood && p_nogood < p_wipe)

(* ================================================================= I-X10's gate =====

   M1-T61. I-X10 says every trace line is RUP against the .opb plus the lines already on
   the page, and that this holds because **every M1 pruning follows from a single model
   constraint** whose rows unit-propagate the claim once the line's own facts are assumed.
   That is a property of the propagator set that happens to exist, not of the encoding,
   and it went unstated for a whole milestone.

   The two checks below are deliberately different in kind, because the property has two
   ways of failing and only one of them is about proof text.

   The trap this file's other lanes cannot cover: they exercise the propagators that
   EXIST. That is exactly why nobody noticed the property -- a suite that only ever runs
   Linear and Ne cannot report that Linear and Ne are special. So (a) watches the set
   itself for new arrivals, and (b) watches the checker's verdict on a pruning shape no
   current propagator emits.

   D-0040 has the measurements and the consequence for M4. *)

let rec find_up dir marker depth =
  if depth <= 0 then None
  else if Sys.file_exists (Filename.concat dir marker) then Some dir
  else
    let parent = Filename.dirname dir in
    if String.equal parent dir then None else find_up parent marker (depth - 1)

(* Same cwd-relative walk the model suites use (test_flatzinc.ml, test_output.ml), so
   `dune runtest --root .` from a worktree finds the tree. An out-of-tree --build-dir
   cannot, which CLAUDE.md already says not to use. *)
let repo_root =
  let marker = Filename.concat "lib" (Filename.concat "core" "propagator.ml") in
  match find_up (Sys.getcwd ()) marker 12 with
  | Some d -> Some d
  | None -> find_up (Filename.dirname Sys.executable_name) marker 12

(* How a propagator family discharges I-X10.

   [Single_row]      its pruning follows from ONE model constraint, whose rows
                     unit-propagate the claim given the line's own facts. The trace line
                     is then RUP with no help, and I-X10 holds for it.
   [Needs_derivation] it counts several constraints, or rests on a structure the .opb does
                     not carry. It MUST emit an explicit pol/ia deriving its pruning
                     before its trace line (D-0027 permits the cutting planes; D-0040
                     records that this is all `all_different` needs), or force the direct
                     encoding (D-0019 point 3). No such propagator exists yet.
   [Prunes_nothing]  not a pruner, so I-X10 has nothing to say about it. *)
type ix10_class = Single_row | Needs_derivation | Prunes_nothing

let ix10_table =
  [
    ("linear.ml", Single_row);
    ("lin_eq.ml", Single_row);
    ("ne.ml", Single_row);
    ("int_le.ml", Single_row);
    ("int_lt.ml", Single_row);
    ("int_eq.ml", Single_row);
    ("bool2int.ml", Single_row);
    (* M2-L12/D-0052: bool_clause.ml, widened to general order literals and renamed. The
       classification is UNCHANGED and that is the point of re-reading it here: a clause
       over order literals is still one constraint whose rows unit-propagate the claim,
       whether that constraint is a model row the front end posted or a learned one
       [Learned.introduce] put on the page. What the widening DID add is a lifetime
       condition -- a learned constraint is on the page only while lib/core/retention.ml
       holds it -- and that is I-X3's business, guarded by [Retention.cite], not
       I-X10's. *)
    ("clause.ml", Single_row);
    (* M2-L13/D-0054: the slack propagator for a learned PB row, of which clause.ml is
       now the degree-1 face. Single_row, and the classification is worth spelling out
       because it is the first one where a SECOND kind of .opb row takes part.

       The pruning follows from ONE constraint -- the learned row, put on the page by
       [Pb_analysis.introduce] with its [pol] derivation behind it -- and the trace line
       is RUP against it with no explicit derivation emitted ahead. What the checker's
       own unit propagation also uses is the ORDER-ENCODING LADDER rows of the variable
       being pruned, because lib/core/prop/pb.ml folds the ladder into a rung's effective
       coefficient. Those are not a second constraint in I-X10's sense: they are the
       .opb's encoding of the variable itself (D-0028, docs/PROOF-FORMAT.md section 3),
       written before the first decision and retired by nothing, and the same standing
       lib/core/ladder.ml's lift relies on. So there is nothing to derive and nothing to
       order, which is what Single_row means.

       The LIFETIME condition of clause.ml's note applies here too and more strongly: a
       learned PB row is on the page only while lib/core/retention.ml holds it.
       [Search.register_learned_pb] cites it. That is I-X3's business, not I-X10's. *)
    ("pb.ml", Single_row);
    (* Not a propagator: it renders bound-fact chains for a reason another propagator
       already justified, so it introduces no pruning of its own. *)
    ("order_reason.ml", Prunes_nothing);
    (* M3-T4: the reification dispatcher. It owns no propagation -- it reads the
       reifier and calls one of three author-supplied pieces, each of which is an
       ordinary propagator that changes domains under its own justification. There is
       no pruning here for I-X10 to have an opinion about; the two authors below are
       where the question is answered. *)
    ("reif.ml", Prunes_nothing);
    (* M3-T2: b <-> (sum a x <= c). Single_row, and for the plainest possible reason:
       every pruning is [Linear]'s, over ONE of the two big-M rows
       [Encoding.add_int_lin_le_reif_rows] posts for the reified constraint, and the
       trace line is RUP against that row with the line's own facts -- the reifier's
       fact included, which is what makes the big-M term vanish. That includes the
       prunings OF the reifier: dis-entailment is FWD's own bound push on FWD's own
       reifier term, and entailment is BWD's. No second constraint takes part, and
       nothing is derived ahead of the line. *)
    ("reif_lin_le.ml", Single_row);
    (* M3-T2: b <-> (sum a x = c), and int_ne_reif, its inverted literal. Single_row in
       exactly the sense [ne.ml] is: one model constraint, several rows. The equality
       side prunes from the guarded LE or GE row; the disequality side and the
       entailment push are nogoods that are RUP against the guarded A/B pair -- which is
       [Encoding.expand_int_lin_ne]'s own pair with a guard term, i.e. the same
       "one constraint, two rows over an .opb-only auxiliary" standing [ne.ml] has had
       since M1-T9. Nothing here counts two constraints and nothing emits a derivation
       ahead of its trace line. *)
    ("reif_lin_eq.ml", Single_row);
    (* M4-T4b: int_times, int_div, int_abs. Single_row, in exactly reif_lin_le.ml's sense:
       every pruning is [Linear]'s over ONE of the guarded rows lib/flatzinc/compile.ml
       posts for the constraint, and the trace line is RUP against that row with the line's
       own facts -- the guard Booleans' facts included, which is what makes the big-M term
       vanish. No second constraint takes part and nothing is derived ahead of the line. *)
    ("arith.ml", Single_row);
    (* M4-T3: array_int_element. Single_row on the Ne precedent -- "one model constraint"
       is a rule about the CONSTRAINT, not the row count. array_int_element is one
       constraint posted as 2n rows, the way int_lin_ne is one posted as two big-M rows
       whose selector the checker's own unit propagation fills in. Negate an index
       pruning: one row plus the result's ladder refutes it. Negate a result pruning:
       each disagreeing position is excluded by its own row and the index's ladder has
       nothing left. MEASURED for the result side -- it has no direct encoding, so
       Trace.derive_ahead never fires for it, and all seven element models plus a scene
       built to defeat it verify with nothing written ahead of their lines (I-S4/D-0039:
       RUP against the .opb plus EARLIER TRACE LINES, not a second model constraint). *)
    ("element.ml", Single_row);
    (* M4-T1: all_different_int. THE FIRST [Needs_derivation] FAMILY, and the one the
       classification above was written in anticipation of.

       A Hall-interval pruning counts: it rests on one at-least-one line per Hall
       variable and one at-most-one line per Hall value, recovered from the pairwise
       disequality rows lib/proof/encoding.ml's [add_all_different] posts. Its trace line
       is therefore NOT RUP against the .opb alone -- D-0040 measured 3.0.2 refusing
       exactly that shape, and [test_ix10_derive_ahead] below re-measures it on this
       propagator's own output rather than on a hand-written analogue.

       What discharges I-X10 for it is lib/core/trace.ml's [derive_ahead]: the
       cutting-planes derivation goes on the page immediately before the line, so the
       line is RUP in sequence. D-0040's sentence, implemented. *)
    ("alldiff.ml", Needs_derivation);
  ]

(* (a) CLOSURE. OCaml cannot reflect over its own modules, so the only way to notice a
   new propagator family is to read the directory. Adding lib/core/prop/all_different.ml
   reddens this until someone classifies it -- which is the "visible event" I-X10 exists
   to create. Without this check, I-X10 is a sentence rather than a gate. *)
let test_ix10_closure () =
  match repo_root with
  | None ->
      check "I-X10 closure: the repository root was found" false;
      ()
  | Some root ->
      let dir =
        Filename.concat root (Filename.concat "lib" (Filename.concat "core" "prop"))
      in
      let on_disk =
        Sys.readdir dir |> Array.to_list
        |> List.filter (fun f -> Filename.check_suffix f ".ml")
        |> List.sort compare
      in
      check "I-X10 closure: lib/core/prop/ was read and is not empty" (on_disk <> []);
      let classified = List.map fst ix10_table in
      let unclassified = List.filter (fun f -> not (List.mem f classified)) on_disk in
      let stale = List.filter (fun f -> not (List.mem f on_disk)) classified in
      if unclassified <> [] then
        Printf.printf
          "     unclassified against I-X10: %s\n\
          \     -- a new propagator family arrived. Decide whether its pruning follows\n\
          \     from ONE model constraint (Single_row) or needs an explicit pol/ia ahead\n\
          \     of its trace line (Needs_derivation). See docs/INVARIANTS.md I-X10 and\n\
          \     docs/DECISIONS.md D-0040.\n"
          (String.concat ", " unclassified);
      if stale <> [] then
        Printf.printf "     classified but gone from disk: %s\n"
          (String.concat ", " stale);
      check "I-X10 closure: every module in lib/core/prop/ is classified"
        (unclassified = []);
      check "I-X10 closure: no classification names a module that no longer exists"
        (stale = []);
      (* A table that classified nothing would pass the two checks above vacuously. *)
      check "I-X10 closure: at least one family is classified Single_row"
        (List.exists (fun (_, c) -> c = Single_row) ix10_table);
      (* THE DEBT THIS GATE USED TO RECORD, PAID (M4-T1).

         Until alldiff.ml arrived, [Needs_derivation] had no members and this check said
         so: "no family needs an explicit derivation yet -- when one does, this gate is
         too weak and must be strengthened", with the note that whoever turned it red
         owed the stronger check. It went red on M4-T1, exactly as written, and the
         stronger check is [test_ix10_derive_ahead] below -- which takes a real
         [Needs_derivation] pruning, asserts its trace line is REFUSED standalone (so the
         obligation is real) and asserts a [pol] precedes it in the proof the solver
         actually wrote (so the obligation is met).

         What stays here is the closure half, restated so that it cannot pass vacuously
         in either direction: a family classified [Needs_derivation] must be one the
         content check below actually exercises. Today that is exactly `alldiff.ml`, and
         a second such family reddens this until [test_ix10_derive_ahead] grows a scene
         for it -- which is the same "visible event" the closure check exists to create,
         one level up. *)
      let needs =
        List.map fst (List.filter (fun (_, c) -> c = Needs_derivation) ix10_table)
      in
      if needs <> [ "alldiff.ml" ] then
        Printf.printf
          "     Needs_derivation is now %s. test_ix10_derive_ahead below drives\n\
          \     `alldiff.ml` and nothing else, so any other family here is classified\n\
          \     but UNCHECKED: give it a scene there. See D-0040.\n"
          (String.concat ", " needs);
      check "I-X10 closure: every Needs_derivation family is one the content check drives"
        (needs = [ "alldiff.ml" ])

(* (b) CONTENT. The closure check is a name list; on its own it would pass forever even
   if I-X10 were false. This asserts the checker's actual verdict on the shape a
   Needs_derivation propagator would emit.

   The scene: x, y, w in 2..4 saturate {2,3,4}, so z in 2..5 is forced to 5. That is a
   Hall interval, and `z >= 5` is exactly what a bounds-consistent all_different (M4-T1)
   would prune. It is ENTAILED -- restricting z to 2..4 makes the model UNSAT -- and the
   checker still will not take it on a bare rup, because it rests on three disequalities
   at once rather than on one.

   Two things about the scene are load-bearing:

   * It MUST be satisfiable. In an UNSAT model every clause is entailed and a rup either
     succeeds or fails on the checker's luck at unit-propagating a contradiction, which
     measures nothing about our proof. That is not hypothetical: it is precisely how
     M1-T57's false trace line survived ~111k fuzzer runs on root_hole_unsat.
   * Widths are 3 and 4 (D-0028: the order encoding is width-proportional).

   The accept-side control is not decoration. A "must be refused" assertion is the single
   most likely thing in this file to pass forever for the wrong reason -- a typo'd literal
   name, a malformed wrapper, a free variable -- and every one of those refuses too. The
   control is a line on the SAME .opb that must be ACCEPTED, so the pair shows the
   wrapper works and the refusal is about the claim. *)
let hall_source =
  {|
var 2..4: x :: output_var;
var 2..4: y :: output_var;
var 2..4: w :: output_var;
var 2..5: z :: output_var;
constraint int_ne(x, y);
constraint int_ne(x, w);
constraint int_ne(x, z);
constraint int_ne(y, w);
constraint int_ne(y, z);
constraint int_ne(w, z);
solve satisfy;
|}

let test_ix10_content () =
  let dir = Filename.temp_file "baguette_ix10" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "hall.opb" in
  let m = F.Builder.of_string ~file:"hall_sat" hall_source in
  let comp = F.Compile.compile m in
  let encoding = comp.F.Compile.encoding in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "hall_sat" ] encoding oc;
  close_out oc;
  let n_model = Encoding.n_constraints encoding in
  (* The Hall bound move itself: what M4-T1 would prune, and what I-X10 predicts the
     checker refuses on a bare rup. *)
  let hall_move = "rup +1 z_ge_5 >= 1 ;" in
  (* An int_ne line on the same .opb: one model constraint, so I-X10 predicts accepted. *)
  let single_row = "rup +1 ~z_ge_4 +1 z_ge_5 +1 ~x_ge_4 >= 1 ;" in
  (match standalone ~dir ~opb ~n_model single_row with
  | Some true ->
      check "I-X10 content: the accept-side control verifies (wrapper is sound)" true
  | Some false ->
      check
        "I-X10 content: the accept-side control verifies (wrapper is sound) -- it was \
         REFUSED, so the refusal below proves nothing"
        false
  | None ->
      (* scripts/checker.sh's no-skipping rule: a missing checker is a failure, never a
         quiet pass. *)
      check
        "I-X10 content: veripb is available (a missing checker is a FAILURE, not a skip)"
        false);
  (match standalone ~dir ~opb ~n_model hall_move with
  | Some false ->
      check
        "I-X10 content: a Hall bound move (M4-T1's shape) is REFUSED standalone, so a \
         multi-constraint pruner must derive it"
        true
  | Some true ->
      Printf.printf
        "     `%s` VERIFIED against hall.opb. I-X10 says a pruning resting on three\n\
        \     disequalities at once is not RUP from the model alone, so either the\n\
        \     encoding changed or I-X10 is false. See docs/DECISIONS.md D-0040.\n"
        hall_move;
      check "I-X10 content: a Hall bound move (M4-T1's shape) is REFUSED standalone" false
  | None -> check "I-X10 content: veripb is available for the refusal lane" false);
  (try Sys.remove opb with Sys_error _ -> ());
  try Sys.rmdir dir with Sys_error _ -> ()

(* (c) THE OBLIGATION ITSELF, on a [Needs_derivation] family's own output (M4-T1).

   The closure check above can see a family arrive; it cannot see whether the family
   does what the classification commits it to. D-0040's sentence is "emit that derivation
   as explicit `pol` lines *ahead of* its trace line, so the line is RUP in sequence",
   and this drives the real solver over a real model and asserts both halves of it:

     REFUSED   the Hall pruning's own trace line, stated alone against this model's .opb,
               is refused -- so there is an obligation, and it is this pruning's, not a
               hand-written analogue of it ([test_ix10_content] above is the analogue,
               and it is kept because it measures the shape on a satisfiable scene).
     ORDERED   in the proof the solver actually wrote, a `pol` precedes that line.
     ACCEPTED  and the whole proof verifies, which is what the two halves are for.

   The model is test/models/alldiff_hall_trace_unsat.fzn, inline here for the reason
   every scene in this file is inline: a test that reads the model directory tests
   whatever is in the model directory.

   x, y <= 2 makes {x, y} a Hall set for [1, 2] and pushes z and w up to 3..4; the
   `z + w <= 5` row then refutes that, so the pruning LANDS and is on the trail when
   [Trace.emit] runs. A Hall pruning that is never followed by a conflict writes no line
   at all and would test nothing here. *)
let ix10_hall_source =
  {|var 1..4: x;
var 1..4: y;
var 1..4: z;
var 1..4: w;
constraint int_le(x, 2);
constraint int_le(y, 2);
constraint all_different_int([x, y, z, w]);
constraint int_lin_le([1,1],[z,w],5);
solve satisfy;
|}

(* The line the Hall pruning of z writes: its claim, disjoined with the negation of the
   two bound facts it read. Pinned verbatim rather than searched for, so that a change
   in what Alldiff records as its reason reddens here instead of silently retargeting
   the check at some other line. *)
let ix10_hall_line = "rup +1 z_ge_3 +1 x_ge_3 +1 y_ge_3 >= 1 ;"

let test_ix10_derive_ahead () =
  let dir = Filename.temp_file "baguette_ix10_ahead" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "ahead.opb" in
  let pbp = Filename.concat dir "ahead.pbp" in
  let m = F.Builder.of_string ~file:"ix10_hall" ix10_hall_source in
  let comp = F.Compile.compile m in
  let encoding = comp.F.Compile.encoding in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "ix10_hall" ] encoding oc;
  close_out oc;
  let n_model = Encoding.n_constraints encoding in
  let oc = open_out pbp in
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = Justify.create ~writer ~encoding in
  let independent (a : Search.assignment) =
    let values = Array.make (F.Model.nvars m) 0 in
    List.iter (fun (v, value) -> values.(Var.to_int v) <- value) a;
    F.Model.check_assignment m values
  in
  let outcome =
    Search.solve ~engine:comp.F.Compile.engine ~store:comp.F.Compile.store ~ctx
      ~check:independent ()
  in
  close_out oc;
  check "I-X10 ahead: the scene is UNSAT, so the Hall pruning's line is written"
    (outcome = Search.Unsat);
  let proof = read_file pbp in
  let ls = List.map strip_label (lines_of proof) in
  let index_of want =
    let rec go i = function
      | [] -> None
      | l :: rest -> if String.equal l want then Some i else go (i + 1) rest
    in
    go 0 ls
  in
  (match index_of ix10_hall_line with
  | None ->
      Printf.printf "     the Hall trace line `%s` is not in the proof at all\n"
        ix10_hall_line;
      check "I-X10 ahead: the Hall pruning wrote its trace line" false
  | Some i ->
      check "I-X10 ahead: the Hall pruning wrote its trace line" true;
      let pol_before =
        List.exists
          (fun (j, l) -> j < i && starts_with "pol " l)
          (List.mapi (fun j l -> (j, l)) ls)
      in
      check
        "I-X10 ahead: a pol precedes the Hall trace line (D-0040's ordering, emitted by \
         Trace.derive_ahead)"
        pol_before);
  (* THE BREAK, and it is the same line: stated alone against this model's .opb, with no
     derivation ahead of it, the checker must refuse it -- and refuse it on the JUDGEMENT
     rather than on the grammar, which is what the wording below distinguishes. An exit
     status cannot tell the two apart (M2-T14). *)
  (match standalone ~dir ~opb ~n_model ix10_hall_line with
  | Some false ->
      check
        "I-X10 ahead BREAK: the same line standalone is REFUSED, and on the checker's \
         own judgement"
        (contains
           "not implied by reverse unit propagation (RUP) from core and derived database"
           !last_veripb_log);
      if
        not
          (contains
             "not implied by reverse unit propagation (RUP) from core and derived \
              database"
             !last_veripb_log)
      then Printf.printf "     veripb said: %s\n" !last_veripb_log
  | Some true ->
      Printf.printf
        "     `%s` VERIFIED standalone against this .opb, so alldiff.ml has no I-X10\n\
        \     obligation on this scene and the ordering check above proves nothing.\n"
        ix10_hall_line;
      check "I-X10 ahead BREAK: the same line standalone is REFUSED" false
  | None ->
      check "I-X10 ahead: veripb is available (a missing checker is a FAILURE)" false);
  (* And the whole proof, which is the point of the ordering: with the derivation on the
     page the line the break just saw refused verifies. *)
  (match run_veripb ~dir ~opb proof with
  | Some true -> check "I-X10 ahead: the full proof verifies (I-X1)" true
  | Some false ->
      Printf.printf "     veripb said: %s\n" !last_veripb_log;
      check "I-X10 ahead: the full proof verifies (I-X1)" false
  | None -> check "I-X10 ahead: veripb is available for the accept lane" false);
  List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) [ opb; pbp ];
  try Sys.rmdir dir with Sys_error _ -> ()

(* ================================================================== I-S4's gate =====

   I-S4 says a trace line that cites a hole is supported only while that hole's own line
   is live, so **the cited line must outlive the citing line**. D-0039 point 1 records
   that this holds "by the level discipline, but that is an argument, not a check", and
   that the argument does not cover M2-T3's learned clauses. This section is the check.

   [Trace] now records one edge per hole line a settle line rests on, with the two facts
   I-S4 is about measured at the moment of the citation. [run_fzn] above asserts the
   verdict on two real runs and asserts that the edge count is not zero. What it cannot
   do is show that the verdict can come back non-empty: every model in the tree satisfies
   I-S4, so a check that only ever ran on them would pass identically if it were wired to
   [fun _ -> []]. This project's signature failure is a check that cannot see its own
   subject fail, and it has never been found by reading. So the break is performed.

   The scene is the smallest one with the shape I-S4 is about, and it is hand-driven
   rather than searched precisely so that the two [Trace.emit] calls can be pulled apart
   and a deletion slipped between them -- which is what M2-T3 will do by accident:

     x in 0..5, with 2 and 3 removed (two adjacent holes, the shape D-0039 measured as
     out of the checker's own unit-propagation reach), and then lo(x) pushed to 2, which
     [Domain.settle] walks past both holes to 4.

   Two lanes on that one scene:

     CONTROL  emit the hole lines, then the settle line. Two edges, no violation. This is
              not decoration: a "must report a violation" assertion is the single most
              likely thing here to pass for the wrong reason -- a mis-built scene, a
              settle that never happened, an entry the trail never got -- and every one
              of those reports a violation too. The control is the same scene with the
              break left out, and it must come back clean.
     BREAK    delete the hole-at-2 line *before* the settle line is written. The settle
              then rests on a line the proof no longer contains, [i_s4_violations] must
              name it, and veripb must refuse the result.

   The *level* half of I-S4 has no reachable instance today -- [emit] files a line at the
   level of the trail entry that produced it and a settle only ever walks over holes at
   levels at or below its own, which is I-S4's argument restated -- so it is checked
   against the edge M2-T3 will create, through [Trace.i_s4_verdict] on one constructed
   edge. When a learned clause cites across levels, that branch is already under test. *)

module Reason = Baguette_core.Reason
module Explanation = Baguette_core.Explanation

let is4_source =
  {|
var 0..5: x :: output_var;
var 3..3: p :: output_var;
var 2..2: q :: output_var;
constraint int_ne(x, p);
constraint int_ne(x, q);
constraint int_lin_le([-1],[x],-2);
solve satisfy;
|}

let var_by_name store name =
  let rec go i =
    if i >= Store.n_vars store then None
    else
      let v = Var.of_int i in
      if String.equal (Store.name store v) name then Some v else go (i + 1)
  in
  go 0

(* Nothing here is a propagator, so nothing here has a derivation: [Reason.none] with the
   empty clause is the honest pair (reason.ml's [none] -- "this change rests on no facts
   at all" -- written out and seen, which is the whole of what I-P4 buys). It is also the
   pair [Store.apply]'s D-0026 agreement check passes trivially, so this scene behaves
   the same under BAGUETTE_DEBUG=1, where the I-S4 check itself is live. What the lines
   claim is still true of the model: x <> 3, x <> 2 and x >= 4 are all entailed by it. *)
let factless = Reason.because ~concludes:None Reason.none (Explanation.clause [])

(* [retire] is how many of the two hole lines to delete between the two emits, newest
   first: 0 is the control, 1 breaks I-S4 for one edge, 2 breaks it for both. Measured
   separately because the *checker* needs both gone before it refuses -- one remaining
   hole line is enough of a hint for it to unit-propagate the other from `int_ne`'s big-M
   rows, which is the same "the checker re-derives the hole unaided" phenomenon that hid
   M1-T57 for ~111k runs (I-X9, D-0039). With neither line the settle line is refused,
   measured: `rup +1 x_ge_4 >= 1 ;` alone against this .opb is "not implied by reverse
   unit propagation". So I-S4 is observable through the checker on this scene, and the
   report says at which dose. *)
let is4_scene ~retire =
  let dir = Filename.temp_file "baguette_is4" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  let opb = Filename.concat dir "model.opb" in
  let pbp = Filename.concat dir "model.pbp" in
  let m = F.Builder.of_string ~file:"is4" is4_source in
  let comp = F.Compile.compile m in
  let store = comp.F.Compile.store in
  let encoding = comp.F.Compile.encoding in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "is4" ] encoding oc;
  close_out oc;
  let oc = open_out pbp in
  (* audit:true because [Writer.is_live] is only maintained under it, and the liveness
     half of I-S4 is what this scene is about. [Writer.conclusion] is deliberately never
     called: the I-X2 audit fires there and this proof is not meant to conclude anything,
     only to have each of its rules checked under `conclusion NONE`. *)
  let writer = Writer.create ~audit:true oc in
  Encoding.start_proof encoding writer;
  let ctx = Justify.create ~writer ~encoding in
  let trace = Trace.create () in
  let x = Option.get (var_by_name store "x") in
  let removed v = Store.remove store x v factless = Store.Changed in
  let ok_holes = removed 3 && removed 2 in
  (* The hole lines. *)
  Trace.emit ctx trace store;
  let hole_ids = Trace.emitted_ids trace in
  (* Emission order is trail order: the line for the hole at 3 first, then the one for
     the hole at 2. Retire from the newest, so [retire = 1] is the hole at 2. *)
  List.iter
    (fun id -> Writer.delete writer id)
    (List.filteri (fun i _ -> i < retire) (List.rev hole_ids));
  (* The settle: asked for 2, lands on 4, having walked over both holes. *)
  let settled =
    Store.set_lo store x 2 factless = Store.Changed && Domain.lo (Store.get store x) = 4
  in
  (* Under BAGUETTE_DEBUG the break makes [Trace]'s own I-S4 check raise at the citation,
     which is the check firing in its loudest form. Catch it so the lane can also report
     the verdict and the checker's opinion. *)
  let raised =
    try
      Trace.emit ctx trace store;
      None
    with Failure msg -> Some msg
  in
  close_out oc;
  let proof = read_file pbp in
  let t s = s ^ " ;" in
  let full =
    String.concat "\n"
      (lines_of (String.trim proof)
      @ [ t "output NONE"; t "conclusion NONE"; t "end pseudo-Boolean proof"; "" ])
  in
  let verdict = run_veripb ~dir ~opb full in
  let result =
    ( ok_holes,
      settled,
      List.length hole_ids,
      Trace.citations trace,
      Trace.i_s4_violations trace,
      raised,
      verdict )
  in
  List.iter (fun f -> try Sys.remove f with _ -> ()) [ opb; pbp ];
  (try Sys.rmdir dir with _ -> ());
  result

let test_is4_gate () =
  (* ---- the control: the scene, unbroken. *)
  let holes, settled, n_hole_lines, cites, viol, raised, verdict = is4_scene ~retire:0 in
  check "I-S4 control: both holes were punched" holes;
  check "I-S4 control: the settle walked past both holes onto 4" settled;
  check "I-S4 control: each hole got its own line (M1-T56)" (n_hole_lines = 2);
  check
    (Printf.sprintf "I-S4 control: the settle line cites both hole lines (%d edge(s))"
       (List.length cites))
    (List.length cites = 2);
  check "I-S4 control: no violation, so the scene itself satisfies I-S4" (viol = []);
  check "I-S4 control: Trace's own check did not raise" (raised = None);
  (match verdict with
  | Some true -> check "I-S4 control: veripb accepts the unbroken scene" true
  | Some false ->
      check
        "I-S4 control: veripb accepts the unbroken scene -- it did NOT, so the refusal \
         in the break lane below proves nothing"
        false
  | None ->
      check
        "I-S4 control: veripb is available (a missing checker is a FAILURE, not a skip)"
        false);

  (* ---- the break: retire the cited line first. *)
  let holes, settled, n_hole_lines, cites, viol, raised, verdict = is4_scene ~retire:1 in
  check "I-S4 break: the scene is the same one (holes punched)" holes;
  check "I-S4 break: the scene is the same one (settle onto 4)" settled;
  check "I-S4 break: the scene is the same one (two hole lines)" (n_hole_lines = 2);
  (* THE assertion this whole section exists for. *)
  check
    (Printf.sprintf
       "I-S4 break: retiring a cited hole line before its citer is REPORTED (%d \
        violation(s))"
       (List.length viol))
    (viol <> []);
  List.iter (fun m -> Printf.printf "     reported: %s\n" m) viol;
  (* The two configurations are genuinely different runs and both are asserted, rather
     than one of them being papered over. With BAGUETTE_DEBUG=1 [Trace]'s own check
     raises at the *first* violating citation, so the run stops there and the remaining
     edges are never recorded -- being loud is the point of that lane. With it off the
     whole settle line is written and the verdict is asked for afterwards, which is the
     lane that reports one violation out of two edges. *)
  if Baguette_core.Debug.enabled then (
    check "I-S4 break: with BAGUETTE_DEBUG=1, Trace raises at the citation"
      (raised <> None);
    check "I-S4 break: and it raised on the first violating edge, not later"
      (List.length cites = 1 && List.length viol = 1))
  else (
    check "I-S4 break: with the check as a verdict, Trace does not raise" (raised = None);
    check
      (Printf.sprintf "I-S4 break: the same two edges are recorded (%d)"
         (List.length cites))
      (List.length cites = 2);
    check "I-S4 break: exactly one of the two edges broke -- the retired one, not both"
      (List.length viol = 1));
  (* One retired line is not yet enough to make the *checker* refuse: the surviving hole
     line lets it unit-propagate the other hole out of `int_ne`'s big-M rows unaided,
     which is I-X9's phenomenon and the reason M1-T57's false line survived ~111k runs.
     Asserted rather than left as a remark, because the dose at which the checker starts
     noticing is the quantity that says how much I-S4 is load-bearing. *)
  (match verdict with
  | Some ok ->
      check
        "I-S4 break: one retired line still verifies -- the checker re-derives the other \
         hole unaided (I-X9), so I-S4 cannot be left to it"
        ok
  | None -> check "I-S4 break: veripb is available for the refusal lane" false);

  (* ---- the same break at the dose the checker does notice: retire BOTH hole lines and
     the settle line is no longer reachable. Measured: `rup +1 x_ge_4 >= 1 ;` against this
     .opb alone is refused outright. This is the lane that makes the whole section a
     measurement of I-S4 rather than of a bookkeeping field. *)
  let holes, settled, _, cites, viol, _, verdict = is4_scene ~retire:2 in
  check "I-S4 double break: the scene is the same one" (holes && settled);
  check
    (Printf.sprintf "I-S4 double break: every recorded edge is reported (%d of %d)"
       (List.length viol) (List.length cites))
    (List.length viol = List.length cites
    && List.length viol = if Baguette_core.Debug.enabled then 1 else 2);
  (match verdict with
  | Some false ->
      check
        "I-S4 double break: veripb REFUSES the proof -- the settle line really does rest \
         on the hole lines"
        true
  | Some true ->
      Printf.printf
        "     with BOTH hole lines retired the settle line still verified. Measured\n\
        \     otherwise when this was written (`rup +1 x_ge_4 >= 1 ;` alone against\n\
        \     this .opb is refused), so either the encoding changed or the scene no\n\
        \     longer settles. See docs/DECISIONS.md D-0039 and I-S4.\n";
      check "I-S4 double break: veripb REFUSES the proof" false
  | None -> check "I-S4 double break: veripb is available for the refusal lane" false);

  (* ---- the level half: no instance today, so the edge M2-T3 will build, by hand.
     [emit] files a line at its trail entry's level and a settle only walks over holes at
     levels at or below its own, which is the whole of I-S4's argument -- so this branch
     of the verdict has no reachable scene until a learned clause cites across levels.
     Checking it on a constructed edge is what stops it being dead code on that day. *)
  let cross : Trace.citation =
    {
      Trace.citing = 41;
      cited = 42;
      citing_level = 1;
      cited_level = 2;
      cited_live = true;
      live_known = true;
      hole = 7;
    }
  in
  (match Trace.i_s4_verdict cross with
  | Some m ->
      check "I-S4 level half: an edge citing a deeper line is REPORTED" true;
      Printf.printf "     reported: %s\n" m
  | None ->
      check
        "I-S4 level half: an edge citing a deeper line is REPORTED -- it was not, so \
         M2-T3's cross-level citation would pass unnoticed"
        false);
  check "I-S4 level half: the same edge the other way round is clean"
    (Trace.i_s4_verdict { cross with Trace.cited_level = 1 } = None)

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
  List.iter run_fzn fzn_cases;
  test_ix10_closure ();
  test_ix10_content ();
  test_ix10_derive_ahead ();
  test_is4_gate ();
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ntrace unit tests passed"
