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
   Every test module open-coded this search, and every copy looked at
   ~/.local/bin/veripb first -- so a project-wide choice of checker lived in nine
   places and silently meant the Python 2.2.2 (M1-T18). [None] is a FAILURE at every
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
  (* The wrapper has to be in the same format as the line it wraps, or the checker
     rejects the *wrapper* and the test reads that as the trace line failing. Which
     format is whatever the writer that produced [rule_line] used. *)
  let v3 = Writer.default_format () = Writer.V3_0 in
  let t s = if v3 then s ^ " ;" else s in
  run_veripb ~dir ~opb
    (String.concat "\n"
       [
         Printf.sprintf "pseudo-Boolean proof version %s"
           (Writer.format_to_string (Writer.default_format ()));
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
      if ok then Printf.printf "  blanked proof still verified:\n%s\n" blanked);

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
  let v3 = Writer.default_format () = Writer.V3_0 in
  let t s = if v3 then s ^ " ;" else s in
  run_veripb ~dir ~opb
    (String.concat "\n"
       ([
          Printf.sprintf "pseudo-Boolean proof version %s"
            (Writer.format_to_string (Writer.default_format ()));
          t (Printf.sprintf "f %d" n_model);
        ]
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
      if ok then Printf.printf "  blanked proof still verified:\n%s\n" blanked);

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
  if !failures > 0 then (
    Printf.printf "\n%d failure(s)\n" !failures;
    exit 1)
  else print_endline "\ntrace unit tests passed"
