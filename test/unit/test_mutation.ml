(* M1-T15: the proof-mutation gate. Corrupt one emitted step, and assert that veripb
   REJECTS it.

   Why this exists, verbatim from the Glasgow Constraint Solver's own harness
   (`run_test_and_expect_verify_failure.bash`), which `scripts/mutate_proof.sh` is
   modelled on:

     A propagator whose derivation has slack in it writes proofs that verify even when
     one step is deliberately corrupted -- so "veripb accepts" on its own says little
     about whether the honest derivation is load-bearing. A test binary run under this
     harness emits a knowingly wrong proof, and the run passes only if veripb says no.
     If veripb accepts, the honest derivation was slack, and that is a finding about the
     propagator, not about the harness.

   Five findings in this project so far were invisible on the instance chosen to test
   the thing they broke (D-0018's closing paragraph counts them), and the recurring
   shape is a derivation that verifies for the wrong reason. Every `ok` line below says
   that one specific step of one specific derivation is load-bearing -- a different
   claim from anything test_proof.ml, test_justify.ml or test_endtoend.ml make, all of
   which only ever ask veripb to say yes.

   Three traps decide which instance each lane runs on. They are GCS's, learned the
   expensive way, and they are why this file builds its own instances rather than
   pointing at whatever proof happens to be lying around:

   1. Mutate on an instance whose margin is ONE. Corrupt a proof of a conflict that had
      three units of slack and the contradiction survives anyway; the lane is then green
      for the wrong reason. [triple_unsat] below closes at `0 >= 1` and is the instance
      the `pol` lanes gate on. [lin_unsat] closes at `0 >= 2` and is registered as
      known-slack for exactly this reason -- see [known_slack] and the comment there.

   1b. AND ON AN INSTANCE THAT NEEDS ITS DERIVATION AT ALL (M1-T38, from D-0030). A
      margin of one in the derivation does not help if a single MODEL ROW is already
      infeasible: the model is then refuted by that row and everything above it is
      decoration, which is what [root_unsat] turned out to be. Trap 1 is a property of
      the `pol`; this is a property of the .opb, and the two are independent.
      [rows_that_refute_alone] puts the question to the checker -- a derivation-free
      proof per model row, each of which must be REJECTED -- and it is run on
      [triple_unsat] before its lanes, and on [root_unsat], which it must still catch.
   2. A mutation that only removes energy from a `pol` is usually not a test: a `pol`
      only has to get *close enough* that unit propagation finishes the job, so slack
      rows still close the proof. Hence `pol-coeff` perturbs a coefficient rather than
      deleting a summand, and hence `pol-cite` (a different live id, so a different
      constraint entirely) and `drop-line` (no step at all) run alongside it.
   3. Mutating a *reason* is only a corruption when the dropped literal traces back to a
      SEARCH DECISION (GCS `dev_docs/constraints.md:1085`). Anything a propagator derived
      is in the proof as a clause in its own right, so the checker has it whether or not
      the reason repeats it: a rule that fired during root propagation has a reason that
      merely restates the database, and dropping from it changes nothing veripb can see.
      Such a lane goes green on an empty corruption. So `rup-drop-lit` and `rhs-const`
      run on [chain] and [branch_trace] below, where the fact arrives UNDER a decision,
      and
      `mutate_proof.sh` itself refuses a unit clause and prefers a clause emitted inside
      a decision level.

   And the control lane, which is as important as the mutations: the same instances,
   uncorrupted, must verify. A mutation lane whose instance does not verify honestly is
   green for no reason at all. GCS registers a `*_mutation_control` next to each
   mutation lane; [control_lane] is that, and it runs first for every instance -- if it
   fails, the instance's mutation lanes are not run and not counted, because their
   result would mean nothing.

   ------------------------------------------------------------------------------
   M1-T26. Three things changed, and the reason for all three is the same one.

   (a) THE KNOBS MOVED INTO THE EMITTER. Corrupting proof *text* means re-deriving
   from the output what [Writer] already knew, and one of those re-derivations was
   structurally impossible to get right. Under format 3.0 every derived constraint
   carries a label and is cited by it, so `drop-line` -- delete a step -- un-defines
   that step's label and the later citation fails to PARSE. veripb rejects, the lane
   goes green, and not one thing about the derivation was tested. Measured on both
   instances that carried the lane, in both formats:

     root_unsat/drop-line  3.0: "The label `@c3` is not assigned to a constraint ID"
     lin_unsat/drop-line   3.0: "The label `@c13` is not assigned to a constraint ID"
     root_unsat/drop-line  2.0: "Accessing the database out of bound with index 3"

   [Writer.Mutation] is the replacement: typed corruptions applied next to the
   derivation, selected by the [~origin] every rule emission already carries. In
   particular [Truncate_derivation] is what `drop-line` was trying to be -- the step
   is emitted with its derivation thrown away but its label still BOUND, so every
   later citation parses and the checker has to judge the step rather than the
   grammar.

   (b) A REJECTION IS CLASSIFIED. "veripb said no" is not one answer. A rejection that
   never reached the derivation says only that the file is malformed, which any
   corruption of a text file achieves. mutate_proof.sh now exits 5 for that case and
   the lanes below assert which class they expect, so `drop-line` stays registered and
   runs -- as an assertion that it tests the GRAMMAR. It is not counted as if it
   tested a derivation, and it is not quietly deleted either: dropping coverage while
   the lane count stays flat is the same failure mode in a new costume.

   (c) THE CONTROL IS NOT SKIPPABLE. It used to be a lane the caller ran first and a
   convention that it must. Now it is enforced twice over: mutate_proof.sh verifies
   the uncorrupted proof inside every lane before it will report anything, and here
   [mutation_lane] and [emitter_lane] take a [controlled] token that only [gated] can
   make and only after the control has passed. A mutation lane that has not had its
   control run is not something this file can express. [gated] also fails every
   declared lane by name when the control fails, and asserts afterwards that the lanes
   run are exactly the lanes declared -- so coverage cannot quietly shrink either.
   [waiting_lanes] is gone with it: a control that fails is red, not "waiting".
   ------------------------------------------------------------------------------

   M1-T13 and the two branch instances. [chain] is the real thing: it branches, fails a
   branch and backtracks, which D-0018 says is the only shape that can catch a
   regression in this area ("a root-level UNSAT model cannot catch a regression here").
   Its clause lanes run against the trace line D-0018 point 1 specifies, and the literal
   `rup-drop-lit` removes from it is the negated decision -- the one case trap 3 says is
   a real corruption.

   [branch_trace] is the hand-built stand-in for that: a decision level, a fact derived
   under it, and the reason that carries the decision, written straight through [Writer]
   and [Encoding]. It was built when no proof the solver emitted both verified and
   contained a branch-level clause, and it stays because it pins the two clause lanes to
   an instance whose margin is one by construction, independently of whatever the search
   currently emits. [chain]'s own lanes are guarded on its control lane -- which since
   M1-T26 means they FAIL if that control fails, rather than reporting as waiting. A
   lane that is allowed to stand down on its own is a lane that can disappear without
   anyone noticing. *)

module Lit = Baguette_proof.Lit
module Opb = Baguette_proof.Opb
module Writer = Baguette_proof.Writer
module Checker = Baguette_proof.Checker
module Encoding = Baguette_proof.Encoding
module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Engine = Baguette_core.Engine
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify

(* M1-T53: the inner heap guard. test_prop.exe is the binary that reached 14.9 GB RSS on
   2026-09-16 and had to be killed by hand, so a guard that covered only test_output and
   test_compile would have missed the one incident it exists to prevent. `ulimit -v` stays
   the outer backstop -- see mem_guard.ml's header for what this cannot see. *)
let () = Mem_guard.install ()
let failures = ref 0
let checks = ref 0

let check name cond =
  incr checks;
  if cond then Printf.printf "ok   %s\n" name
  else (
    incr failures;
    Printf.printf "FAIL %s\n" name)

let fail fmt =
  incr failures;
  Printf.ksprintf (fun s -> Printf.printf "FAIL %s\n" s) fmt

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let indent s =
  String.split_on_char '\n' s
  |> List.filter (fun l -> String.trim l <> "")
  |> List.map (fun l -> "       " ^ l)
  |> String.concat "\n"

let show s = if String.trim s <> "" then print_endline (indent s)

(* mutate_proof.sh says "corrupted proof kept at DIR" when it keeps its working copy.
   Remove that directory again -- used only where the acceptance was expected and the
   files are therefore not evidence of anything. The basename guard is so that a
   garbled line can never turn this into a delete of something else. *)
let discard_kept_files out =
  let marker = "corrupted proof kept at " in
  let n = String.length marker in
  let after_marker line =
    let rec find i =
      if i + n > String.length line then None
      else if String.sub line i n = marker then
        Some (String.trim (String.sub line (i + n) (String.length line - i - n)))
      else find (i + 1)
    in
    find 0
  in
  let remove_dir dir =
    let base = Filename.basename dir in
    let prefix = "baguette-mutate-" in
    if
      String.length base > String.length prefix
      && String.sub base 0 (String.length prefix) = prefix
      && Sys.file_exists dir
    then (
      Array.iter
        (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
        (Sys.readdir dir);
      try Sys.rmdir dir with _ -> ())
  in
  String.split_on_char '\n' out
  |> List.iter (fun line ->
         match after_marker (String.trim line) with
         | Some dir -> remove_dir dir
         | None -> ())

(* ------------------------------------------------------------------ *)
(* Finding scripts/mutate_proof.sh                                     *)
(*                                                                     *)
(* dune runs a test with its cwd inside the build directory and does   *)
(* not copy scripts/ there, so the script has to be found in the       *)
(* source tree. Walking up from the cwd finds it for the in-tree       *)
(* `_build/` that `make test` uses; a --build-dir elsewhere (which is  *)
(* how concurrent sessions build, see CLAUDE.md) has no path back to   *)
(* the source, so BAGUETTE_ROOT is the override for that case.         *)
(*                                                                     *)
(* Not finding it is a loud failure and never a quiet pass: a mutation *)
(* lane that does not run is the exact failure mode this file exists   *)
(* to prevent.                                                         *)
(* ------------------------------------------------------------------ *)

let rec ancestors dir =
  let parent = Filename.dirname dir in
  if parent = dir then [ dir ] else dir :: ancestors parent

let script =
  let candidates =
    (match Sys.getenv_opt "BAGUETTE_ROOT" with Some r -> [ r ] | None -> [])
    @ ancestors (Sys.getcwd ())
    @ ancestors (Filename.dirname Sys.executable_name)
  in
  List.find_opt Sys.file_exists
    (List.map (fun d -> Filename.concat d "scripts/mutate_proof.sh") candidates)

(* ------------------------------------------------------------------ *)
(* Running one lane                                                    *)
(* ------------------------------------------------------------------ *)

(* The exit codes mutate_proof.sh documents. "The lane did nothing" is deliberately
   not the same value as "the lane passed". *)
type lane_result =
  | Held (* veripb rejected the corruption ON THE DERIVATION, or accepted the control *)
  | Slack (* veripb ACCEPTED a corrupted proof, or rejected the control *)
  | Not_applicable (* no site for this mutation in this proof *)
  | Unevaluated
    (* veripb rejected without ever judging the derivation: the proof did not parse, or
       a rule cited an id that is no longer defined. NOT a pass -- the lane tested the
       grammar. This is what `drop-line` does under 3.0; see (a) in the header. *)
  | No_checker (* veripb (or the script) missing: nothing was checked *)
  | Broken of int (* usage or internal error in the harness *)

let lane_result_name = function
  | Held -> "rejected-on-the-derivation"
  | Slack -> "ACCEPTED"
  | Not_applicable -> "no-site"
  | Unevaluated -> "rejected-without-judging-the-derivation"
  | No_checker -> "no-checker"
  | Broken n -> Printf.sprintf "harness-error(%d)" n

let run_lane ?nth ~proof mutation =
  match script with
  | None ->
      ( No_checker,
        "scripts/mutate_proof.sh was not found from the cwd, the executable path or \
         $BAGUETTE_ROOT" )
  | Some sh ->
      let log = Filename.temp_file "baguette_mutation" ".log" in
      let rc =
        Sys.command
          (Printf.sprintf "bash %s %s %s %s > %s 2>&1" (Filename.quote sh)
             (match nth with None -> "" | Some n -> Printf.sprintf "--nth %d" n)
             (Filename.quote mutation) (Filename.quote proof) (Filename.quote log))
      in
      let out = read_file log in
      (try Sys.remove log with _ -> ());
      ( (match rc with
        | 0 -> Held
        | 1 -> Slack
        | 3 -> Not_applicable
        | 4 -> No_checker
        | 5 -> Unevaluated
        | n -> Broken n),
        out )

(* ------------------------------------------------------------------ *)
(* The control gate                                                    *)
(*                                                                     *)
(* A mutation lane whose instance does not verify honestly is green    *)
(* for no reason at all. Making that a rule the caller follows is not  *)
(* making it a rule, so it is a TYPE here: [mutation_lane] and         *)
(* [emitter_lane] take a [controlled], and [gated] is the only thing   *)
(* that builds one -- after the control has passed. A lane without a   *)
(* control is not an expression this file has.                         *)
(* ------------------------------------------------------------------ *)

type controlled = {
  c_tag : string;
  c_declared : string list; (* the lanes this instance promises to run *)
  mutable c_run : string list; (* the lanes it actually ran *)
}

(* The control lane itself. Returns whether it held. *)
let control_holds ~tag ~proof =
  let r, out = run_lane ~proof "control" in
  match r with
  | Held ->
      check (Printf.sprintf "%s/control: veripb accepts the honest proof" tag) true;
      true
  | No_checker ->
      fail "%s/control: NOTHING was checked -- do not read this as a pass" tag;
      show out;
      false
  | _ ->
      fail
        "%s/control: the uncorrupted proof does not verify, so every mutation lane on \
         this instance would be green for no reason at all"
        tag;
      show out;
      false

(* Run an instance's lanes behind its control.

   [declares] is the list of lane names the instance promises. Two things depend on it,
   and both are about coverage not being allowed to shrink quietly:

   - if the control FAILS, every declared lane is failed BY NAME. The run is red and
     says which lanes did not run. It does not merely become shorter.
   - if the control passes, the lanes actually run are checked against [declares]
     afterwards. A lane deleted from the body while its name stays in the list -- or
     the reverse -- is a failure, not a silently different suite. *)
let gated ~tag ~declares ~control body =
  if control () then (
    let c = { c_tag = tag; c_declared = declares; c_run = [] } in
    body c;
    let sort = List.sort compare in
    check
      (Printf.sprintf "%s: every lane this instance declares was run (%d)" tag
         (List.length c.c_declared))
      (sort c.c_run = sort c.c_declared))
  else
    List.iter
      (fun m ->
        fail
          "%s/%s: NOT RUN. The control lane on this instance failed, so this lane was \
           not attempted -- and a lane that did not run is not a lane that passed."
          tag m)
      declares

let ran c name = c.c_run <- name :: c.c_run

(* ------------------------------------------------------------------ *)
(* A lane through the text harness, scripts/mutate_proof.sh            *)
(* ------------------------------------------------------------------ *)

(* [expect] says which outcome this lane is asserting:

   [`Rejects]          veripb must reject the corruption ON THE DERIVATION. The only
                       expectation that means "this step is load-bearing".
   [`Known_slack why]  veripb is known to ACCEPT the corruption. Recorded the way
                       test/models/PENDING records a known failure: reported on every
                       run so it cannot be forgotten, and if it starts holding the suite
                       goes red telling you to delete the marker. Not a weakened test --
                       the lane runs and its result is asserted, against the outcome
                       that was measured.
   [`Unevaluated why]  veripb rejects, but without ever judging the derivation. The lane
                       tests the GRAMMAR. Registered so that it keeps running and keeps
                       saying so, and so that the day it starts judging a derivation the
                       suite says that too. It is NOT counted as derivation coverage;
                       the emitter knob named in [why] is what covers that. *)
let mutation_lane c ?nth ~proof ~expect mutation =
  let tag = c.c_tag in
  let name = Printf.sprintf "%s/%s" tag mutation in
  ran c mutation;
  let r, out = run_lane ?nth ~proof mutation in
  let wrong_class got =
    incr checks;
    fail
      "%s: this lane is registered as %s but veripb answered %s. The lane has found \
       something: say what, do not re-register it to match (CLAUDE.md)."
      name
      (match expect with
      | `Rejects -> "rejecting on the derivation"
      | `Known_slack _ -> "accepting (known slack)"
      | `Unevaluated _ -> "rejecting without judging the derivation")
      (lane_result_name got);
    show out
  in
  match (r, expect) with
  | Held, `Rejects ->
      check (Printf.sprintf "%s: veripb rejects the corrupted proof" name) true
  | Held, `Known_slack _ ->
      incr checks;
      fail
        "XPASS %s: veripb now REJECTS this corruption. The derivation is tighter than it \
         was, or the instance stopped exercising it -- find out which, then delete this \
         lane's entry from [known_slack] below."
        name
  | Unevaluated, `Unevaluated why ->
      check
        (Printf.sprintf
           "%s: veripb rejects, and rejects on the GRAMMAR rather than the derivation -- \
            %s"
           name why)
        true
  | Slack, `Rejects ->
      incr checks;
      fail
        "%s: veripb ACCEPTED a deliberately corrupted proof. The honest derivation has \
         slack in it -- the corrupted step is not load-bearing, so 'veripb accepts' says \
         nothing about it. This is a finding about the propagator, not about the \
         harness: record it in docs/DECISIONS.md. Do not weaken the lane to make it \
         pass."
        name;
      show out
  | Slack, `Known_slack why ->
      Printf.printf "xslack %s: veripb accepts this corruption -- %s\n" name why;
      (* mutate_proof.sh keeps the corrupted proof whenever veripb accepts, which is
         right when that is news. On a lane already registered as slack it is not news,
         and keeping one directory per run would litter /tmp forever, so tidy it up. *)
      discard_kept_files out
  | Not_applicable, _ ->
      incr checks;
      fail
        "%s: the mutation found no site to corrupt, so nothing was tested. A registered \
         lane whose instance has no such step is not a pass; fix the instance."
        name;
      show out
  | No_checker, _ ->
      incr checks;
      fail "%s: NOTHING was checked -- do not read this as a pass" name;
      show out
  | Broken n, _ ->
      incr checks;
      fail "%s: mutate_proof.sh itself failed (exit %d)" name n;
      show out
  | (Held | Slack | Unevaluated), _ -> wrong_class r

(* ------------------------------------------------------------------ *)
(* Instances                                                           *)
(* ------------------------------------------------------------------ *)

let tmpdir () =
  let d = Filename.temp_file "baguette_mutation" "" in
  Sys.remove d;
  Sys.mkdir d 0o700;
  d

(* A model as this file needs it: named integer variables, and rows `sum a_i x_i <= r`
   over their indices. An equality is its two rows, written out (D-0011). *)
type model = { vars : (string * int * int) array; rows : ((int * int) list * int) list }

let evaluate m assign =
  List.for_all
    (fun (terms, rhs) ->
      List.fold_left (fun acc (a, i) -> acc + (a * assign.(i))) 0 terms <= rhs)
    m.rows

(* I-S1 in miniature: re-check a solution against the model rather than trusting the
   propagators that produced it. *)
let independent_check m (assignment : Search.assignment) =
  let assign = Array.make (Array.length m.vars) 0 in
  List.iter (fun (v, value) -> assign.(Var.to_int v) <- value) assignment;
  evaluate m assign

(* What a builder hands back. [fired] is [false] for an honest build and says, for a
   mutated one, whether the knob found a site it could corrupt. A lane must check it:
   a knob that did not fire leaves an honest proof, veripb accepts it, and reading that
   acceptance as "the step was not load-bearing" would be a finding about a corruption
   that never happened. It is the emitter's [Not_applicable]. *)
type built = { pbp : string; opb : string; fired : bool }

(* The .opb side of an instance: declare its variables, post its rows, hand back the
   encoding and the row ids. Factored out of [solve_to_proof] because
   [rows_that_refute_alone] must certify the SAME .opb the lanes are run against -- a
   second copy of this that drifted would certify a model nothing tests. *)
let encoding_of m =
  let enc = Encoding.create () in
  Array.iter (fun (n, lo, hi) -> Encoding.declare_int enc n ~lo ~hi) m.vars;
  let named terms =
    List.map
      (fun (a, i) ->
        let n, _, _ = m.vars.(i) in
        (a, n))
      terms
  in
  let row_ids =
    List.map (fun (terms, rhs) -> Encoding.add_int_lin_le enc (named terms) rhs) m.rows
  in
  (enc, row_ids)

(* Solve [m] through the real pipeline -- the same one test_endtoend.ml drives -- and
   leave the .opb/.pbp pair behind for the harness to corrupt. These are the solver's
   own proofs, not transcriptions of them, so a lane cannot go stale against a
   derivation that changed underneath it.

   [?mutation] arms one of the emitter's typed knobs for this build. A build without it
   goes through [Writer.create], which cannot corrupt anything. *)
let solve_to_proof ?mutation ~dir ~name m =
  let opb = Filename.concat dir (name ^ ".opb") in
  let pbp = Filename.concat dir (name ^ ".pbp") in
  let store =
    Store.create
      ~names:(Array.map (fun (n, _, _) -> n) m.vars)
      ~domains:(Array.map (fun (_, lo, hi) -> Domain.make lo hi) m.vars)
  in
  let enc, row_ids = encoding_of m in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "test_mutation: " ^ name ] enc oc;
  close_out oc;
  let oc = open_out pbp in
  let writer =
    match mutation with
    | None -> Writer.create ~comments:false ~audit:true oc
    | Some mutation -> Writer.create_mutated ~comments:false ~audit:true ~mutation oc
  in
  Encoding.start_proof enc writer;
  (* M1-T31: no ambient row to install, so no thunk to fail. *)
  let ctx = Justify.create ~writer ~encoding:enc in
  let instances =
    List.map2
      (fun (terms, rhs) row_id ->
        Linear.make ~row_id store (List.map (fun (a, i) -> (a, Var.of_int i)) terms) rhs)
      m.rows row_ids
  in
  let engine =
    Engine.create
      (List.mapi
         (fun id lin ->
           Propagator.pack ~id (module Linear : Propagator.S with type t = Linear.t) lin)
         instances)
  in
  let outcome = Search.solve ~engine ~store ~ctx ~check:(independent_check m) () in
  close_out oc;
  ({ pbp; opb; fired = Writer.mutation_fired writer }, outcome)

(* -- root_unsat -----------------------------------------------------------------
   test/models/trivial_unsat.fzn's model: x in 1..3 with x <= 0. Propagation refutes
   it at level 0 and the whole proof is one `pol` over the model row plus two order-
   encoding axioms, closing at `0 >= 1`.

   Its margin is one, and that used to be the whole reason it carried the `pol` lanes.
   M1-T26 found that the margin is not sufficient: its .opb row

       @c2  +1 ~x_ge_2 +1 ~x_ge_3 >= 3

   asks two coefficient-1 literals to sum to 3 and is INFEASIBLE ON ITS OWN, so the
   model is refuted by a single row and the `pol` above it restates a contradiction the
   checker already had. See D-0030.

   THE LANES HAVE MOVED to [triple_unsat] below (M1-T38). This instance stays, and is
   still built and still put to the checker, as the CONTROL for
   [rows_that_refute_alone]: the procedure that certifies a candidate instance is only
   evidence if it can be seen finding the defect, and this is the row known to have it.
   If it ever stops being found, the certification of every other instance in this file
   means nothing, and the check below says so rather than going quietly green. *)
let root_unsat = { vars = [| ("x", 1, 3) |]; rows = [ ([ (1, 0) ], 0) ] }

(* -- triple_unsat ---------------------------------------------------------------
   M1-T38's replacement for [root_unsat] on the `pol` lanes.

       x, y, z in 0..3,   x + y + z <= 3,   x >= 2,   y >= 2

   Four properties, and the instance was chosen for all four at once. The first is the
   one D-0030 says root_unsat cannot have; the fourth is what made a first, smaller
   candidate (the same thing without z) unusable, and is recorded so it is not
   rediscovered.

   1. NO SINGLE ROW REFUTES IT, and neither does any pair. The .opb is

        @c1..@c6  the three ladders
        @c7  +1 ~x_ge_1 .. +1 ~z_ge_3 >= 6      (nine literals)
        @c8  +1 x_ge_1 +1 x_ge_2 +1 x_ge_3 >= 2
        @c9  +1 y_ge_1 +1 y_ge_2 +1 y_ge_3 >= 2

      Every one of those is satisfiable on its own -- nine literals asked for six,
      three asked for two, three asked for two -- and so is every pair: @c7 with @c8
      leaves `sum ~y + sum ~z >= 3`, and @c8 and @c9 share no variable. Only all three
      together close, so refuting this model genuinely REQUIRES the derivation.
      Asserted two ways by [no_single_row_refutes] below, the second of which is the
      checker's answer rather than our arithmetic.

   2. THE MARGIN IS ONE (trap 1). The derivation's left-hand side is nine
      complementary pairs collapsing to 3 + 3 + 3 = 9, against 6 + 2 + 2 = 10 on the
      right: `0 >= 1`, exactly. A unit of energy taken out of, or put into, the `pol`
      and it stops being a contradiction.

   3. TRUNCATING THE DERIVATION LOSES IT. The step the `conclusion` cites is a
      three-way combine whose first operand is @c7, which is satisfiable, so the
      corruption is judged rather than absorbed. That is the lane root_unsat could not
      carry. Emitted:

        @c10 pol @c8 ;
        @c11 pol @c9 ;
        @c12 pol @c7 @c10 + @c11 + z_ge_1 z_ge_2 + z_ge_3 + + ;
        conclusion UNSAT : @c12 ;

   4. z IS IN NO OTHER ROW, AND THAT IS THE POINT. Nothing pins z, so its whole
      contribution to @c7 has to be weakened away by literal axioms
      (Order_reason.weaken_declared, D-0013) -- the `z_ge_1 z_ge_2 + z_ge_3 +` tail
      above. Without a spectator variable the derivation is all constraint ids and no
      coefficients, and `pol-coeff` / `perturb-coefficient` have NO SITE: they report
      not-applicable and the lane fails saying nothing was tested. Measured on the
      two-variable version of this instance before z was added. A `pol` lane needs a
      `pol` with arithmetic in it, which is a requirement on the instance that neither
      trap 1 nor D-0030 implies.

   Deliberately NOT a bigger gap: at a gap of more than one the sum closes at
   `0 >= k` with k > 1 and trap 1 bites, which is what lin_unsat is and why its
   `pol-coeff` lane is registered known-slack. *)
let triple_unsat =
  {
    vars = [| ("x", 0, 3); ("y", 0, 3); ("z", 0, 3) |];
    rows = [ ([ (1, 0); (1, 1); (1, 2) ], 3); ([ (-1, 0) ], -2); ([ (-1, 1) ], -2) ];
  }

(* ------------------------------------------------------------------ *)
(* Certifying an instance: does refuting it need the derivation?       *)
(*                                                                     *)
(* D-0030's finding, as a procedure a lane's instance must pass before *)
(* the lane means anything. The technique is M2-T1/M2-T2's, in         *)
(* test/unit/test_prop.ml [test_no_single_row_refutes]; it is reused   *)
(* here against this file's own [model] values rather than against     *)
(* .fzn files, because these instances have no .fzn.                   *)
(* ------------------------------------------------------------------ *)

(* The largest value a row's left-hand side can take. A variable occurring at both
   polarities can only contribute once, which is the trap a plain sum of positive
   coefficients falls into -- and it is exactly the shape the order encoding produces.
   Same function as test_prop.ml's; that file is another session's and neither may
   depend on the other's internals, so it is written out rather than shared. *)
let max_attainable_lhs (c : Opb.constr) =
  let tbl = Hashtbl.create 16 in
  List.iter
    (fun (a, (l : Lit.t)) ->
      let key = Lit.var_name l.Lit.v in
      let p, n = try Hashtbl.find tbl key with Not_found -> (0, 0) in
      if l.Lit.positive then Hashtbl.replace tbl key (p + a, n)
      else Hashtbl.replace tbl key (p, n + a))
    (Opb.terms c);
  Hashtbl.fold (fun _ (p, n) acc -> acc + max (max p n) 0) tbl 0

(* Which of [m]'s .opb rows refute the model ALL BY THEMSELVES, put to the checker
   rather than to our own arithmetic: for each row id in turn, a proof that derives
   NOTHING and concludes `UNSAT : @ci`. veripb accepting one means row i is already a
   contradiction, so every derivation above it is decoration and no mutation lane on
   this instance can show a step to be load-bearing.

   [Error msg] rather than an empty list when nothing could be run: a certification
   that did not happen is never a pass. *)
type certification = Refuted_alone of int list | Cannot_certify of string

let rows_that_refute_alone ~dir ~name m =
  match Checker.find () with
  | None -> Cannot_certify Checker.not_found_message
  | Some veripb ->
      let enc, _ = encoding_of m in
      let rows = Encoding.constraints enc in
      let n = Opb.n_checker_constraints rows in
      let opb = Filename.concat dir (name ^ "_cert.opb") in
      let accepted = ref [] in
      for i = 1 to n do
        (* M2-T14. Both files go through [Writer]/[Encoding] so that they cannot
           disagree about the grammar. They did: the .opb came from [write_opb], which
           followed a format switch, while the proof was literal text hardcoded to 3.0
           with `;` terminators and an `@c<i>` citation. Set the switch the other way and
           that wrote an UNLABELLED .opb and then cited a label in it, so every row was
           refused on the grammar, [accepted] came back empty for every instance, and
           [no_single_row_refutes] reported "no row refutes alone" about a procedure that
           could not have found one.

           That is D-0030's own guard against a hollow instance, passing for exactly the
           reason D-0030 exists. It was caught by [certification_finds_root_unsat], the
           control that asserts the procedure can still find the row it is known to have
           -- which is why that control is not optional. The switch is gone (D-0046) and
           the two files cannot differ any more, but the .pbp below is still literal text
           and would drift from the .opb the same way if the grammar ever moved. *)
        let pbp = Filename.concat dir (name ^ "_cert.pbp") in
        let oc = open_out pbp in
        let w = Writer.create ~comments:false ~audit:false oc in
        let opb_oc = open_out opb in
        Encoding.write_opb ~comments:[ "test_mutation: certifying " ^ name ] enc opb_oc;
        close_out opb_oc;
        Encoding.start_proof enc w;
        (* Derives NOTHING: the conclusion names a model row directly. *)
        Writer.conclusion w (Writer.Unsat (Some i));
        close_out oc;
        let log = Filename.concat dir (name ^ "_cert.log") in
        let rc =
          Sys.command
            (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
               (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
        in
        if rc = 0 then accepted := i :: !accepted;
        (try Sys.remove pbp with _ -> ());
        try Sys.remove log with _ -> ()
      done;
      (try Sys.remove opb with _ -> ());
      Refuted_alone (List.rev !accepted)

(* The arithmetic half of the same question, on our own reading of the rows. Kept
   beside the checker's answer rather than instead of it: this one names the row in
   terms a reader can check by eye, and the checker's is the one that cannot be wrong
   about what veripb will do. *)
let rows_infeasible_by_arithmetic m =
  let enc, _ = encoding_of m in
  List.filter
    (fun c -> Opb.relation c = Opb.Ge && max_attainable_lhs c < Opb.rhs c)
    (Encoding.constraints enc)

(* Assert that no single row of [m] refutes it, i.e. that an instance is fit to carry a
   mutation lane at all. Both halves must agree that there is nothing to find. *)
let no_single_row_refutes ~dir ~name m =
  let bad = rows_infeasible_by_arithmetic m in
  check
    (Printf.sprintf "%s: no .opb row is infeasible on its own, by arithmetic (D-0030)"
       name)
    (bad = []);
  List.iter
    (fun c -> Printf.printf "       infeasible alone: %s\n" (Opb.constr_to_string c))
    bad;
  match rows_that_refute_alone ~dir ~name m with
  | Cannot_certify why ->
      fail
        "%s: the D-0030 certification did NOT run (%s), so nothing below it is evidence"
        name why
  | Refuted_alone [] ->
      check
        (Printf.sprintf
           "%s: veripb rejects a derivation-free proof against every model row, so \
            refuting this instance needs the derivation (D-0030)"
           name)
        true
  | Refuted_alone ids ->
      fail
        "%s: veripb ACCEPTS a proof that derives nothing and concludes `UNSAT : %s`. \
         This instance is as hollow as root_unsat and cannot carry a mutation lane -- \
         fix the instance, do not re-register the lane."
        name
        (String.concat ", " (List.map (fun i -> Printf.sprintf "@c%d" i) ids))

(* The control for that procedure, and it is not optional. D-0030 was found because an
   instance nobody had certified turned out to be hollow; a certification nobody has
   watched find a defect is the same mistake one level up. [root_unsat] is the row
   known to be bad, so the procedure must report it -- both halves of it. *)
let certification_finds_root_unsat ~dir =
  let bad = rows_infeasible_by_arithmetic root_unsat in
  check "D-0030 control: the arithmetic half DOES find root_unsat's infeasible row"
    (List.exists (fun c -> Opb.constr_to_string c = "+1 ~x_ge_2 +1 ~x_ge_3 >= 3 ;") bad);
  (* The over-counting trap, and it needs its own control because root_unsat's bad row
     does NOT exercise it: its two literals are different variables, so summing the two
     polarities and taking their maximum give the same answer. Replacing [max p n] with
     [p + n] leaves every check above green -- measured. A row mentioning one variable
     at both polarities can only reach 1. *)
  let both = Opb.ge [ (1, Lit.bool_true "a"); (1, Lit.bool_false "a") ] 2 in
  check
    "D-0030 control: a variable at both polarities is counted once, not twice, so the \
     arithmetic half finds this row infeasible too"
    (max_attainable_lhs both = 1 && max_attainable_lhs both < Opb.rhs both);
  let ok = Opb.clause [ Lit.bool_true "a"; Lit.bool_false "b" ] in
  check "D-0030 control: ... and it does not fire on an ordinary clause"
    (max_attainable_lhs ok >= Opb.rhs ok);
  match rows_that_refute_alone ~dir ~name:"root_unsat_control" root_unsat with
  | Cannot_certify why -> fail "D-0030 control: the certification did NOT run (%s)" why
  | Refuted_alone ids ->
      check
        "D-0030 control: the checker half DOES find that root_unsat is refuted by one \
         row alone (@c2), so the procedure can be seen working"
        (List.mem 2 ids)

(* -- lin_unsat ------------------------------------------------------------------
   test/models/lin_unsat.fzn: x + y <= 3 against x + y >= 8, over x, y in 0..5. The
   D-0015 Combine derivation: two weakenings of the <= row, then one addition against
   the >= row. It closes at `0 >= 2`, so it has a unit of slack, which is exactly what
   trap 1 warns about and exactly why its `pol-coeff` lane is registered known-slack
   rather than green. *)
let lin_unsat =
  {
    vars = [| ("x", 0, 5); ("y", 0, 5) |];
    rows = [ ([ (1, 0); (1, 1) ], 3); ([ (-1, 0); (-1, 1) ], -8) ];
  }

(* -- chain ----------------------------------------------------------------------
   test/models/chain_sat.fzn's model, as six `<=` rows: a + b + c = 6, b = a + 1,
   c = b + 1, over 0..9. Root propagation does not settle it, so the search branches;
   the first branch fails and is backtracked. D-0018's testing note says this is the
   only shape that can catch a regression in the branch-level derivation -- "a
   root-level UNSAT model cannot catch a regression here".

   Whether its proof verifies is M1-T13's business, not this file's, so the lanes below
   are guarded on its control lane: they run when the branch-level proof verifies and
   are printed as waiting when it does not. *)
let chain =
  {
    vars = [| ("a", 0, 9); ("b", 0, 9); ("c", 0, 9) |];
    rows =
      [
        ([ (1, 0); (1, 1); (1, 2) ], 6);
        ([ (-1, 0); (-1, 1); (-1, 2) ], -6);
        ([ (1, 1); (-1, 0) ], 1);
        ([ (-1, 1); (1, 0) ], -1);
        ([ (1, 2); (-1, 1) ], 1);
        ([ (-1, 2); (1, 1) ], -1);
      ];
  }

(* -- branch_trace ---------------------------------------------------------------
   The stand-in for a D-0018 branch proof, hand-built because the solver does not emit
   one that verifies yet.

   Model: x, y in 0..2 with x + y >= 3. Under the decision x <= 1, y >= 2 follows, and
   the trace line that says so is

       rup +1 y_ge_2 +1 x_ge_2 >= 1 ;

   the claim disjoined with the negation of its reason -- which here is the decision
   itself. That is D-0018 point 1's shape exactly.

   The instance is chosen so that BOTH halves are load-bearing, which makes the lane
   independent of the order Opb happens to print the literals in: `y_ge_2` alone is not
   RUP (x = 2, y = 1 satisfies the model), and `x_ge_2` alone is not RUP either
   (x = 1, y = 2 does). Drop either literal and the checker must reject. That is the
   margin-one property of trap 1 carried over to a clause.

   It is also why this is not a root-level reason: at the root the claim would restate
   what the checker already has, the corruption would be empty, and the lane would go
   green having tested nothing (trap 3). *)
let branch_trace ?mutation ?(name = "branch_trace") ~dir () =
  let opb = Filename.concat dir (name ^ ".opb") in
  let pbp = Filename.concat dir (name ^ ".pbp") in
  let enc = Encoding.create () in
  Encoding.declare_int enc "x" ~lo:0 ~hi:2;
  Encoding.declare_int enc "y" ~lo:0 ~hi:2;
  let _row = Encoding.add_int_lin_le enc [ (-1, "x"); (-1, "y") ] (-3) in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "test_mutation: branch_trace (M1-T15)" ] enc oc;
  close_out oc;
  let oc = open_out pbp in
  let w =
    match mutation with
    | None -> Writer.create ~comments:false ~audit:true oc
    | Some mutation -> Writer.create_mutated ~comments:false ~audit:true ~mutation oc
  in
  Encoding.start_proof enc w;
  (* The decision level, and the fact that arrives under it. *)
  Writer.set_level w 1;
  let _trace =
    Writer.rup_clause w ~origin:"branch_trace: y >= 2 under the decision x <= 1"
      (* Both are real order literals on 0..2, so [Lit.ge] is what [Encoding.ge]
         would hand back: no [Holds]/[Fails] case to thread through here. *)
      [ Lit.ge "y" 2; Lit.ge "x" 2 ]
  in
  (* Backtrack the way search.ml does: re-set the level, then wipe it. Emitting the
     nogood BEFORE the wipe is D-0018 point 4; there is no nogood here because this
     branch does not fail -- supplying one is M1-T13's job, on [chain] above. *)
  Writer.set_level w 1;
  Writer.wipe_level w 1;
  Writer.conclusion w (Writer.Sat (Encoding.assignment_lits enc [ ("x", 2); ("y", 1) ]));
  close_out oc;
  { pbp; opb; fired = Writer.mutation_fired w }

(* ------------------------------------------------------------------ *)
(* Lanes through the emitter (M1-T26)                                  *)
(* ------------------------------------------------------------------ *)

let contains hay needle =
  let n = String.length needle and h = String.length hay in
  let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
  n = 0 || go 0

(* Why veripb said no. The distinction is the whole of M1-T26 (b): a rejection that
   never reached the derivation says only that the file is malformed. The markers are
   VeriPB 3.0.2's, taken from runs; scripts/mutate_proof.sh classifies on the same list
   and exits 5 where this returns [Rejected_unevaluated], so the two halves of the
   harness agree about what a lane has shown. *)
type verdict = Accepted | Rejected_on_derivation | Rejected_unevaluated | Unchecked

let unevaluated_markers =
  [
    "Syntax error while parsing";
    "is not assigned to a constraint ID";
    "Accessing the database out of bound";
    "has already been deleted";
    "Unsupported version";
  ]

(* An emitter lane has no file to corrupt -- the corruption happened as the proof was
   written -- so it runs the checker itself, through the same [Checker.find] the rest
   of the tree resolves with. D-0023 put the choice of checker in exactly two places;
   this is not a third. A missing checker is a FAILURE, never a skip. *)
let check_proof { pbp; opb; _ } =
  match Checker.find () with
  | None -> (Unchecked, Checker.not_found_message)
  | Some veripb ->
      let log = Filename.temp_file "baguette_mutation_veripb" ".log" in
      let rc =
        Sys.command
          (Printf.sprintf "%s %s %s > %s 2>&1" (Filename.quote veripb)
             (Filename.quote opb) (Filename.quote pbp) (Filename.quote log))
      in
      let out = read_file log in
      (try Sys.remove log with _ -> ());
      let v =
        if rc = 0 then Accepted
        else if List.exists (contains out) unevaluated_markers then Rejected_unevaluated
        else Rejected_on_derivation
      in
      (v, out)

let verdict_name = function
  | Accepted -> "ACCEPTED"
  | Rejected_on_derivation -> "rejected-on-the-derivation"
  | Rejected_unevaluated -> "rejected-without-judging-the-derivation"
  | Unchecked -> "NOTHING CHECKED"

(* The banner [Writer.header] stamps on any proof built by [create_mutated]. Asserted
   on every emitter lane: a corrupted proof that did not say so could be mistaken for a
   real one, and a clean proof that did would mean the stamp had stopped meaning
   anything. *)
let corruption_banner = "DELIBERATELY CORRUPTED PROOF"

(* One emitter lane.

   [build ~name ~mutation] emits the instance with the knob armed and returns the
   [built] record. Four assertions, in order, and the first three are all about the
   ways a lane can be green having tested nothing:

     1. the knob FIRED -- otherwise the proof is honest and its acceptance says
        nothing (see [built]);
     2. the proof carries the corruption banner;
     3. the control has already passed, which the [controlled] token witnesses;
     4. the checker's verdict is the expected one, CLASS INCLUDED. *)
let emitter_lane c ~build ~expect ~knob name =
  let tag = c.c_tag in
  let lane = Printf.sprintf "%s/%s" tag name in
  ran c name;
  let b = build ~name:(Printf.sprintf "%s_%s" tag name) ~mutation:knob in
  if not b.fired then (
    incr checks;
    fail
      "%s: the knob %s found no site it could corrupt, so the proof this lane checked is \
       HONEST. Nothing was tested -- fix the site, do not read the checker's answer."
      lane
      (Writer.Mutation.describe knob))
  else if not (contains (read_file b.pbp) corruption_banner) then (
    incr checks;
    fail "%s: a corrupted proof was emitted without the %S banner" lane corruption_banner)
  else
    let v, out = check_proof b in
    match (v, expect) with
    | Rejected_on_derivation, `Rejects ->
        check
          (Printf.sprintf "%s: veripb rejects the corrupted step, on the derivation" lane)
          true
    | Accepted, `Known_slack why ->
        Printf.printf "xslack %s: veripb accepts this corruption -- %s\n" lane why
    | Accepted, `Rejects ->
        incr checks;
        fail
          "%s: veripb ACCEPTED a deliberately corrupted proof. The honest derivation has \
           slack in it -- the corrupted step is not load-bearing. That is a finding \
           about the propagator, not about this harness: record it in docs/DECISIONS.md. \
           Do not weaken the lane to make it pass."
          lane;
        Printf.printf "       knob: %s\n" (Writer.Mutation.describe knob);
        show out
    | Rejected_on_derivation, `Known_slack _ ->
        incr checks;
        fail
          "XPASS %s: veripb now REJECTS this corruption. The derivation is tighter than \
           it was, or the instance stopped exercising it -- find out which, then delete \
           this lane's known-slack entry."
          lane
    | Unchecked, _ ->
        incr checks;
        fail "%s: %s -- do not read this as a pass" lane (verdict_name Unchecked);
        show out
    | Rejected_unevaluated, _ ->
        incr checks;
        fail
          "%s: veripb answered %s -- the proof did not parse, or a rule cited an id that \
           is gone. An EMITTER knob must never do that: it is the failure the text knobs \
           were moved here to escape. The lane tested the grammar and nothing else."
          lane
          (verdict_name Rejected_unevaluated);
        show out

(* ------------------------------------------------------------------ *)
(* The registry                                                        *)
(*                                                                     *)
(* Known slack: a mutation veripb ACCEPTS today. Each entry is a       *)
(* finding about the derivation, not a licence to ignore the lane.     *)
(* ------------------------------------------------------------------ *)

let known_slack_lin_unsat_pol_coeff =
  "lin_unsat's refutation closes at `0 >= 2`, one unit wider than a contradiction needs \
   to be, so a one-unit coefficient perturbation of either weakening step still closes \
   it (`y_ge_1 >= 2` is still infeasible). Trap 1 in this file's header, measured rather \
   than assumed. The `pol` lanes gate on triple_unsat, whose margin is one and whose \
   rows are each individually satisfiable (M1-T38); this lane stays registered so the \
   slack is reported on every run"

(* GONE (M1-T38), and worth recording why rather than just deleting it.

   M1-T26 registered `root_unsat/truncate-derivation` as known-slack. The reason was not
   slack in the derivation at all: root_unsat's model row

       @c2  +1 ~x_ge_2 +1 ~x_ge_3 >= 3

   asks two coefficient-1 literals to sum to 3 and is ALREADY a contradiction, so
   truncating the `pol` above it to its first operand leaves @c2, which still refutes the
   model. Its sibling `pol-coeff` / `pol-cite` lanes rejected only because
   `conclusion UNSAT : @c3` names @c3 by hint and the corruption makes THAT row
   non-contradicting -- a strictly weaker claim than "the derivation was load-bearing".
   D-0030 has the measurement.

   The registration is not deleted to tidy the table: the lanes moved to
   [triple_unsat], whose rows are each individually satisfiable, and the truncation lane
   there REJECTS. root_unsat itself stays in this file as the control for
   [rows_that_refute_alone] -- the defect is still measured on every run, it is simply
   no longer being mistaken for a lane. *)

(* Registered the way [known_slack] is, and for the same reason: the lane keeps running
   and keeps saying what it is. `drop-line` deletes a derivation step, and a derivation
   step is deleted precisely because something later cites it -- so the checker stops at
   the citation and never judges the derivation. Measured in both formats; see (a) in
   this file's header for the messages. The lane is kept because asserting the CLASS of
   the rejection is worth doing (if it ever starts judging a derivation, that is news),
   and the derivation coverage it never had is now carried by the emitter's
   [Truncate_derivation], which corrupts the same step with its label still bound. *)
let drop_line_is_a_grammar_lane =
  "deleting a step un-defines the label every later citation names, so veripb stops at \
   the grammar; Writer.Mutation.Truncate_derivation is the lane that judges this step's \
   derivation"

(* ------------------------------------------------------------------ *)

let run () =
  (* Without the script nothing below can check anything, and a run that quietly
     reports "waiting" lanes would read as if the harness had merely found nothing to
     do. Say it once, loudly, and stop. *)
  if script = None then
    fail
      "scripts/mutate_proof.sh was not found from the cwd, the executable path or \
       $BAGUETTE_ROOT, so NOT ONE mutation lane ran. This is not a pass. Set \
       BAGUETTE_ROOT to the checkout when building into a --build-dir outside it."
  else
    let dir = tmpdir () in
    let knob = Writer.Mutation.make in
    (* Where the emitter knobs aim. A site is a substring of the [~origin] the rule
       emission already carries, so a lane NAMES the derivation it corrupts instead of
       hunting for it in the text. "combine" is Justify.emit_combine's origin (D-0013's
       weaken-divide-add) and the chain site names the claim literal outright: if the
       search stops deriving `~b_ge_2` under a decision, the knob does not fire and the
       lane FAILS saying so, rather than sliding onto a root-level line where dropping a
       reason literal changes nothing the checker can see (trap 3). *)
    let site_combine = "combine" in
    let site_branch_trace = "branch_trace" in
    let site_chain_branch_claim = "trace: ~b_ge_2" in

    (* -- the pol lanes, on the margin-one instance ---------------------------- *)
    (* M1-T38. The lanes were on [root_unsat] until D-0030 showed that one of its model
       rows refutes the model by itself, so nothing above it can be load-bearing. They
       are on [triple_unsat] now, and BEFORE they run, the procedure that says so is
       shown finding that defect on root_unsat and not finding it here. An instance
       that has not been certified is one nobody has checked can fail. *)
    certification_finds_root_unsat ~dir;
    no_single_row_refutes ~dir ~name:"triple_unsat" triple_unsat;
    let b, outcome = solve_to_proof ~dir ~name:"triple_unsat" triple_unsat in
    check "triple_unsat: the solver refutes it (the instance is what we think it is)"
      (outcome = Search.Unsat);
    let build_triple ~name ~mutation =
      fst (solve_to_proof ~mutation ~dir ~name triple_unsat)
    in
    gated ~tag:"triple_unsat"
      ~control:(fun () -> control_holds ~tag:"triple_unsat" ~proof:b.pbp)
      ~declares:
        [
          "pol-coeff";
          "pol-cite";
          "drop-line";
          "perturb-coefficient";
          "swap-citation";
          "truncate-derivation";
        ]
      (fun c ->
        mutation_lane c ~proof:b.pbp ~expect:`Rejects "pol-coeff";
        mutation_lane c ~proof:b.pbp ~expect:`Rejects "pol-cite";
        mutation_lane c ~proof:b.pbp ~expect:(`Unevaluated drop_line_is_a_grammar_lane)
          "drop-line";
        emitter_lane c ~build:build_triple ~expect:`Rejects
          ~knob:(knob ~site:site_combine Writer.Mutation.Perturb_coefficient)
          "perturb-coefficient";
        emitter_lane c ~build:build_triple ~expect:`Rejects
          ~knob:(knob ~site:site_combine Writer.Mutation.Swap_citation)
          "swap-citation";
        (* What `drop-line` was for, done so that the checker has to answer it: the
           step keeps its label and loses its derivation. On root_unsat this was
           ACCEPTED and registered known-slack (D-0030); here the truncation leaves
           @c5, which is satisfiable, so the checker has to judge it. *)
        emitter_lane c ~build:build_triple ~expect:`Rejects
          ~knob:(knob ~site:site_combine Writer.Mutation.Truncate_derivation)
          "truncate-derivation");

    (* -- the same lanes on the wider D-0015 derivation ------------------------ *)
    let b, outcome = solve_to_proof ~dir ~name:"lin_unsat" lin_unsat in
    check "lin_unsat: the solver refutes it (the instance is what we think it is)"
      (outcome = Search.Unsat);
    let build_lin ~name ~mutation = fst (solve_to_proof ~mutation ~dir ~name lin_unsat) in
    gated ~tag:"lin_unsat"
      ~control:(fun () -> control_holds ~tag:"lin_unsat" ~proof:b.pbp)
      ~declares:
        [
          "pol-coeff";
          "pol-cite";
          "drop-line";
          "perturb-coefficient";
          "swap-citation";
          "truncate-derivation";
        ]
      (fun c ->
        mutation_lane c ~proof:b.pbp
          ~expect:(`Known_slack known_slack_lin_unsat_pol_coeff) "pol-coeff";
        mutation_lane c ~proof:b.pbp ~expect:`Rejects "pol-cite";
        mutation_lane c ~proof:b.pbp ~expect:(`Unevaluated drop_line_is_a_grammar_lane)
          "drop-line";
        (* Occurrence 1 is the first weakening `pol`, which is the step D-0020 is
           about: the emitter lane lands on the same site the text lane does, and
           finds the same slack. Registered, not silenced. *)
        emitter_lane c ~build:build_lin
          ~expect:(`Known_slack known_slack_lin_unsat_pol_coeff)
          ~knob:(knob ~site:site_combine Writer.Mutation.Perturb_coefficient)
          "perturb-coefficient";
        emitter_lane c ~build:build_lin ~expect:`Rejects
          ~knob:(knob ~site:site_combine Writer.Mutation.Swap_citation)
          "swap-citation";
        (* Occurrence 3 is the outer `pol`, the one `conclusion UNSAT` cites -- the
           step `drop-line` deletes, judged rather than parsed. *)
        emitter_lane c ~build:build_lin ~expect:`Rejects
          ~knob:
            (knob ~occurrence:3 ~site:site_combine Writer.Mutation.Truncate_derivation)
          "truncate-derivation");

    (* -- the clause lanes, on a fact that arrives under a decision ------------ *)
    let b = branch_trace ~dir () in
    let build_branch ~name ~mutation = branch_trace ~mutation ~name ~dir () in
    gated ~tag:"branch_trace"
      ~control:(fun () -> control_holds ~tag:"branch_trace" ~proof:b.pbp)
      ~declares:[ "rup-drop-lit"; "rhs-const"; "drop-literal"; "strengthen-rhs" ]
      (fun c ->
        mutation_lane c ~proof:b.pbp ~expect:`Rejects "rup-drop-lit";
        mutation_lane c ~proof:b.pbp ~expect:`Rejects "rhs-const";
        emitter_lane c ~build:build_branch ~expect:`Rejects
          ~knob:(knob ~site:site_branch_trace Writer.Mutation.Drop_literal)
          "drop-literal";
        emitter_lane c ~build:build_branch ~expect:`Rejects
          ~knob:(knob ~site:site_branch_trace Writer.Mutation.Strengthen_rhs)
          "strengthen-rhs");

    (* -- the real branch proof (D-0018 / M1-T13) ------------------------------ *)
    let b, outcome = solve_to_proof ~dir ~name:"chain" chain in
    check "chain: the solver solves it (the instance is what we think it is)"
      (match outcome with Search.Sat _ -> true | Search.Unsat -> false);
    (* "A decision level was opened" is spelled `# 1` in a 2.0 proof and `% level 1` in
       a 3.0 one, which has no set-level rule at all (D-0024). Looking only for `# 1`
       would make this check vacuously FALSE under 3.0 -- the mirror of the hazard
       PROOF-FORMAT section 5 warns about, and a test that stops testing is worse than
       one that fails. Accept either marker. *)
    let branched =
      let s = read_file b.pbp in
      let opens_a_level l =
        let starts p =
          String.length l >= String.length p && String.sub l 0 (String.length p) = p
        in
        starts "# 1" || starts "% level 1"
      in
      String.length s > 0 && List.exists opens_a_level (String.split_on_char '\n' s)
    in
    check "chain: the search really branched, so its proof is a branch-level one (D-0018)"
      branched;
    let build_chain ~name ~mutation = fst (solve_to_proof ~mutation ~dir ~name chain) in
    gated ~tag:"chain"
      ~control:(fun () -> control_holds ~tag:"chain" ~proof:b.pbp)
      ~declares:[ "rup-drop-lit"; "rhs-const"; "drop-literal"; "strengthen-rhs" ]
      (fun c ->
        mutation_lane c ~proof:b.pbp ~expect:`Rejects "rup-drop-lit";
        mutation_lane c ~proof:b.pbp ~expect:`Rejects "rhs-const";
        emitter_lane c ~build:build_chain ~expect:`Rejects
          ~knob:(knob ~site:site_chain_branch_claim Writer.Mutation.Drop_literal)
          "drop-literal";
        emitter_lane c ~build:build_chain ~expect:`Rejects
          ~knob:(knob ~site:site_chain_branch_claim Writer.Mutation.Strengthen_rhs)
          "strengthen-rhs");

    (* -- the harness's own guards -------------------------------------------- *)
    (* A mutation that rewrote nothing would make every lane green against the control's
       own proof. mutate_proof.sh calls that out rather than running veripb on an
       unchanged file; [Not_applicable] is the exit it uses, and it must not be 0. *)
    let r, out = run_lane ~proof:(branch_trace ~dir ()).pbp "pol-coeff" in
    check "harness: a mutation with no site reports not-applicable rather than passing"
      (r = Not_applicable);
    if r <> Not_applicable then show out;
    let r, out = run_lane ~proof:(branch_trace ~dir ()).pbp "no-such-mutation" in
    check "harness: an unknown mutation name is an error, not a pass"
      (match r with Broken 2 -> true | _ -> false);
    if match r with Broken 2 -> false | _ -> true then show out;

    (* The control is not a lane the caller may forget (M1-T26): mutate_proof.sh
       verifies the UNCORRUPTED proof inside every lane and refuses to report anything
       when that fails. Asserted by composing the two halves of the harness -- hand the
       script a proof the EMITTER has already corrupted, so the script's "honest" proof
       is not honest at all. It must report the control failure (exit 1), not a passing
       pol-cite lane. *)
    let already_corrupt =
      build_triple ~name:"control_guard"
        ~mutation:(knob ~site:site_combine Writer.Mutation.Perturb_coefficient)
    in
    check "harness: the emitter really did corrupt the control-guard instance"
      already_corrupt.fired;
    let r, out = run_lane ~proof:already_corrupt.pbp "pol-cite" in
    check
      "harness: a lane on an instance whose honest proof does not verify FAILS on the \
       control, rather than reporting the corruption"
      (r = Slack && contains out "UNCORRUPTED");
    if not (r = Slack && contains out "UNCORRUPTED") then show out;
    discard_kept_files out;

    (* A knob whose site matches nothing must not fire -- and the proof it leaves is
       then HONEST, which is exactly why every emitter lane asserts [fired] before it
       believes the checker. *)
    let missed =
      build_triple ~name:"no_site"
        ~mutation:(knob ~site:"no-such-derivation" Writer.Mutation.Perturb_coefficient)
    in
    check "harness: an emitter knob whose site matches nothing does not fire"
      (not missed.fired);
    let v, out = check_proof missed in
    check
      "harness: ... and the proof it leaves is honest, so a lane that ignored [fired] \
       would read this acceptance as slack"
      (v = Accepted);
    if v <> Accepted then show out;

    (* The banner is the other half of that: a proof [create] wrote never carries it. *)
    check "harness: an unmutated proof carries no corruption banner"
      (not (contains (read_file b.pbp) corruption_banner));

    (* And the knob cannot fire in a normal run because nothing in the shipped code can
       ask it to. [Writer.create_mutated] is the only door, it reads no environment
       variable, and no module under lib/ or bin/ names it. Asserted rather than
       asserted-in-a-comment: the day a propagator reaches for it "temporarily", this
       goes red. The writer is excluded because it is the definition site. *)
    (match script with
    | None -> ()
    | Some sh ->
        let root = Filename.dirname (Filename.dirname sh) in
        let rc =
          Sys.command
            (Printf.sprintf
               "grep -rn create_mutated %s %s --include=*.ml 2>/dev/null | grep -v \
                writer[.]ml > /dev/null"
               (Filename.quote (Filename.concat root "lib"))
               (Filename.quote (Filename.concat root "bin")))
        in
        check
          "harness: nothing under lib/ or bin/ names Writer.create_mutated, so no normal \
           run can arm a knob"
          (rc <> 0));

    (* The corrupted proofs are the ones we expected to be bad, so they are thrown away
       on success and kept when there is something to look at -- GCS's rule, and
       mutate_proof.sh keeps its own copies under the same one. *)
    if !failures = 0 && Sys.getenv_opt "BAGUETTE_PRESERVE_PROOF_FILES" <> Some "1" then (
      Array.iter
        (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
        (Sys.readdir dir);
      try Sys.rmdir dir with _ -> ())
    else Printf.printf "note: the instances are kept at %s\n" dir

let () =
  print_endline "";
  (match script with Some s -> Printf.printf "* harness: %s\n" s | None -> ());
  run ();
  Printf.printf "\n%d mutation checks" !checks;
  if !failures > 0 then (
    Printf.printf ", %d failure(s)\n" !failures;
    exit 1)
  else print_endline ", all passed"
