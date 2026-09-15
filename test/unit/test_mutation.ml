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
      for the wrong reason. [root_unsat] below closes at `0 >= 1` and is the instance
      the `pol` lanes gate on. [lin_unsat] closes at `0 >= 2` and is registered as
      known-slack for exactly this reason -- see [known_slack] and the comment there.
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
   currently emits. [chain]'s own lanes are guarded on its control lane: if the
   branch-level proof stops verifying, they report as waiting rather than failing, and
   they come back on their own. Nothing here needs editing either way. *)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding
module Var = Baguette_core.Var
module Domain = Baguette_core.Domain
module Store = Baguette_core.Store
module Propagator = Baguette_core.Propagator
module Linear = Baguette_core.Linear
module Engine = Baguette_core.Engine
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify

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
  | Held (* veripb rejected the corruption, or accepted the control *)
  | Slack (* veripb ACCEPTED a corrupted proof, or rejected the control *)
  | Not_applicable (* no site for this mutation in this proof *)
  | No_checker (* veripb (or the script) missing: nothing was checked *)
  | Broken of int (* usage or internal error in the harness *)

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
        | n -> Broken n),
        out )

(* The control lane. Returns whether it held, so that an instance whose honest proof
   does not verify is reported as such rather than having meaningless lanes run on it. *)
let control_lane ~tag ~proof =
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

(* A mutation lane.

   [expect] is [`Rejects] for a lane that holds, or [`Known_slack why] for one where
   veripb is known to ACCEPT the corruption. A known-slack lane is recorded the way
   test/models/PENDING records a known failure: reported on every run so it cannot be
   forgotten, and if it starts holding the suite goes red telling you to delete the
   marker. That is what stops the list rotting into a list of quietly broken things --
   and it is not a weakened test: the lane still runs and its result is still asserted,
   only against the outcome that was actually measured and recorded. *)
let mutation_lane ~tag ~proof ?nth ~expect mutation =
  let name = Printf.sprintf "%s/%s" tag mutation in
  let r, out = run_lane ?nth ~proof mutation in
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

(* Lanes on an instance whose honest proof does not verify yet. Reported, never
   counted, never red: the point is that they light up on their own when it does. *)
let waiting_lanes ~tag ~why lanes =
  Printf.printf "wait %s/control: %s\n" tag why;
  List.iter
    (fun m ->
      Printf.printf
        "wait %s/%s: not run -- it activates by itself once the control lane above passes\n"
        tag m)
    lanes

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

(* Solve [m] through the real pipeline -- the same one test_endtoend.ml drives -- and
   leave the .opb/.pbp pair behind for the harness to corrupt. These are the solver's
   own proofs, not transcriptions of them, so a lane cannot go stale against a
   derivation that changed underneath it. *)
let solve_to_proof ~dir ~name m =
  let opb = Filename.concat dir (name ^ ".opb") in
  let pbp = Filename.concat dir (name ^ ".pbp") in
  let store =
    Store.create
      ~names:(Array.map (fun (n, _, _) -> n) m.vars)
      ~domains:(Array.map (fun (_, lo, hi) -> Domain.make lo hi) m.vars)
  in
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
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "test_mutation: " ^ name ] enc oc;
  close_out oc;
  let oc = open_out pbp in
  let writer = Writer.create ~comments:false ~audit:true oc in
  Encoding.start_proof enc writer;
  let ctx =
    Justify.create ~writer ~encoding:enc ~model_id:(fun () ->
        failwith "test_mutation: search demanded Explanation.Trivial")
  in
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
  (pbp, outcome)

(* -- root_unsat -----------------------------------------------------------------
   test/models/trivial_unsat.fzn's model: x in 1..3 with x <= 0. Propagation refutes
   it at level 0 and the whole proof is one `pol` over the model row plus two order-
   encoding axioms, closing at `0 >= 1`.

   The MARGIN IS ONE, which is the entire reason this instance rather than a bigger
   one carries the `pol` lanes (trap 1). Any single unit of energy taken out of, or
   put into, that `pol` and the result stops being a contradiction. *)
let root_unsat = { vars = [| ("x", 1, 3) |]; rows = [ ([ (1, 0) ], 0) ] }

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
let branch_trace ~dir =
  let opb = Filename.concat dir "branch_trace.opb" in
  let pbp = Filename.concat dir "branch_trace.pbp" in
  let enc = Encoding.create () in
  Encoding.declare_int enc "x" ~lo:0 ~hi:2;
  Encoding.declare_int enc "y" ~lo:0 ~hi:2;
  let _row = Encoding.add_int_lin_le enc [ (-1, "x"); (-1, "y") ] (-3) in
  let oc = open_out opb in
  Encoding.write_opb ~comments:[ "test_mutation: branch_trace (M1-T15)" ] enc oc;
  close_out oc;
  let oc = open_out pbp in
  let w = Writer.create ~comments:false ~audit:true oc in
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
  pbp

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
   than assumed. The `pol` lanes gate on root_unsat, whose margin is one; this lane \
   stays registered so the slack is reported on every run"

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

    (* -- the pol lanes, on the margin-one instance ---------------------------- *)
    let proof, outcome = solve_to_proof ~dir ~name:"root_unsat" root_unsat in
    check "root_unsat: the solver refutes it (the instance is what we think it is)"
      (outcome = Search.Unsat);
    if control_lane ~tag:"root_unsat" ~proof then (
      mutation_lane ~tag:"root_unsat" ~proof ~expect:`Rejects "pol-coeff";
      mutation_lane ~tag:"root_unsat" ~proof ~expect:`Rejects "pol-cite";
      mutation_lane ~tag:"root_unsat" ~proof ~expect:`Rejects "drop-line");

    (* -- the same lanes on the wider D-0015 derivation ------------------------ *)
    let proof, outcome = solve_to_proof ~dir ~name:"lin_unsat" lin_unsat in
    check "lin_unsat: the solver refutes it (the instance is what we think it is)"
      (outcome = Search.Unsat);
    if control_lane ~tag:"lin_unsat" ~proof then (
      mutation_lane ~tag:"lin_unsat" ~proof
        ~expect:(`Known_slack known_slack_lin_unsat_pol_coeff) "pol-coeff";
      mutation_lane ~tag:"lin_unsat" ~proof ~expect:`Rejects "pol-cite";
      mutation_lane ~tag:"lin_unsat" ~proof ~expect:`Rejects "drop-line");

    (* -- the clause lanes, on a fact that arrives under a decision ------------ *)
    let proof = branch_trace ~dir in
    if control_lane ~tag:"branch_trace" ~proof then (
      mutation_lane ~tag:"branch_trace" ~proof ~expect:`Rejects "rup-drop-lit";
      mutation_lane ~tag:"branch_trace" ~proof ~expect:`Rejects "rhs-const");

    (* -- the real branch proof, once M1-T13 makes one verify ------------------ *)
    let proof, outcome = solve_to_proof ~dir ~name:"chain" chain in
    check "chain: the solver solves it (the instance is what we think it is)"
      (match outcome with Search.Sat _ -> true | Search.Unsat -> false);
    let branched =
      let s = read_file proof in
      String.length s > 0
      && List.exists
           (fun l -> String.length l >= 3 && String.sub l 0 3 = "# 1")
           (String.split_on_char '\n' s)
    in
    check "chain: the search really branched, so its proof is a branch-level one (D-0018)"
      branched;
    let clause_lanes = [ "rup-drop-lit"; "rhs-const" ] in
    let r, _ = run_lane ~proof "control" in
    if r = Held then (
      Printf.printf
        "note chain: the branch-level proof verifies, so the clause lanes below run on a \
         real branch nogood and a real trace line (D-0018), not only on branch_trace's \
         hand-built stand-in.\n";
      List.iter
        (fun m -> mutation_lane ~tag:"chain" ~proof ~expect:`Rejects m)
        clause_lanes)
    else
      waiting_lanes ~tag:"chain"
        ~why:
          "the branch-level proof does not verify (D-0018 / M1-T13). While that is so, \
           branch_trace above is the only instance carrying the clause lanes"
        clause_lanes;

    (* -- the harness's own guards -------------------------------------------- *)
    (* A mutation that rewrote nothing would make every lane green against the control's
       own proof. mutate_proof.sh calls that out rather than running veripb on an
       unchanged file; [Not_applicable] is the exit it uses, and it must not be 0. *)
    let r, out = run_lane ~proof:(branch_trace ~dir) "pol-coeff" in
    check "harness: a mutation with no site reports not-applicable rather than passing"
      (r = Not_applicable);
    if r <> Not_applicable then show out;
    let r, out = run_lane ~proof:(branch_trace ~dir) "no-such-mutation" in
    check "harness: an unknown mutation name is an error, not a pass"
      (match r with Broken 2 -> true | _ -> false);
    if match r with Broken 2 -> false | _ -> true then show out;

    (* The corrupted proofs are the ones we expected to be bad, so they are thrown away
       on success and kept when there is something to look at -- GCS's rule, and
       mutate_proof.sh keeps its own copies under the same one. *)
    if !failures = 0 then (
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
