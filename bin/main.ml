(* The baguette CLI.
     baguette MODEL.fzn [--proof PREFIX] [--proof-comments] [--all] [--time]

   docs/ARCHITECTURE.md gives this file one job -- "parse args, wire everything, print
   results" -- and the wiring is the whole of M1-T14. Everything below it already
   worked; none of it was reachable from a command line, which is why all five models
   in test/models/ were xfail while the engine underneath them solved and emitted
   proofs veripb accepted.

   The pipeline, in the order it must happen:

     Builder.of_file   .fzn text            -> Model.t
     Compile.compile   Model.t              -> store, engine, encoding
     Encoding.write_opb                     -> PREFIX.opb        (I-X5: before the proof
                                                                  references it)
     Encoding.start_proof                   -> the proof's `f N` header
     Search.solve                           -> Sat assignment | Unsat, proof written
     Output.solution / Output.unsatisfiable -> stdout, SPEC 2.2

   Two things here are less obvious than they look.

   **The variable-index bridge.** [Search.assignment] is a [(Var.t * int) list] over the
   solver's own variable identities; [Model.check_assignment] and [Output.solution] both
   want an [int array] indexed by *model* variable index. Those two index spaces coincide
   only because [Compile.compile] builds the store in [Model.vars] order and promises to
   keep doing so. [assignment_values] below is where they meet, and it re-checks the
   promise rather than assuming it: an off-by-one here would print a wrong answer that
   the independent check (I-S1) would then happily confirm, because it would be checking
   the same permuted array.

   **A proof is written even without --proof.** [Search.solve] needs a [Justify.ctx],
   which needs a [Writer.t], which needs a channel; there is no "solve without logging"
   mode and docs/SPEC.md 1 is explicit that there should not be one ("The proof is not a
   debugging aid. It is a primary output"). Without --proof the proof is written to a
   temporary file and deleted, so the work -- and the audit -- still happens and the run
   still fails loudly if the solver cannot justify itself. It is the file that is
   optional, not the proof.

   **The .opb comment names the model's BASENAME, not the path it was given** (M1-T37).
   `.opb` bytes are the one column M3-T5 found trustworthy at every row, and while the
   header read `"baguette: " ^ opts.model` that column was not a property of the model at
   all: the same file measured as `test/models/x.fzn` and as `/tmp/x.fzn` produced .opb
   files ~16 bytes apart, so two people's byte counts could legitimately disagree about
   the same model. The basename is kept rather than the comment dropped because a human
   holding a .opb and a .pbp in a temp directory still needs to know which model they
   belong to, and the *directory* is the one part of the path that person already knows:
   they typed it. bench/run_bench.sh checks this property on every run -- see
   `opb_path_independence` there -- so the dependence cannot come back unnoticed. *)

module Model = Baguette_flatzinc.Model
module Builder = Baguette_flatzinc.Builder
module Compile = Baguette_flatzinc.Compile
module Output = Baguette_flatzinc.Output
module Fz_error = Baguette_flatzinc.Error
module Var = Baguette_core.Var
module Store = Baguette_core.Store
module Search = Baguette_core.Search
module Justify = Baguette_core.Justify
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding
module Checked = Baguette_core.Checked

type options = {
  model : string;
  proof_prefix : string option;
  proof_comments : bool;
  all_solutions : bool;
  time : bool;
  stats : bool;
}

(* Exit codes. 0 covers both SAT and UNSAT: an UNSAT model is a successful run that
   proved something, not a failure, and scripts/run_model_tests.sh reads a non-zero exit
   as the solver having fallen over. *)
let exit_ok = 0
let exit_usage = 2
let exit_unsupported = 3
let exit_internal = 4

let usage () =
  prerr_endline
    "usage: baguette MODEL.fzn [--proof PREFIX] [--proof-comments] [--all] [--time] \
     [--stats]";
  prerr_endline "";
  prerr_endline "  --proof PREFIX    write PREFIX.opb and PREFIX.pbp (SPEC 4.1); verify";
  prerr_endline "                    them with: veripb PREFIX.opb PREFIX.pbp";
  prerr_endline "  --proof-comments  enable the proof writer's comment lines. As of M1,";
  prerr_endline "                    no shipped model reaches a call site that emits one,";
  prerr_endline "                    so this flag is currently a no-op on every model in";
  prerr_endline "                    test/models/: .opb and .pbp are byte-identical with";
  prerr_endline "                    and without it. It will start mattering once the";
  prerr_endline "                    direct-encoding path (M4) lands (see M1-T48).";
  prerr_endline "  --all             every solution, not just the first (not implemented)";
  prerr_endline "  --time            phase-by-phase CPU timings, ON STDERR, one `time: `";
  prerr_endline "                    line each. Off by default; stdout is byte-identical";
  prerr_endline "                    with and without it (SPEC 2.2). Read what each phase";
  prerr_endline "                    does and does not contain before quoting a number:";
  prerr_endline "                    the report says so on every line.";
  prerr_endline "  --stats           search-tree counters, ON STDERR, one `stats: ` line";
  prerr_endline "                    each (M1-T36): nodes visited, decisions taken, tree";
  prerr_endline "                    depth. Counted by the search, NOT read back out of";
  prerr_endline "                    the proof -- so it is available without --proof and";
  prerr_endline "                    it does not move when the proof's shape does. It is";
  prerr_endline "                    three int increments per node and no clock reads, so";
  prerr_endline "                    unlike --time it is safe to leave on while timing.";
  prerr_endline "                    stdout is byte-identical with and without it.";
  prerr_endline "";
  prerr_endline "  BAGUETTE_PROOF_AUDIT=0 disables the constraint-id audit (I-X2), which";
  prerr_endline "  is on by default here even though the library's own default is off.";
  exit exit_usage

let parse_args argv =
  let model = ref None in
  let proof_prefix = ref None in
  let proof_comments = ref false in
  let all_solutions = ref false in
  let time = ref false in
  let stats = ref false in
  let rec go i =
    if i >= Array.length argv then ()
    else
      match argv.(i) with
      | "--proof" ->
          if i + 1 >= Array.length argv then usage ();
          proof_prefix := Some argv.(i + 1);
          go (i + 2)
      | "--proof-comments" ->
          proof_comments := true;
          go (i + 1)
      | "--all" ->
          all_solutions := true;
          go (i + 1)
      | "--time" ->
          time := true;
          go (i + 1)
      | "--stats" ->
          stats := true;
          go (i + 1)
      | "-h" | "--help" -> usage ()
      | arg when String.length arg > 0 && arg.[0] = '-' ->
          Printf.eprintf "unknown option: %s\n" arg;
          usage ()
      | arg ->
          if !model <> None then usage ();
          model := Some arg;
          go (i + 1)
  in
  go 1;
  match !model with
  | None -> usage ()
  | Some m ->
      {
        model = m;
        proof_prefix = !proof_prefix;
        proof_comments = !proof_comments;
        all_solutions = !all_solutions;
        time = !time;
        stats = !stats;
      }

(* --------------------------------------------------------- timing (M1-T35) *)

(* Why this exists. M3-T5 measured a process floor of 4.0 ms to start this binary and
   4.6 ms to start the checker, and then found 15 of the 18 models in the suite sitting
   AT that floor with 9-66% spread. Their "solve ms" column is a timing of `exec`, not
   of this solver, and until the solver could report its own numbers no timing claim
   about it was supportable from the model suite in either direction -- which is why
   bench/README.md says D-0026's falsifier cannot be run.

   ---------------------------------------------------------------------------
   The clock is CPU time, not wall time
   ---------------------------------------------------------------------------

   [Sys.time] is the only clock reachable from here: bin/dune links baguette_core,
   baguette_proof and baguette_flatzinc and nothing else, `unix` is not among them, and
   dune files are not this task's to edit. That turns out to be the better instrument
   rather than a compromise, and both halves of that were measured on this switch rather
   than assumed:

     * RESOLUTION. The smallest non-zero delta of [Sys.time] over 2000 consecutive
       samples is exactly 1e-6 s. It is NOT the 10 ms CLK_TCK granularity of times(2)
       that [Sys.time] used to have; this runtime reaches clock_gettime.
     * WHAT IT COUNTS. CLOCK_PROCESS_CPUTIME_ID: user + system CPU consumed by this
       process since the process was created. So it EXCLUDES every moment the process
       spent off the CPU -- descheduled behind another session's `dune build`, or
       blocked on I/O -- which is precisely the noise bench/README.md warns about; and
       it INCLUDES the CPU burned before OCaml ever reached this file, which is what
       makes [startup] below measurable at all.
     * THE ALTERNATIVE WAS WORSE. /proc/self/schedstat reports nanoseconds and looks
       finer. Measured here, its smallest non-zero delta is 1.9 ms, because the
       scheduler only updates it at its own tick. It cannot see a 400 us parse.

   Two consequences, to be repeated wherever these numbers are quoted:

   1. A CPU number and a wall number are different measurements. On a busy machine CPU
      is BELOW wall and the difference is time the process was not running; it is not an
      error bar and the two must not be averaged.
   2. [startup] IS process start-up. It is reported so that it can be subtracted, not
      folded in. D-0023 and D-0025 are both retractions of speed claims, and the way to
      avoid a third is to publish the contaminated part as its own number.

   ---------------------------------------------------------------------------
   What [search] used to fuse, and what it still does (M1-T47)
   ---------------------------------------------------------------------------

   [search] used to be propagation, search AND the proof lines emitted during them,
   with no way to tell them apart from here: every emission point is below
   [Search.solve]. M1-T47 put the accumulator where the emission actually happens --
   [Writer.emitted_us], around the writer's own output calls -- so [search] now splits
   into two reported rows, [emit] and [propag].

   THEY ARE BOUNDS, NOT FIGURES, and the reason is specific rather than ritual.
   [Writer] accumulates the time it spends WRITING a line; the time spent BUILDING
   that line's body -- Pol.to_string_cited, Opb.constr_to_string, the Printf.sprintf
   at each rule's call site -- is spent before the writer's output call is entered and
   is not in [emit]. So:

     emit   is a LOWER bound on what proof emission costs during the search;
     propag is search - emit, an UPPER bound on what propagation and search cost.

   Two more things travel with them. [emit] is measured with the same [Sys.time] as
   every other row, which costs ~0.72 us per read here, so [emit] carries about one
   clock read per emitted line of its own overhead and [search] carries two; the row
   [emitln] is the line count the correction is computed from, and the report prints
   it. And the clock inside the writer is only running under --time, so a run without
   this flag pays one bool dereference per line and nothing else.

   The two proof-emission phases that were ALREADY separable from here are still
   separate, and on the wide models they are the larger half: building and writing the
   .opb ([opb]) and flushing the .pbp ([pbpclose]). *)

module Timing = struct
  (* Process CPU microseconds. See the note above for what that does and does not
     count. *)
  let now () = int_of_float ((Sys.time () *. 1_000_000.) +. 0.5)
  let on = ref false
  let main_start = ref 0
  let startup = ref 0
  let phases : (string * int) list ref = ref []
  let record name us = if !on then phases := (name, us) :: !phases

  (* M1-T47. Derived rows: they are a SPLIT of [search], not phases of their own, so
     they are deliberately not in [phases] -- putting them there would make the sum
     that produces [other] count the search twice. [emit_lines] is a count, not a
     duration, and is printed with a `lines` unit so that nothing reading `$4 == "us"`
     picks it up as a timing. *)
  let emit_us = ref 0
  let emit_lines = ref 0
  let have_emit = ref false

  (* The cost of ONE [Sys.time] read, in nanoseconds, measured on this machine under
     this load rather than taken from a table. It is what [emit] and [propag] each
     carry once per emitted line, and on a 545-line proof it is half of [emit] -- far
     too large to leave folded in silently.

     Called from [report], AFTER every number the report prints has been taken, so the
     ~0.4 ms it costs lands in no phase and contaminates nothing. That placement is
     the whole reason this is a function and not a constant: a calibration run before
     the solve would show up in `rest` and move the very table it exists to correct.

     MINIMUM OF BURSTS, NOT A MEAN, for the reason bench/README.md section 2 gives for
     every other number in this project: a mean folds in whatever else the machine was
     doing, and four sessions build on this one. A single 512-read burst was tried
     first and ranged 836..1871 ns across five consecutive runs of the same model --
     which would have made the published correction swing by a factor of two. Nine
     bursts of 256, minimum taken, holds inside a few percent. *)
  let clock_tick_ns () =
    let n = 256 and bursts = 9 in
    let best = ref max_int in
    for _ = 1 to bursts do
      let t0 = Sys.time () in
      for _ = 1 to n do
        ignore (Sys.time ())
      done;
      let t1 = Sys.time () in
      let ns = int_of_float (((t1 -. t0) *. 1e9 /. float_of_int n) +. 0.5) in
      if ns < !best then best := ns
    done;
    !best

  (* Free when timing is off: one dereference and the call itself. A phase whose body
     raises records nothing, which is why the report prints an `other` row instead of
     pretending the rows always add up. *)
  let phase name f =
    if not !on then f ()
    else
      let t0 = now () in
      let r = f () in
      record name (now () - t0);
      r

  (* The descriptions live here, once, rather than at the call sites, because they are
     the part a reader must have in front of them before quoting a number. *)
  let describe = function
    | "startup" ->
        "CPU before main's first statement: exec, dynamic link, OCaml runtime, module \
         init"
    | "args" -> "argument parsing, the file-exists check and the --all check"
    | "parse" -> "Builder.of_file: lex, parse, build Model.t"
    | "compile" -> "Compile.compile: store, engine, encoding -- no I/O, no proof"
    | "opb" ->
        "Encoding.write_opb: the .opb built, written and closed (0 without --proof)"
    | "proofopen" -> "proof channel opened, Writer.create, Encoding.start_proof"
    | "search" -> "Search.solve: propagation, search and proof emission together"
    | "emit" ->
        "of `search`: inside Writer's output calls. LOWER bound -- excludes building \
         each line"
    | "propag" ->
        "of `search`: search - emit. UPPER bound on propagation and search themselves"
    | "clockovh" ->
        "this instrument's own cost: charged ONCE to `emit` and ONCE to `propag`. \
         Subtract it"
    | "pbpclose" -> "the .pbp flushed and closed (and removed, without --proof)"
    | "output" -> "Output.solution rendered, printed and flushed to stdout"
    | "other" -> "inside main but outside every phase above (dispatch, diagnostics)"
    | "inmain" -> "main's first statement to here: every row above except startup"
    | "process" -> "startup + inmain: all CPU this process has consumed, to here"
    | other -> other

  let row name us = Printf.eprintf "time: %-10s %10d us  %s\n" name us (describe name)

  (* Installed with at_exit, so it is written on every path that reaches [exit] --
     including the diagnostics, where the phases that did run are still worth having.
     STDERR ONLY. SPEC 2.2 pins stdout byte for byte and nothing here may appear
     there. *)
  let report () =
    if !on then (
      let in_main = now () - !main_start in
      (* Calibrated here and nowhere earlier: see [clock_tick_ns]. *)
      let tick_ns = if !have_emit then clock_tick_ns () else 0 in
      let ps = List.rev !phases in
      let summed = List.fold_left (fun a (_, us) -> a + us) 0 ps in
      prerr_endline
        "time: baguette internal timings (M1-T35). CPU microseconds from Sys.time:";
      prerr_endline
        "time: user+system CPU of THIS PROCESS, so below wall time by whatever the";
      prerr_endline "time: machine spent not running it. stderr only, never stdout.";
      row "startup" !startup;
      List.iter
        (fun (n, us) ->
          row n us;
          if n = "search" && !have_emit then (
            row "emit" !emit_us;
            row "propag" (us - !emit_us);
            row "clockovh" (!emit_lines * tick_ns / 1000);
            Printf.eprintf "time: %-10s %10d lines  %s\n" "emitln" !emit_lines
              "proof lines written during `search`: what `clockovh` is computed from"))
        ps;
      row "other" (in_main - summed);
      row "inmain" in_main;
      row "process" (!startup + in_main);
      if !have_emit then (
        prerr_endline
          "time: `search` splits into `emit` and `propag` (M1-T47). BOTH ARE BOUNDS:";
        prerr_endline
          "time: `emit` is time inside Writer's output calls and EXCLUDES building each";
        prerr_endline
          "time: line's body at its call site, so it is a lower bound on emission and";
        prerr_endline "time: `propag` is an upper bound on propagation.";
        Printf.eprintf
          "time: AND BOTH INCLUDE `clockovh`: Sys.time measured %d ns a read here, one\n"
          tick_ns;
        prerr_endline
          "time: read per emitted line landing in each. Subtract it from both. `search`";
        prerr_endline
          "time: itself is 2 x clockovh above what the same run costs without --time.")
      else
        prerr_endline
          "time: `search` INCLUDES the proof lines written during it: no writer was \
           opened.";
      prerr_endline "time: note above module Timing in bin/main.ml before quoting these.")
end

(* --------------------------------------------------------- the index bridge *)

(* [Search.assignment] to a [Model.vars]-indexed array. The two index spaces agree by
   construction (see Compile's header) and this is the one place that depends on it, so
   this is where it is checked rather than assumed: every model variable must be
   assigned exactly once, and the store must agree about its name. *)
let assignment_values m store (assignment : Search.assignment) =
  let n = Model.nvars m in
  let values = Array.make n 0 in
  let seen = Array.make n false in
  List.iter
    (fun (v, value) ->
      let i = Var.to_int v in
      if i < 0 || i >= n then
        failwith
          (Printf.sprintf "solver variable %d is outside the model's %d variables" i n);
      let declared = (Model.var m i).Model.v_name in
      let in_store = Store.name store v in
      if not (String.equal declared in_store) then
        failwith
          (Printf.sprintf
             "variable index %d is %S in the model and %S in the store -- Compile must \
              build the store in Model.vars order"
             i declared in_store);
      seen.(i) <- true;
      values.(i) <- value)
    assignment;
  Array.iteri
    (fun i s ->
      if not s then
        failwith
          (Printf.sprintf "variable %S (index %d) was not assigned"
             (Model.var m i).Model.v_name i))
    seen;
  values

(* ------------------------------------------------------------------ running *)

(* The proof channel, plus how to finish with it. Without --proof it is a temporary
   file that is removed afterwards: see the header. *)
let open_proof_channel opts =
  match opts.proof_prefix with
  | Some prefix ->
      let path = prefix ^ ".pbp" in
      (open_out path, fun () -> ())
  | None -> (
      let path = Filename.temp_file "baguette" ".pbp" in
      (open_out path, fun () -> try Sys.remove path with Sys_error _ -> ()))

let audit_enabled () =
  (* The library defaults this off and turns it on with BAGUETTE_PROOF_AUDIT=1
     (docs/ARCHITECTURE.md section 6). The CLI inverts that default deliberately: I-X2
     is cheap at these sizes, it has already caught one real defect (D-0015), and a user
     running the solver should get the check without having known to ask for it. *)
  match Sys.getenv_opt "BAGUETTE_PROOF_AUDIT" with Some "0" -> false | _ -> true

(* --------------------------------------------------- search-tree counters (M1-T36) *)

(* [Search.stats] rendered on stderr, one `stats: ` line each, under --stats.

   WHY THIS IS NOT FOLDED INTO --time. The two instruments cost different things and
   must be separable for that reason. --time takes a [Sys.time] per phase and one per
   emitted proof line, and bench/run_bench.sh therefore runs it on its own dedicated
   repeats so that none of it lands in a number printed as "solve ms" (M1-T47). This
   costs three int increments per node and no clock reads, so it can be left on during
   a timed run -- which is the whole point: the tree size and the time have to be
   readable off the SAME run before "the same tree costs no more" (D-0026) means
   anything.

   STDERR ONLY, like the timings, because SPEC 2.2 pins stdout byte for byte.

   The unit word is the third field and it is `nodes`/`decs`/`levels`, never `us`, so
   that anything reading the timing report's `$4 == "us"` cannot pick these up as
   durations -- the same discipline `emitln` follows with its `lines` unit. *)
let report_stats (st : Search.stats) (outcome : Search.outcome) =
  let exhausted = match outcome with Search.Unsat -> true | Search.Sat _ -> false in
  prerr_endline
    "stats: baguette search-tree counters (M1-T36). Counted by Search itself, not read";
  prerr_endline
    "stats: back out of the proof: available without --proof, and unmoved by a change";
  prerr_endline "stats: to the proof's shape. stderr only, never stdout.";
  Printf.eprintf "stats: %-10s %10d nodes  %s\n" "nodes" st.Search.nodes
    "search-tree nodes visited: the root, plus every child Search.branch dispatched";
  Printf.eprintf "stats: %-10s %10d decs   %s\n" "decisions" st.Search.decisions
    "decisions taken: one per internal node (Search.branch calls)";
  Printf.eprintf "stats: %-10s %10d levels %s\n" "maxdepth" st.Search.max_depth
    "deepest decision stack reached: the depth of the TREE, not of the proof";
  Printf.eprintf "stats: %-10s %10d %-6s %s\n" "exhausted"
    (if exhausted then 1 else 0)
    "bool" "1 if the search closed its whole tree (UNSAT), 0 if it stopped at a solution";
  (* The identity these counters have to satisfy, stated above [Search.stats] and
     checked here on every --stats run rather than only under BAGUETTE_DEBUG. Binary
     branching with every push landing means an exhausted tree visits both sides of
     every decision. If this line ever prints, one of the counters is counting the
     wrong event and no number above may be quoted. *)
  Printf.eprintf "stats: %-10s %10d nodes  %s\n" "skipped" st.Search.skipped
    "siblings NOT explored: one per backjump (M2-L3). 0 means no backjump happened";
  Printf.eprintf "stats: %-10s %10d cls    %s\n" "learned" st.Search.n_learned
    "1UIP clauses derived and put on the page, level 0 (M2-L3, D-0044 fork ii)";
  Printf.eprintf "stats: %-10s %10d cls    %s\n" "convertible" st.Search.n_converts
    "...of which Learned.to_linear_row would accept, i.e. could propagate. MEASURED ONLY";
  Printf.eprintf "stats: %-10s %10d lits   %s\n" "minimised" st.Search.n_min_dropped
    "literals semantic minimisation removed from nogoods (M2-L3); 0 means it never fired";
  Printf.eprintf "stats: %-10s %10d lines  %s\n" "i-s4-cross" st.Search.i_s4_crossings
    "hole lines above level 0 a level-0 learned clause rests on -- data, not a fault";
  (* M2-L6. [pb-fallback] is the one to read first: the clause path is PERMANENT
     (D-0044), so a build in which PB analysis never succeeded would be green in every
     other counter here. A rate of 1.00 means the PB path did nothing on this model. *)
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "pb-tried" st.Search.n_pb_attempts
    "conflicts PB conflict analysis was asked about (M2-L6)";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-learned" st.Search.n_pb_learned
    "...of which yielded a PB inequality, derived by pol and stated, at level 0";
  Printf.eprintf "stats: %-10s %10d confl  %s (%.2f)\n" "pb-fallback"
    st.Search.n_pb_fallback
    "...of which fell back to the M2-L3 clause path -- rate in brackets"
    (Search.stats_pb_fallback_rate st);
  if Search.stats_pb_fallbacks st <> [] then
    Printf.eprintf "stats: %-10s %10s        first fallback reason: %s\n" "pb-why" ""
      (List.hd (Search.stats_pb_fallbacks st));
  Printf.eprintf "stats: %-10s %10d pivots %s\n" "pb-steps" st.Search.n_pb_steps
    "pivots eliminated by linear combination + reduction, over all analyses";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-convert" st.Search.n_pb_converts
    "...learned PB rows Learned.to_linear_row accepts, i.e. which could propagate";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-stronger" st.Search.n_pb_stronger
    "...of those, where the SAME conflict's clause does NOT convert. M2-L6 test (a)";
  if Search.stats_i_s4_broken st <> [] then
    Printf.eprintf "stats: I-S4 VIOLATED %d time(s); first: %s\n"
      (List.length (Search.stats_i_s4_broken st))
      (List.hd (Search.stats_i_s4_broken st));
  (* The identity, now with M2-L3's one extra term. See [Search.stats_consistent]. *)
  if not (Search.stats_consistent st ~exhausted) then
    Printf.eprintf
      "stats: INCONSISTENT -- nodes=%d is not %s 2 * decisions + 1 - skipped = %d. The \
       counters are wrong; do not quote them (M1-T36, M2-L3).\n"
      st.Search.nodes
      (if exhausted then "=" else "<=")
      (Search.stats_expected_nodes st)

let solve opts (m : Model.t) =
  let compiled = Timing.phase "compile" (fun () -> Compile.compile m) in
  let store = compiled.Compile.store in
  let encoding = compiled.Compile.encoding in
  (* I-X5: the .opb is complete and on disk before any proof rule can cite it. The
     comment names the BASENAME, not the path -- M1-T37, see this file's header. *)
  Timing.phase "opb" (fun () ->
      match opts.proof_prefix with
      | Some prefix ->
          let oc = open_out (prefix ^ ".opb") in
          Encoding.write_opb
            ~comments:[ "baguette: " ^ Filename.basename opts.model ]
            encoding oc;
          close_out oc
      | None -> ());
  let proof_oc, cleanup, ctx =
    Timing.phase "proofopen" (fun () ->
        let proof_oc, cleanup = open_proof_channel opts in
        let writer =
          Writer.create ~comments:opts.proof_comments ~audit:(audit_enabled ()) proof_oc
        in
        Encoding.start_proof encoding writer;
        (* Every propagator instance carries its own row id (D-0011/D-0015). This used
           to install a [model_id] thunk that raised, because [Explanation.Trivial]
           could still reach the proof layer and there was no honest way to guess
           which row it meant. M1-T31 removed the field: there is no ambient row to
           install, so there is nothing to guard here. *)
        let ctx = Justify.create ~writer ~encoding in
        (proof_oc, cleanup, ctx))
  in
  let check assignment =
    Model.check_assignment m (assignment_values m store assignment)
  in
  (* M1-T36. Always allocated and always threaded: the counters cost three increments
     per node whether or not anyone asks to see them, and a counter that is only wired
     up under a flag is a counter no test exercises. --stats decides whether it is
     PRINTED, not whether it is kept. *)
  let stats = Search.stats_create () in
  let outcome =
    Fun.protect
      ~finally:(fun () ->
        Timing.phase "pbpclose" (fun () ->
            close_out proof_oc;
            cleanup ()))
      (fun () ->
        Timing.phase "search" (fun () ->
            (* M1-T47. Writer's accumulator is process-wide and cumulative -- it has
               already counted Encoding.start_proof, which ran in [proofopen] -- so
               what belongs to [search] is the DIFFERENCE across this call and not the
               total. Sampled inside the phase so that the two brackets nest. *)
            let e0 = Writer.emitted_us () and l0 = Writer.emitted_lines () in
            let r =
              Search.solve ~engine:compiled.Compile.engine ~store ~ctx ~check ~stats ()
            in
            Timing.emit_us := Writer.emitted_us () - e0;
            Timing.emit_lines := Writer.emitted_lines () - l0;
            Timing.have_emit := true;
            r))
  in
  (* [flush stdout] is inside the phase on purpose: the runtime would flush at exit
     anyway, after at_exit has already printed the report, and a number called "output"
     that excluded the write would be measuring string building only. It changes no
     byte of what is written. *)
  Timing.phase "output" (fun () ->
      (match outcome with
      | Search.Sat assignment ->
          print_string (Output.solution m (assignment_values m store assignment))
      | Search.Unsat -> print_string Output.unsatisfiable);
      flush stdout);
  if opts.stats then report_stats stats outcome

(* --------------------------------------------------------------------- main *)

let () =
  (* One [Sys.time] read, unconditionally, because --time has not been parsed yet and
     [startup] has to be sampled before anything else happens. It costs one syscall
     against a measured 4.0 ms process floor. Everything after this point is gated on
     the flag. *)
  let t_main = Timing.now () in
  Timing.startup := t_main;
  Timing.main_start := t_main;
  let opts = parse_args Sys.argv in
  Timing.on := opts.time;
  (* M1-T47. The writer's per-line clock is a syscall a line and stays off unless the
     numbers are being asked for; --time is the only thing in the tree that opens it. *)
  Writer.time_emission := opts.time;
  if opts.time then at_exit Timing.report;
  if not (Sys.file_exists opts.model) then (
    Printf.eprintf "no such file: %s\n" opts.model;
    exit exit_usage);
  if opts.all_solutions then (
    (* SPEC 2.2 describes `==========` for an exhausted search, and Output.exhausted
       renders it, but Search.solve stops at the first solution: there is no
       all-solutions mode to print it after. Saying so beats printing one solution and
       letting the `----------` imply there were no others. *)
    prerr_endline
      "baguette: --all is not implemented -- Search.solve returns the first solution \
       only. Re-run without it.";
    exit exit_unsupported);
  Timing.record "args" (Timing.now () - t_main);
  match
    Timing.phase "parse" (fun () -> Fz_error.catch (fun () -> Builder.of_file opts.model))
  with
  | Error e ->
      prerr_endline (Fz_error.to_string e);
      exit exit_usage
  | Ok m -> (
      match Fz_error.catch (fun () -> solve opts m) with
      | Ok () -> exit exit_ok
      | Error e ->
          (* Compile raises through the front end's error type for everything SPEC 2.1
             requires a diagnostic for: an unimplemented builtin, a domain the encoding
             cannot express, an objective, a search annotation that is not what the
             search actually does. *)
          prerr_endline (Fz_error.to_string e);
          exit exit_unsupported
      | exception Search.Unsound_solution assignment ->
          (* I-P1. The solver found an assignment its own propagators accepted and the
             model rejects. That is a propagator soundness bug, and the only correct
             thing to do with it is stop. *)
          Printf.eprintf
            "baguette: INTERNAL -- a propagator is unsound (I-P1). The search returned \
             an assignment that does not satisfy the model:\n";
          List.iter
            (fun (v, value) ->
              Printf.eprintf "  %s = %d\n" (Model.var m (Var.to_int v)).Model.v_name value)
            assignment;
          exit exit_internal
      | exception Writer.Audit_failed msg ->
          (* I-X2: some constraint id was minted and never retired. The answer may well
             be right, but the proof is not one we are entitled to stand behind. *)
          Printf.eprintf "baguette: INTERNAL -- proof audit failed (I-X2): %s\n" msg;
          exit exit_internal
      | exception Encoding.Width_too_large (x, lo, hi) ->
          (* M1-T54 / D-0041. The sibling of the [Unrepresentable] arm below, and exit 4
             for the same reason: lib/flatzinc/compile.ml refuses an over-wide declared
             domain first, with a positioned diagnostic and exit 3 (which is the right
             code, because an over-wide domain is a MODEL problem, not an invariant
             failure). So reaching the encoding's own raise through this binary means
             Compile's pass did not cover the path.

             Measured before adding this, with Compile's pass disabled: the binary died
             on "Fatal error: exception Baguette_proof.Encoding.Width_too_large(...)",
             exit 2 -- the same code as a bad command line.

             Two-reader wording, as I-X8 requires: reached through a different caller of
             Encoding, this exception is the documented contract rather than a bug.

             And unlike [Unrepresentable] there is NO "do not use the proof" warning,
             because [declare_int] raises before the Hashtbl and before the ladder loop.
             Nothing was allocated and nothing was written. *)
          Printf.eprintf
            "baguette: INTERNAL -- the encoding refused to declare `%s` over %d..%d, a \
             width of %d, past Encoding.max_order_width = %d (D-0041, I-X8).\n"
            x lo hi (hi - lo) Encoding.max_order_width;
          prerr_endline
            "  lib/flatzinc/compile.ml checks every declared width against that same \
             constant and";
          prerr_endline
            "  rejects an over-wide model with a positioned diagnostic and exit 3, so no \
             model this";
          prerr_endline
            "  CLI accepts should get here. Reaching it through baguette means that pass \
             has a";
          prerr_endline
            "  hole. (Reached through a different caller of Encoding, this exception is \
             the";
          prerr_endline
            "  documented contract, not a bug.) No proof was written: declare_int raises \
             before";
          prerr_endline "  it allocates the ladder.";
          exit exit_internal
      | exception Encoding.Unrepresentable why ->
          (* M1-T58. [Encoding] is the *committing door* for the .opb: it raises this
             when a row's arithmetic does not fit a 63-bit int, so writing the row would
             put a constraint in the file that is not the one posted and veripb would
             cheerfully verify the wrong model (D-0029, I-X8).

             Before this arm existed the CLI died on an uncaught exception here --
             "Fatal error: exception Baguette_proof.Encoding.Unrepresentable(...)",
             exit 2, no context and no warning about the artefact. [Checked.Overflow]
             below has had a positioned diagnostic since M1-T34; this is its twin and
             was simply missing.

             Why it is exit 4 and not exit 3, by the same argument as Overflow's: a
             model genuinely over the arithmetic limit is rejected by
             lib/flatzinc/compile.ml's cap first, with a positioned diagnostic and
             exit 3. So reaching HERE means the cap did not cover the path, which is an
             invariant this binary states about itself failing -- not a model problem.
             Reporting it as one would send the reader to rescale a model when the bug
             is in the checking.

             What is NOT the same as Overflow, and is the reason I-X8 exists: this
             exception is raised by the module that writes the artefact, on behalf of
             *any* caller. `bin/main.ml` is the only front end today and it goes through
             Compile's cap, so this is unreachable from here. A second front end -- or a
             caller that drives Encoding directly, as the test suite does -- has no such
             cap in front of it, and for those this exception is the contract rather than
             a bug. The message therefore says which of the two the reader is looking at
             instead of asserting it is a baguette bug outright. *)
          Printf.eprintf
            "baguette: INTERNAL -- the encoding refused to commit a row (I-X8, D-0029):\n\
            \  %s\n"
            why;
          Printf.eprintf
            "  Compile checks every declared bound and every posted row against \
             Checked.limit = %d\n"
            Checked.limit;
          prerr_endline
            "  before Encoding is reached, so no model this CLI accepts should get here. \
             Reaching";
          prerr_endline
            "  it through baguette means the cap has a hole -- a path whose arithmetic \
             the cap";
          prerr_endline
            "  does not bound. (Reached through a different caller of Encoding, this \
             exception";
          prerr_endline
            "  is the documented contract, not a bug: Encoding never declines quietly.)";
          prerr_endline
            "  DO NOT USE ANY PROOF FROM THIS RUN. The .opb is written before the search \
             and may";
          prerr_endline
            "  already be on disk, partially written, encoding a different model than \
             the .fzn --";
          prerr_endline "  and a checker would accept it (D-0029, SPEC 2.1).";
          exit exit_internal
      | exception Checked.Overflow msg ->
          (* M1-T34. D-0029 decided that overflow RAISES rather than wrapping or quietly
             declining, and put a compile-time cap in front of the raise so that no model
             the CLI accepts can reach it. This arm is what happens if that cap is ever
             wrong, and without it the CLI would die on an uncaught exception -- "Fatal
             error: exception Baguette_core.Checked.Overflow(...)", exit 2, no context.

             Three deliberate choices:

             * It is attached to [solve] and nowhere else. The front end computes no
               arithmetic that could overflow (nothing in lexer.ml, parser.ml,
               builder.ml or model.ml mentions Checked), so [Builder.of_file] cannot
               raise this; [Compile.compile], [Search.solve] and the encoding can, and
               all three are inside [solve].

             * It exits 4 (INTERNAL), not 3 (unsupported model), even though the model
               that triggered it really is over the arithmetic limit. Compile's own cap
               already rejects such a model with a positioned diagnostic and exit 3, so
               reaching *here* means the cap did not cover the path -- an invariant this
               binary states about itself has failed, which is what exit 4 means
               elsewhere in this file (I-P1, I-X2). Reporting it as a model problem would
               send the reader to rescale a model when the bug is in the checking.

             * It says the .opb may already be on disk and may be corrupt. That is the
               whole of D-0029's asymmetry: the row is written from the same arithmetic
               the propagator uses, before any propagator runs, so a run that gets this
               far has already produced an artefact nobody should hand to a checker. *)
          Printf.eprintf
            "baguette: INTERNAL -- integer overflow escaped the compile-time cap \
             (D-0029): %s\n"
            msg;
          Printf.eprintf
            "  Compile checks every declared bound and every posted row against \
             Checked.limit = %d\n"
            Checked.limit;
          prerr_endline
            "  and rejects over-large models with a positioned diagnostic, so this raise \
             is";
          prerr_endline
            "  meant to be unreachable. Reaching it means the cap has a hole -- a path \
             that";
          prerr_endline
            "  computes a product or a sum the cap does not bound. That is a bug in \
             baguette,";
          prerr_endline "  not in the model.";
          prerr_endline
            "  DO NOT USE ANY PROOF FROM THIS RUN. The .opb is written before the \
             search, from";
          prerr_endline
            "  the same arithmetic, so it may encode a different model than the .fzn and \
             a";
          prerr_endline "  checker would accept it (D-0029, SPEC 2.1).";
          exit exit_internal)
