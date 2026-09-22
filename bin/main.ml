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
module Retention = Baguette_core.Retention
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
     [--stats] [--max-order-width N] [--max-direct-values N] [--width-warn N]";
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
  prerr_endline "  --max-order-width N   refuse any variable whose DECLARED width";
  prerr_endline "                    exceeds N. DEFAULT: none -- the default build has no";
  prerr_endline "                    width refusal at all (M7-T1). Until M7 this was a";
  prerr_endline "                    hard cap of 10000, and that number came from the";
  prerr_endline "                    15 GB laptop baguette was written on, not from the";
  prerr_endline "                    problem. `none` restores the default. 10000 restores";
  prerr_endline "                    the old behaviour exactly.";
  prerr_endline "  --max-direct-values N  refuse a direct encoding over more than N";
  prerr_endline "                    values. DEFAULT: none (was 100000, same reason).";
  prerr_endline "  --width-warn N    warn on stderr when a single declared width exceeds";
  prerr_endline "                    N. DEFAULT: 10000 -- the OLD CAP, which now reports";
  prerr_endline "                    instead of refusing. The order encoding is written";
  prerr_endline "                    out in full, one Boolean per value, so the proof";
  prerr_endline "                    grows with the declared domain rather than with the";
  prerr_endline
    "                    difficulty; a wide domain can make a proof nobody can";
  prerr_endline
    "                    store or check. `none` silences it. Silencing it does";
  prerr_endline "                    not make the cost go away, only the sentence.";
  prerr_endline "";
  prerr_endline
    "  BAGUETTE_MAX_ORDER_WIDTH, BAGUETTE_MAX_DIRECT_VALUES, BAGUETTE_WIDTH_WARN";
  prerr_endline "                    the same three, as environment variables. A flag on";
  prerr_endline "                    the command line wins over the environment. Each";
  prerr_endline
    "                    takes an integer or `none`; anything else is an error";
  prerr_endline "                    rather than a silent `none`.";
  prerr_endline "";
  prerr_endline
    "  BAGUETTE_RETENTION=off|fifo:N|lbd:N  the learned-constraint retention policy";
  prerr_endline
    "                    (M2-L4). Default `off`: measured, see lib/core/retention.ml.";
  prerr_endline "  BAGUETTE_PROOF_AUDIT=0 disables the constraint-id audit (I-X2), which";
  prerr_endline "  is on by default here even though the library's own default is off.";
  exit exit_usage

(* A limit from the command line or the environment. A value that is neither an integer
   nor `none` is a usage error and not a silent `none`: a mistyped budget that quietly
   means "no budget" is exactly the failure this row exists to stop. *)
let set_limit what r v =
  match Encoding.limit_of_string ~what v with
  | l -> r := l
  | exception Encoding.Bad_limit (what, v) ->
      Printf.eprintf
        "%s: %S is not a limit. Give a non-negative integer, or `none` for no limit.\n"
        what v;
      usage ()

let parse_args argv =
  (* The environment first, the command line second, so a flag beats an env var. *)
  (try Encoding.limits_from_env ()
   with Encoding.Bad_limit (what, v) ->
     Printf.eprintf
       "%s: %S is not a limit. Give a non-negative integer, or `none` for no limit.\n"
       what v;
     usage ());
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
      (* M7-T1. The three tunables whose DEFAULT is now off. They mutate Encoding's refs
         rather than riding in [options], because the front end consults them during
         [Compile.compile] and the .opb writer consults them again later: there is no
         single call site to thread them through, and a ref that the CLI sets once,
         before anything is compiled, is honest about that. *)
      | "--max-order-width" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--max-order-width" Encoding.order_width_limit argv.(i + 1);
          go (i + 2)
      | "--max-direct-values" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--max-direct-values" Encoding.direct_values_limit argv.(i + 1);
          go (i + 2)
      | "--width-warn" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--width-warn" Encoding.width_warn_threshold argv.(i + 1);
          go (i + 2)
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

(* ------------------------------------------------- the retention policy (M2-L4) *)

(* [Search.config.retention], from the environment.

   An environment variable rather than a flag because it is a MEASUREMENT knob and not a
   user-facing choice: M2-L4's test (c) measures .pbp bytes and checker time with the
   policy on and off, and a measurement nobody else can re-run is a measurement this
   project has already been burned by. The default is [Retention.default], so a normal
   run never reads this.

   Unparseable input FAILS rather than falling back to the default. A measurement run
   that silently used the default because the spelling was wrong is exactly the
   "byte-identical before and after" trap CLAUDE.md records twice. *)
let retention_policy () =
  let bad v =
    prerr_endline
      (Printf.sprintf
         "baguette: BAGUETTE_RETENTION=%S is not a policy. Use off, fifo:N or lbd:N, \
          where N is the database cap."
         v);
    exit 2
  in
  match Sys.getenv_opt "BAGUETTE_RETENTION" with
  | None -> Retention.default
  | Some "off" -> Retention.keep_all
  | Some v -> (
      match String.index_opt v ':' with
      | None -> bad v
      | Some i -> (
          let kind = String.sub v 0 i in
          let arg = String.sub v (i + 1) (String.length v - i - 1) in
          match (kind, int_of_string_opt arg) with
          | _, None -> bad v
          | _, Some n when n < 0 -> bad v
          | "fifo", Some n -> Retention.fifo ~cap:n
          | "lbd", Some n -> Retention.lbd ~cap:n
          | _ -> bad v))

(* [Search.config.propagate_learned], from the environment, for the same reason and with
   the same discipline as [retention_policy] above: M2-L12 has to be able to measure a
   build in which every learned constraint is proof-only, which is what this project was
   before that row. BAGUETTE_PROPAGATE_LEARNED=off is that build. Anything other than
   "off" or unset FAILS; a measurement run that silently used the default because the
   spelling was wrong is the trap CLAUDE.md records twice. *)
let propagate_learned () =
  match Sys.getenv_opt "BAGUETTE_PROPAGATE_LEARNED" with
  | None | Some "on" -> true
  | Some "off" -> false
  | Some v ->
      prerr_endline
        (Printf.sprintf
           "baguette: BAGUETTE_PROPAGATE_LEARNED=%S is not a setting. Use on or off." v);
      exit 2

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
(* M7-T1. What the encoding cost, on stderr under --stats.

   This is the counter half of the diagnostic that replaced the width refusal. The
   warning half fires in Encoding.declare_int and does not wait to be asked; this half
   is here because the TOTAL is the number the per-variable cap never bounded, and said
   so in its own comment: a thousand variables at width 9 999 was always ten million
   clauses and always slipped through.

   Written for a reader who has not read D-0028, per the same rule as the warning. *)
let report_encoding_cost (c : Encoding.cost) =
  prerr_endline
    "stats: encoding cost (M7-T1). Baguette writes every integer variable out as one";
  prerr_endline
    "stats: Boolean per value (`x >= v`) before any constraint is posted, so the size of";
  prerr_endline
    "stats: the proof follows the DECLARED domains, not the difficulty of the problem.";
  Printf.eprintf "stats: %-10s %10d cls    order-ladder clauses, over all variables\n"
    "ladder" c.Encoding.c_ladder_clauses;
  Printf.eprintf "stats: %-10s %10d lines  .opb constraints (ids minted)\n" "opb"
    c.Encoding.c_constraints;
  Printf.eprintf "stats: %-10s %10d vals   materialised into direct encodings\n" "direct"
    c.Encoding.c_direct_values;
  (match c.Encoding.c_widest with
  | None ->
      Printf.eprintf "stats: %-10s %10s        no integer variable declared\n" "widest"
        "-"
  | Some (x, lo, hi) ->
      Printf.eprintf
        "stats: %-10s %10d wide   `%s` over %d..%d -- the one to narrow first\n" "widest"
        (hi - lo) x lo hi);
  Printf.eprintf "stats: %-10s %10s        --max-order-width, --width-warn\n" "limits"
    (Encoding.order_width_limit_string ())

let report_stats (st : Search.stats) ~exhausted =
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
  Printf.eprintf "stats: %-10s %10s        %s\n" "retention"
    (Retention.policy_name (Search.stats_db st))
    (Retention.to_string (Search.stats_db st));
  Printf.eprintf "stats: %-10s %10s        %s\n" "lbd"
    (String.concat ","
       (List.map (fun (l, n) -> Printf.sprintf "%d:%d" l n) (Search.stats_lbd st)))
    "M2-L4: learned-clause LBD histogram, `lbd:count`; the last bucket is `>=`";
  Printf.eprintf "stats: %-10s %10s        %s\n" "width"
    (String.concat ","
       (List.map (fun (w, n) -> Printf.sprintf "%d:%d" w n) (Search.stats_width st)))
    "M2-L12: learned-clause WIDTH histogram, `lits:count`; the last bucket is `>=`";
  (* M2-L12. [glob-prune] is the one to read: a learned unit that never moves a bound is
     a bound the search had already re-derived for itself, so a build with units applied
     and this counter at 0 would have changed nothing. [cls-inst] is step 2's population
     and [glob-decl]/[cls-decl] are the literals neither step could take (a [Lit.Eq], or
     a name the encoding does not declare) -- printed because "step 1 captured the unit
     population" is a claim they can refute. *)
  Printf.eprintf "stats: %-10s %10d units  %s\n" "globals"
    (List.length (Search.stats_globals st))
    "M2-L12: distinct learned UNITS in force as global bound tightenings";
  Printf.eprintf "stats: %-10s %10d prunes %s\n" "glob-prune" st.Search.n_global_prunes
    "...times applying one actually MOVED a bound; 0 means step 1 changed nothing";
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "glob-confl" st.Search.n_global_conflicts
    "...times one refuted the node outright";
  Printf.eprintf "stats: %-10s %10d inst   %s\n" "cls-inst" st.Search.n_clause_instances
    "M2-L12 step 2: multi-literal learned clauses registered as engine instances";
  Printf.eprintf "stats: %-10s %10d cls    %s\n" "cls-decl"
    (st.Search.n_global_declined + st.Search.n_clause_declined)
    "...learned clauses neither step could instantiate (a Lit.Eq, or an unknown name)";
  Printf.eprintf "stats: %-10s %10d prunes %s\n" "cls-prune" st.Search.n_clause_prunes
    "...bounds those clause instances actually MOVED. M2-L12 measured 0 suite-wide";
  (* M2-L13 / D-0054. The learned PB ROW as a runtime consumer -- the solving-side
     object, instantiated by Pb.of_terms over the order literals it already names and
     NOT by Learned.to_linear_row, which is the proof-side gate this row removed. Do not
     read `pb-convert` as a success measure for it: that counter IS the gate. Read these.
     `pb-prune` and `pb-confl` are the honest pair, counted off the trail (M2-T7 stamps
     every entry with the instance that pushed it), and they are what M2-L12's measured
     zero has to be compared against. *)
  Printf.eprintf "stats: %-10s %10d inst   %s\n" "pb-inst" st.Search.n_pb_instances
    "M2-L13: learned PB rows registered as engine instances (Pb.Learned_pb)";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-inst-no" st.Search.n_pb_inst_declined
    "...rows Pb.of_terms refused (a Lit.Eq literal, or a name the encoding lacks)";
  Printf.eprintf "stats: %-10s %10d prunes %s\n" "pb-prune" st.Search.n_pb_prunes
    "...bounds a learned PB instance actually MOVED. The M2-L13 counter";
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "pb-confl" st.Search.n_pb_inst_conflicts
    "...and conflicts one reported outright";
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
    "...learned PB rows Learned.to_linear_row accepts -- INCLUDING the empty \
     contradiction";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-stronger" st.Search.n_pb_stronger
    "...of those, where the SAME conflict's clause does NOT convert. M2-L6 test (a)";
  (* M2-L11 test (b). READ THIS BESIDE [pb-convert] AND [pb-stronger], NEVER INSTEAD OF
     EITHER. A learned row that is the EMPTY CONTRADICTION is strictly stronger than the
     clause it replaces and still useless as a propagation result; it also CONVERTS -- to
     a zero-term Linear -- so neither [pb-convert] nor [pb-stronger] can tell the two
     apart. That is deliberate and it is what test_ladder.ml's degenerate control pins;
     [pb-nondeg] is the counter that can, so a claim that PB learning improved is a claim
     about this line.

     Re-measured 2026-09-18 (M2-L4), by solving every model in test/models/ with `--stats`
     and summing each line -- not read off an earlier note, which is how the figure this
     replaces went stale:

       39 models; pb-learned 38; pb-nondeg 28; pb-convert 36; pb-stronger 36.

     **10 of those 36 conversions are the empty contradiction** -- backjump_lineq_unsat
     (3), near_limit_unsat (3), offset_unsat (4), every one of them the int_lin_eq family
     whose two halves add to 0 >= k in one elimination. So 26 of the 36 are conversions
     that could actually propagate, and the same 10 inflate [pb-stronger].

     The text here previously read "26 of 36 NON-degenerate on the same 38 models". Two
     things were wrong with it and they pull in opposite directions: the suite is 39
     models, not 38, and the non-degenerate count is 28 of 38 LEARNED ROWS, not 26 of 36
     CONVERSIONS. 26 of 36 is a real figure about a different question -- the one in the
     paragraph above.

     [pb-lifted] says whether lib/core/ladder.ml fired at all: the lift is a retry after
     the bare model row fails, so 0 here means this build derives exactly what M2-L6
     derived. *)
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-nondeg" st.Search.n_pb_nondegenerate
    "...learned PB rows that are NOT the empty contradiction. M2-L11 test (b)";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-lifted" st.Search.n_pb_lifted
    "...learned by resolving against model row PLUS a ladder chain (M2-L11); 0 = M2-L6";
  Printf.eprintf "stats: %-10s %10d rungs  %s\n" "pb-rungs" st.Search.n_pb_rungs
    "order-encoding ladder rows those analyses cited, summed (D-0028)";
  (* M2-L15. The backjump's own level set, against the one the learned PB row names.
     REPORTED AND NOT ACTED ON: lib/core/search.ml's [pb_level_verdict] has the argument,
     and the short form is that the nogood is a clause over DECISIONS, so only the
     decision closure answers the question the filter asks. [lvl-narrow] is the dangerous
     arm -- the PB set is a strict subset and would license a jump the closure does not --
     and every count in it is a conflict at which [Search.backjump_on_pb] emits a clause
     veripb refuses. [lvl-assert] is the SAT solver's backjump level looking deeper than
     the closure's deepest decision, i.e. exactly the temptation Le Berre et al.
     (arXiv 2107.13085) warn carries no guarantee over PB. *)
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "lvl-cmp" st.Search.n_level_compared
    "conflicts where BOTH a decision closure and a PB row existed to compare (M2-L15)";
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "lvl-same" st.Search.n_level_same
    "...at which the two level sets are EQUAL";
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "lvl-narrow" st.Search.n_level_narrower
    "...at which the PB row's set is a STRICT SUBSET -- it would jump too high. UNSOUND";
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "lvl-wide" st.Search.n_level_wider
    "...at which the closure's is the strict subset -- the row names levels it does not \
     rest on";
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "lvl-incomp"
    st.Search.n_level_incomparable "...at which neither set contains the other";
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "lvl-empty" st.Search.n_level_pb_empty
    "...of those, where the PB row names NO level -- the empty contradiction. WORST CASE";
  Printf.eprintf "stats: %-10s %10d confl  %s\n" "lvl-assert"
    st.Search.n_level_assert_deeper
    "...at which the PB row asserts BELOW EVERY decision the conflict rests on (M2-L15)";
  if Search.stats_level_diffs st <> [] then
    Printf.eprintf "stats: %-10s %10s        first disagreement: %s\n" "lvl-why" ""
      (List.hd (Search.stats_level_diffs st));
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
  if opts.stats then report_encoding_cost (Encoding.cost encoding);
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
            let config =
              {
                Search.default_config with
                retention = retention_policy ();
                propagate_learned = propagate_learned ();
              }
            in
            let r =
              match compiled.Compile.objective with
              | None ->
                  `Satisfy
                    (Search.solve ~engine:compiled.Compile.engine ~store ~ctx ~check
                       ~stats ~config ())
              | Some objective ->
                  (* M5-T1. Each improving solution is printed AS IT IS FOUND, which is
                     the FlatZinc convention SPEC 2.2 describes -- a running report, so
                     that a user who interrupts a long optimisation has still been told
                     the best answer so far. The consequence for --time is that the
                     solution printing of an optimisation run is inside the `search`
                     phase and not inside `output`, where a satisfaction run's is; the
                     `output` phase then holds only the final marker. That is the honest
                     placement, since the printing really does happen there. *)
                  `Optimise
                    (Search.optimise ~engine:compiled.Compile.engine ~store ~ctx ~check
                       ~stats ~config ~objective
                       ~on_solution:(fun assignment ->
                         print_string
                           (Output.solution m (assignment_values m store assignment));
                         flush stdout)
                       ())
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
  let exhausted =
    match outcome with
    | `Satisfy Search.Unsat -> true
    | `Satisfy (Search.Sat _) -> false
    (* An optimisation run that reports an optimum has exhausted the space under the
       last improving bound, and one that reports no solution has exhausted it outright.
       Either way the search finished; there is no "stopped at the first answer" arm. *)
    | `Optimise (Search.Opt _ | Search.Opt_unsat) -> true
  in
  Timing.phase "output" (fun () ->
      (match outcome with
      | `Satisfy (Search.Sat assignment) ->
          print_string (Output.solution m (assignment_values m store assignment))
      | `Satisfy Search.Unsat -> print_string Output.unsatisfiable
      (* SPEC 2.2: `==========` after the last solution when the search space is
         exhausted. Every improving solution, including this one, has already been
         printed by [on_solution] above, so what is left here is the marker that says
         the last of them was optimal -- and it is printed only because the proof just
         written establishes that. *)
      | `Optimise (Search.Opt _) -> print_string Output.exhausted
      | `Optimise Search.Opt_unsat -> print_string Output.unsatisfiable);
      flush stdout);
  if opts.stats then report_stats stats ~exhausted

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
            "baguette: INTERNAL -- the encoding refused to declare `%s` over %d..%d, \
             past the width limit in force, which is %s (D-0041, I-X8; M7-T1 made it an \
             option, default none).\n"
            x lo hi
            (Encoding.order_width_limit_string ());
          prerr_endline
            "  lib/flatzinc/compile.ml checks every declared width against that same \
             limit and";
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
