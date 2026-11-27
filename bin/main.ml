(* The baguette CLI.
     baguette MODEL.fzn|MODEL.scp [--proof PREFIX | --no-proof] [options]
   ([usage] lists every option and every environment switch.)

   This file has one job, which docs/ARCHITECTURE.md states as "parse args, wire
   everything, print results": it reads the command line, runs the library's pipeline
   and maps each outcome to an output and an exit status. It computes nothing of its
   own. Wiring the CLI (.fzn in, solution and proof out) was M1-T14; before it the
   engine already solved the models in test/models/ and emitted proofs veripb accepted,
   but nothing reached it from a command line.

   The pipeline, in the order it must happen:

     Builder.of_file / Reader.of_file  .fzn or .scp text -> Model.t
     Compile.compile   Model.t              -> store, engine, encoding
     Encoding.write_opb                     -> PREFIX.opb   (I-X5: the .opb is complete
                                                             on disk before any proof
                                                             rule cites it)
     Encoding.start_proof                   -> the proof's `f N` header
     Search.solve / Search.optimise         -> an answer, the proof written as it goes
     Output.solution / Output.unsatisfiable -> stdout, in the format SPEC 2.2 pins

   The file in order: the exit statuses; [usage]; the option parser [parse_args] and
   where a run without --proof writes its proof; the --time instrument ([Timing]); the
   index bridge from solver variables to model variables; the measurement knobs read
   from the environment; the --stats reports; [solve], which runs the pipeline above;
   the MiniZinc standard flags; and the main program, which sizes the minor heap,
   arms the heap budget, picks the reader and turns each exception into its exit
   status.

   Four things here are less obvious than they look.

   **The variable-index bridge.** [Search.assignment] is a [(Var.t * int) list] over the
   solver's own variable identities; [Model.check_assignment] and [Output.solution] both
   want an [int array] indexed by *model* variable index. Those two index spaces coincide
   only because [Compile.compile] builds the store in [Model.vars] order and promises to
   keep doing so. [assignment_values] below is where they meet, and it re-checks the
   promise rather than assuming it. An off-by-one here would print a wrong answer that
   the independent solution check would then confirm (I-S1: every printed solution
   satisfies every constraint, re-checked by [Model.check_assignment] outside the
   propagators), because it would be checking the same permuted array.

   **A run without --proof writes its proof and KEEPS it** (M9-no-proof-T5, D-0163, the
   user's decision of 2026-11-19). docs/SPEC.md section 1 says "The proof is not a
   debugging aid. It is a primary output", so the default run writes PREFIX.opb and
   PREFIX.pbp under a name [default_proof_prefix] takes from the model (`./foo.opb` and
   `./foo.pbp` for `foo.fzn`, in the current directory) and leaves them there.
   `--proof PREFIX` chooses the name. Before T5 such a run wrote the .pbp to a temporary
   file and deleted it, and wrote no .opb at all, so its answer came with a proof nobody
   could check.

   **Except under `--no-proof` (M9-no-proof-T2), which is off by default and is a
   MEASUREMENT INSTRUMENT, not a mode of the solver** (D-0126: a solve without a proof
   exists only to measure what the proof costs). It keeps every Explanation (I-P4: every
   domain change carries one, and the mutators take one by type), the learning and the
   independent solution check I-S1. It skips what makes bytes: the .opb rows
   ([Encoding.row_sink] at [Discard_rows], and the ladder loop short-circuited to its
   count), the .pbp (a [Writer.t] over [Filename.null] built by
   [Writer.create ~null:true], whose every rule mints its id and writes nothing), every
   justification and trace ([Justify] and [Trace] return at their entry under that
   writer, before forcing anything), the proof-side deletion of learned rows and the
   audit I-X2 (every constraint id minted is deleted exactly once, checked at the
   conclusion). [Encoding.start_proof] is still called, through that writer, because
   element and alldiff embed its [Writer.fresh] ids in their explanations and D-0126's
   id rule wants those ids identical in both modes. Since the --no-proof audit (D-0161,
   which removed what the null writer still paid for) it mints the root lemmas' ids
   without reading the lemmas, and [Search] no longer builds what only a proof line
   reads: an improving solution's literal family, a decision's bits atom, and the walk
   over the cut that I-S4 needs (a trace line citing a hole is supported only while that
   hole's own line is live). What such a run prints is UNVERIFIED and SPEC section 1
   says it is not a result; `--stats` says so on stderr. `make check` proves every model
   AND runs it again under this flag, and stdout and the exit code must be
   byte-identical (scripts/run_model_tests.sh). That comparison is the one direct test
   that proof logging never steers the search.

   **The .opb comment names the model's BASENAME, not the path it was given** (M1-T37).
   The .opb's size must be a property of the model alone. Its byte count is the one
   column the proof benchmark (M3-T5, which reports .opb bytes, .pbp bytes and checker
   seconds separately) found trustworthy at every row, and while the header read
   `"baguette: " ^ opts.model` that column depended on where the file lived: the same
   file measured as `test/models/x.fzn` and as `/tmp/x.fzn` produced .opb files about
   16 bytes apart. The basename is kept, rather than the comment dropped, because a
   person holding a .opb and a .pbp in a temporary directory still needs to know which
   model they belong to, and the directory is the one part of the path that person
   already knows (they typed it). bench/run_bench.sh checks this property on every run
   (`opb_path_independence` there), so the dependence cannot come back unnoticed.

   **The MiniZinc standard flags** (M7-T32, D-0150, SPEC 2.2). `minizinc --solver
   baguette` passes a solver only the flags its `tools/baguette.msc` declares in
   `stdFlags`, always BEFORE the model file, and each one here is a thin mapping onto a
   long option that already existed.

     -t MS     is `--time-limit MS/1000`.
     -s        is `--stats` plus a `%%%mzn-stat:` block on stdout at the end of the run,
               the one way a flag changes stdout.
     -f        is `--search alternate --restarts luby --phase-saving`, for whichever of
               the three was not given explicitly. That is Chuffed's free search, the
               annotation's order alternating with the activity order under restarts
               (D-0137 section 4). It was unsafe while the checker refused some branch
               nogoods under restarts with a dynamic order (M7-T31), until D-0148 fixed
               the decision closure; the default search stays the fixed one by the
               user's choice (D-0154).
     -i        and, on an optimisation model, `-a` ask for every improving solution,
               which this CLI prints anyway, each with its own `soli` line in the proof.
     -r SEED   is accepted and unused: nothing on the CLI's path draws a random number.
     -p N      is accepted, and the run uses one thread.
     -v        says on stderr what the flags became.

   REFUSED with exit 3, after the model is read: `-a` and `-n N` with N > 1 on a
   SATISFACTION model. Enumerating solutions needs a proof shape for "no other
   solution" that the writer does not have (VeriPB 3.0's `solx` needs a preserved set,
   see [Writer]) and a search that continues past a solution, which [Search.solve] does
   not do. The .msc therefore declares `-i` and not `-a`, and MiniZinc itself answers
   `-a` on a satisfaction model with "Solver does not support all solutions". *)

module Model = Baguette_flatzinc.Model
module Builder = Baguette_flatzinc.Builder
module Compile = Baguette_flatzinc.Compile
module Output = Baguette_flatzinc.Output
module Fz_error = Baguette_flatzinc.Error
module Var = Baguette_core.Var
module Store = Baguette_core.Store
module Search = Baguette_core.Search
module Retention = Baguette_core.Retention
module Restart = Baguette_core.Restart
module Phase = Baguette_core.Phase
module Activity = Baguette_core.Activity
module Justify = Baguette_core.Justify
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding
module Checked = Baguette_core.Checked

type options = {
  model : string;
  proof_prefix : string option;
      (* M9-no-proof-T5: [None] exactly under --no-proof; otherwise --proof's argument, or
         [default_proof_prefix] of the model when it was not given *)
  proof_note : bool; (* M9-no-proof-T5: say on stderr where the proof went (MiniZinc) *)
  proof_comments : bool;
  all_solutions : bool;
  time : bool;
  stats : bool;
  time_limit : float option;
  no_proof : bool; (* M9-no-proof-T2: solve without a proof -- see the header *)
  (* The opt-in search strategies (D-0137): restarts and phase saving (M10-search-
     strategy-T2), the activity order and trail reuse (M10-search-strategy-T3). *)
  restarts : Restart.policy; (* --restarts *)
  phase_saving : bool; (* --phase-saving *)
  search : Search.search_mode; (* --search *)
  reuse_trail : bool; (* --reuse-trail *)
  cdcl : bool;
      (* --cdcl, or BAGUETTE_CDCL=1: the CDCL loop, in which the learned clause drives
         the search by backjumping to its asserting level (M19-config-T10/T11, D-0219) *)
  chrono : int option;
  (* --chrono T, or BAGUETTE_CHRONO=T: under --cdcl, a backjump over more than T
     levels goes back one level instead (chronological backtracking,
     M19-config-T11, D-0224) *)
  (* M7-T32, D-0150: the MiniZinc standard flags. See the header. *)
  intermediate : bool; (* -i: every improving solution; printed anyway *)
  n_solutions : int option; (* -n N; N > 1 on a satisfaction model is refused *)
  seed : int option; (* -r SEED: accepted, unused *)
  threads : int option; (* -p N: accepted, one thread *)
  mzn_stats : bool; (* -s: --stats and the %%%mzn-stat block on stdout *)
  verbose : bool; (* -v: the flags' mapping, on stderr *)
  e2e : bool;
      (* --e2e: the proof is written to be checked against the .opb of cake_pb_cp, the
         verified CakeML encoder, and its prefix derives this run's .opb from that one
         (M14-e2e-verification-T3, D-0187) *)
}

(* Exit statuses. Each names a kind of outcome a harness must tell apart from the
   others, so a new kind of failure gets its own number rather than sharing one.

     0  the run answered: SAT, UNSAT, an optimum, or a run stopped by --time-limit, by
        BAGUETTE_NODE_LIMIT, by a signal, or by the heap budget once it has an incumbent.
        The proof is ended in every one of these cases.
     2  usage: a bad command line or environment value, a missing model file, a model
        the reader cannot parse, --e2e on a .scp. An uncaught OCaml exception also
        exits 2, which is the runtime's own status and why the arms in the main program
        exist.
     3  unsupported: a legal model this solver declines with a diagnostic (a builtin it
        does not implement, a domain the encoding cannot express, enumeration on a
        satisfaction model, a construct --e2e does not cover).
     4  internal: an invariant this binary states about itself failed (an unsound
        propagator, the proof audit, a compile-time cap with a hole).
     5  resource: the run needed more than the budget it was given ([exit_resource]).
     6  write: a file could not be written ([exit_write]).

   0 covers UNSAT as well as SAT because an UNSAT model is a successful run that proved
   something, and scripts/run_model_tests.sh reads a non-zero exit as the solver having
   fallen over. *)
let exit_ok = 0
let exit_usage = 2
let exit_unsupported = 3
let exit_internal = 4

(* Exit 5, a RESOURCE overrun: the run asked for more of the machine than the budget it
   was given allows. The budgets are the graceful resource guard of M7-T8 (D-0071), off
   by default: a predictive one, --max-encoding-clauses, which refuses an encoding
   before allocating it, and a reactive one, --max-heap-mb, which watches the OCaml
   heap. It is not 3, because the model is legal input that a bigger budget would
   answer; it is not 4, because no invariant failed; and it is above all not the exit
   134 of the OCaml runtime's own `Fatal error: allocation failure`, which the first
   full corpus run (D-0068) saw nine times and could not tell apart from a crash. The
   number lives in [Encoding] because the Gc alarm exits with it directly, and this
   binding is here so that this table shows all six statuses. *)
let exit_resource = Encoding.exit_resource

(* Exit 6, a WRITE failed: the proof's directory does not exist, or the disk is full
   (M22-review-T5, D-0248). Not 5, because campaigns count 5 as the heap budget
   (scripts/corpus_run.sh's REFUSED-RESOURCE) and its remedy, a larger budget, is not
   this one's; not 4, because no invariant failed; and not the 2 an uncaught [Sys_error]
   used to exit with, which is also usage's. See [exit_write_failed]. *)
let exit_write = 6

let usage () =
  prerr_endline
    "usage: baguette MODEL.fzn|MODEL.scp [--proof PREFIX | --no-proof] \
     [--proof-comments] [--all] [--time] [--stats] [--max-order-width N] \
     [--max-direct-values N] [--width-warn N] [--max-encoding-clauses N] [--max-heap-mb \
     N] [--bits-above W] [--time-limit S] [--restarts POLICY] [--phase-saving] [--search \
     ORDER] [--reuse-trail] [--cdcl] [--chrono T] [-a] [-i] [-n N] [-f] [-t MS] [-r \
     SEED] [-p N] [-s] [-v]";
  prerr_endline "";
  prerr_endline
    "  MODEL.scp (M23-inputs, D-0230): the .scp format of CakeML's cake_pb_cp, version";
  prerr_endline
    "                    1, read by lib/scp/ into the same model a .fzn becomes. A";
  prerr_endline
    "                    constraint baguette does not propagate is refused with its";
  prerr_endline
    "                    position, never read in part; `enumerate` searches one";
  prerr_endline
    "                    solution, as `decide`; every variable of the file is printed";
  prerr_endline "                    as `name = value;`. --e2e is refused on a .scp.";
  prerr_endline "";
  prerr_endline
    "  The MiniZinc standard flags (M7-T32, D-0150; tools/baguette.msc declares them):";
  prerr_endline
    "  -i                every improving solution of an optimisation model, each";
  prerr_endline "                    followed by `----------` (printed anyway; SPEC 2.2).";
  prerr_endline "  -a                -i on an optimisation model; refused (exit 3) on a";
  prerr_endline
    "                    satisfaction model: enumeration has no proof shape yet.";
  prerr_endline
    "  -n N              stop after N solutions: N = 1 is the default; N > 1 on a";
  prerr_endline "                    satisfaction model is refused (exit 3) as -a is.";
  prerr_endline "  -f                free search: --search alternate --restarts luby";
  prerr_endline "                    --phase-saving, each unless given explicitly. Worth";
  prerr_endline
    "                    trying when the model's search annotation is a poor order.";
  prerr_endline "  -t MS             --time-limit in milliseconds.";
  prerr_endline
    "  -r SEED           accepted and unused: the search draws no random number.";
  prerr_endline "  -p N              accepted; the run uses one thread.";
  prerr_endline
    "  -s                --stats, plus a `%%%mzn-stat:` block on STDOUT at the";
  prerr_endline "                    end of the run (MiniZinc's statistics format).";
  prerr_endline "  -v                what the flags above became, on stderr.";
  prerr_endline "";
  prerr_endline
    "  --proof PREFIX    write the proof as PREFIX.opb and PREFIX.pbp (SPEC 4.1);";
  prerr_endline "                    verify it with: veripb PREFIX.opb PREFIX.pbp";
  prerr_endline "                    WITHOUT --proof every run still writes and keeps its";
  prerr_endline "                    proof, as ./MODEL.opb and ./MODEL.pbp in the current";
  prerr_endline "                    directory, MODEL being the model's file name without";
  prerr_endline
    "                    .fzn (M9-no-proof-T5). Under MiniZinc, whose .fzn is a";
  prerr_endline
    "                    temporary mznfile*.fzn, it is ./baguette-proof.opb and";
  prerr_endline
    "                    .pbp, and stderr says so. A previous run's files of the";
  prerr_endline "                    same name are overwritten. --no-proof writes none.";
  prerr_endline "  --proof-comments  enable the proof writer's comment lines. No shipped";
  prerr_endline
    "                    model reaches a call site that emits one, so on every";
  prerr_endline "                    model in test/models/ the .opb and .pbp are";
  prerr_endline "                    byte-identical with and without it (M1-T48).";
  prerr_endline
    "  --all             on an optimisation model, every improving solution (printed";
  prerr_endline
    "                    anyway); on a satisfaction model, every solution: NOT";
  prerr_endline "                    implemented, refused with exit 3 (M7-T32, D-0150).";
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
  prerr_endline "  --time-limit S    stop the search after S seconds (M6-T9). Checked at";
  prerr_endline "                    the entry of every search node and every 128";
  prerr_endline
    "                    propagator runs inside one (M6-T21), against the WALL";
  prerr_endline
    "                    clock (Unix.gettimeofday, M6-T10 -- the clock an outer";
  prerr_endline "                    `timeout` uses, so under load the stop wins the race";
  prerr_endline "                    the CPU clock lost), counted from process start, so";
  prerr_endline "                    parse and compile are inside it. One slow propagator";
  prerr_endline
    "                    run or conflict can overrun it; keep an outer `timeout`";
  prerr_endline "                    above it. On";
  prerr_endline "                    expiry: stdout is `=====UNKNOWN=====` if no solution";
  prerr_endline
    "                    was printed, and otherwise just the solutions already";
  prerr_endline "                    printed (an optimisation run prints each improving";
  prerr_endline "                    one as found) WITHOUT `==========`; stderr carries";
  prerr_endline "                    one `limit: ` summary line, plus --stats/--time as";
  prerr_endline "                    usual; the proof ends `conclusion NONE`, which";
  prerr_endline "                    veripb checks and reports as VERIFIED NO CONCLUSION,";
  prerr_endline "                    or on an optimisation model `conclusion BOUNDS`,";
  prerr_endline "                    the declared bound and the best solution printed.";
  prerr_endline "                    Exit status 0: a stopped run is not a failure.";
  prerr_endline "                    SIGTERM, SIGINT and SIGXCPU stop a run the same way";
  prerr_endline "                    (M6-T24), and a second one ends the proof at once.";
  prerr_endline
    "  --no-proof        (M9-no-proof-T2, D-0126) solve WITHOUT a proof. Off by";
  prerr_endline "                    default, and a MEASUREMENT INSTRUMENT: the answer it";
  prerr_endline
    "                    prints is UNVERIFIED and is not a result (SPEC 1). It";
  prerr_endline
    "                    writes no .opb, no .pbp, no justification and no trace,";
  prerr_endline
    "                    skips the proof-side deletion of learned rows and the";
  prerr_endline
    "                    audit I-X2 (BAGUETTE_PROOF_AUDIT is ignored), and keeps";
  prerr_endline
    "                    every explanation, the learning, the solution check and";
  prerr_endline
    "                    every front-end refusal. stdout is byte-identical to the";
  prerr_endline
    "                    proved run's -- scripts/run_model_tests.sh checks that on";
  prerr_endline
    "                    every model, every `make check`. Cannot be combined with";
  prerr_endline "                    --proof (exit 2). --stats says the run was unproved.";
  prerr_endline "";
  prerr_endline
    "  --e2e             (M14-e2e-verification-T3, D-0187) write PREFIX.pbp to be checked";
  prerr_endline
    "                    against the .opb CakeML's verified encoder cake_pb_cp writes for";
  prerr_endline
    "                    the model's .scp (tools/e2e/fzn2scp.py), not against PREFIX.opb:";
  prerr_endline
    "                    its head derives each row of PREFIX.opb from cake's rows";
  prerr_endline
    "                    (docs/PROOF-FORMAT.md section 3b). Needs --proof. A builtin it";
  prerr_endline "                    does not cover is refused (exit 3). Off by default.";
  prerr_endline "";
  prerr_endline
    "  --restarts POLICY (M10-search-strategy-T2, D-0137, SPEC 3.4) restart the search";
  prerr_endline
    "                    to level 0 on a deterministic schedule. POLICY is one of";
  prerr_endline
    "                    none (default), luby[:U] (U * luby(k) conflicts, U=100),";
  prerr_endline
    "                    geom[:U[:F]] (U * F^k, 100 and 1.5), lbd[:W[:K]] (Glucose's";
  prerr_endline
    "                    LBD average, W=50 K=0.8, with a Luby floor), stable[:U]";
  prerr_endline "                    (lbd and luby:U phases alternating). Every learned";
  prerr_endline "                    constraint is kept across a restart.";
  prerr_endline
    "  --phase-saving    (M10-search-strategy-T2, D-0137) branch on the value a";
  prerr_endline "                    variable was last fixed at, when it is still in its";
  prerr_endline
    "                    domain; the variable choice is unchanged. Overrides an";
  prerr_endline "                    annotation's value choice: an explicit substitution.";
  prerr_endline "  --search ORDER    (M10-search-strategy-T3, D-0137) the variable order:";
  prerr_endline "                    annotation (default: the annotation, else SPEC 3.4's";
  prerr_endline "                    first-fail), activity (the unfixed variable with the";
  prerr_endline "                    highest conflict activity, EVSIDS decay), alternate";
  prerr_endline "                    (annotation and activity, switching at each restart;";
  prerr_endline "                    needs --restarts to ever switch).";
  prerr_endline
    "  --reuse-trail     with --search activity and --restarts: keep the levels";
  prerr_endline
    "                    whose decision still outscores every unfixed variable";
  prerr_endline "                    (partial restarts, van der Tak et al. 2011).";
  prerr_endline
    "  --cdcl            (M19-config-T10, D-0219) opt-in: the CDCL loop instead of the";
  prerr_endline
    "                    default depth-first search: learn the 1UIP clause, backjump";
  prerr_endline
    "                    to its asserting level and let it propagate there. Same as";
  prerr_endline "                    BAGUETTE_CDCL=1.";
  prerr_endline
    "  --chrono T        (M19-config-T11, D-0224) with --cdcl: a backjump that would";
  prerr_endline
    "                    skip more than T levels goes back one level instead and";
  prerr_endline "                    asserts the learned literal there (chronological";
  prerr_endline "                    backtracking, Nadel and Ryvchin 2018). Same as";
  prerr_endline "                    BAGUETTE_CHRONO=T. Off by default.";
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
  prerr_endline "  --max-encoding-clauses N  stop before the encoding grows past N";
  prerr_endline "                    clauses-and-values in TOTAL, over every variable";
  prerr_endline "                    (M7-T8). DEFAULT: none. Unlike --max-order-width";
  prerr_endline "                    this bounds the AGGREGATE, which is the thing that";
  prerr_endline "                    actually grows: a thousand variables of width 9999";
  prerr_endline "                    is ten million clauses and no per-variable cap sees";
  prerr_endline "                    it. Checked before each declaration allocates, so";
  prerr_endline "                    nothing is half-built; the diagnostic names the";
  prerr_endline "                    declaration that crossed it and the widest domain";
  prerr_endline "                    to narrow. Exit status 5.";
  prerr_endline "  --max-heap-mb N   stop when the OCaml heap passes N MB (M7-T8).";
  prerr_endline "                    DEFAULT: none. The backstop for what the clause";
  prerr_endline "                    budget cannot predict -- the search's own trail,";
  prerr_endline "                    learned constraints, the proof writer. Checked at";
  prerr_endline "                    each declaration AND from a Gc alarm -- the alarm";
  prerr_endline "                    is the reliable half, because the heap figure is";
  prerr_endline "                    only refreshed at a major-GC boundary, so a run too";
  prerr_endline "                    short to complete one reads 0. Exit status 5.";
  prerr_endline "                    Without it an over-large run ends in the OCaml";
  prerr_endline "                    runtime's `Fatal error: allocation failure`, exit";
  prerr_endline "                    134, which cannot be caught and names nothing.";
  prerr_endline "";
  prerr_endline "  exit status       0 solved (SAT or UNSAT) or stopped by --time-limit,";
  prerr_endline "                    2 usage or bad model,";
  prerr_endline "                    3 unsupported model, 4 internal invariant failure,";
  prerr_endline "                    5 a resource budget above was exhausted (0 when the";
  prerr_endline "                    search had printed a solution: a stopped run),";
  prerr_endline "                    6 a file could not be written (the proof's directory";
  prerr_endline
    "                    is missing, the disk is full): the proof is incomplete.";
  prerr_endline "";
  prerr_endline
    "  --bits-above W    (M8-bits-encoding-T2, D-0130/D-0132) put every ELIGIBLE integer";
  prerr_endline "                    variable declared wider than W on the BITS encoding:";
  prerr_endline
    "                    bit_length(hi-lo) Booleans x_bit_i, two bound rows, no";
  prerr_endline "                    ladder; its order atoms are minted into the proof on";
  prerr_endline
    "                    demand. `0` (default, D-0199): every eligible variable";
  prerr_endline
    "                    (width 0 and 1 stay order). `none`: the order encoding";
  prerr_endline "                    everywhere, the solver before D-0201.";
  prerr_endline
    "                    A variable in an all_different, gcc, element, maxmin,";
  prerr_endline
    "                    cumulative, int_ne, int_eq_reif or bool2int scope, or";
  prerr_endline
    "                    with holes, stays order at every W (--stats says so).";
  prerr_endline
    "  BAGUETTE_MAX_ORDER_WIDTH, BAGUETTE_MAX_DIRECT_VALUES, BAGUETTE_WIDTH_WARN,";
  prerr_endline
    "  BAGUETTE_MAX_ENCODING_CLAUSES, BAGUETTE_MAX_HEAP_MB, BAGUETTE_BITS_ABOVE";
  prerr_endline "                    the same five, as environment variables. A flag on";
  prerr_endline "                    the command line wins over the environment. Each";
  prerr_endline
    "                    takes an integer or `none`; anything else is an error";
  prerr_endline "                    rather than a silent `none`.";
  prerr_endline "";
  prerr_endline
    "  BAGUETTE_RETENTION=off|keep_all|fifo:N|lbd:N|tiered[:K=N,...]  the \
     learned-constraint";
  prerr_endline
    "                    retention policy; tiered (D-0139) takes keys core, mid,";
  prerr_endline "                    first, inc and mid_every, e.g. tiered:first=500";
  prerr_endline
    "                    (M2-L4). Default `tiered` since D-0226; `off` (or `keep_all`)";
  prerr_endline
    "                    keeps every learned constraint, the default before it.";
  prerr_endline
    "  BAGUETTE_PB_ANALYSIS=on|off  off is the clause path only: no PB conflict analysis";
  prerr_endline
    "                    (M6-T9, a measurement knob; Search.no_pb). Default on.";
  prerr_endline
    "  BAGUETTE_NODE_LIMIT=N  stop as --time-limit does, past N search nodes (M6-T9):";
  prerr_endline
    "                    the deterministic stop, for byte-comparing two builds.";
  prerr_endline "  BAGUETTE_PROOF_AUDIT=0 disables the constraint-id audit (I-X2), which";
  prerr_endline "  is on by default here even though the library's own default is off.";
  prerr_endline
    "  BAGUETTE_HASHCONS=0  every rebuilt derivation writes its own proof line (D-0172):";
  prerr_endline
    "                    the proof before hash-consing, for comparison. Default on.";
  prerr_endline
    "  BAGUETTE_MINIMISE=off|root|local|rec|rec-nofilter  which minimisation rules";
  prerr_endline "                    trim a learned clause (D-0241). Default off.";
  prerr_endline
    "  BAGUETTE_PRIORITY=off|classes  classes runs cheap propagators first, in four";
  prerr_endline "                    cost classes (D-0246). Default off: one FIFO queue.";
  prerr_endline
    "  BAGUETTE_PROBE=off|root  root tries each bound literal of a small domain";
  prerr_endline
    "                    before the first decision and asserts the negation of one";
  prerr_endline
    "                    that fails (failed-literal probing, D-0250). Default off.";
  prerr_endline "                    BAGUETTE_PROBE_BUDGET (propagator runs, 5000000),";
  prerr_endline "                    BAGUETTE_PROBE_CPU (seconds, 10; 0 for none) and";
  prerr_endline
    "                    BAGUETTE_PROBE_WIDTH (largest domain probed, 64) bound it.";
  prerr_endline
    "  BAGUETTE_REST_SATISFIED=on|off  a satisfied learned clause rests on its true";
  prerr_endline "                    literal until a backtrack (D-0173). Default off.";
  prerr_endline "  BAGUETTE_PROPAGATE_LEARNED=on|off  off keeps every learned constraint";
  prerr_endline
    "                    proof-only (a measurement build, M2-L12). Default on.";
  prerr_endline
    "  BAGUETTE_PB_MAX_TERMS=N, BAGUETTE_PB_PROPAGATE_MAX=N  a learned PB row of";
  prerr_endline "                    more than N terms is not derived, or derived but not";
  prerr_endline "                    propagated (D-0226). Default 0: no cap.";
  prerr_endline "  BAGUETTE_DEBUG=1  the invariant checks of docs/INVARIANTS.md (slow).";
  prerr_endline
    "  BAGUETTE_CONSISTENCY=1  the brute-force consistency oracle (M2-T10), with";
  prerr_endline
    "                    BAGUETTE_CONSISTENCY_CAP=N its tuple budget (4096) and";
  prerr_endline "                    BAGUETTE_CONSISTENCY_TRACE=1 its report.";
  prerr_endline "  Measurements on stderr: BAGUETTE_CDCL_STATS, BAGUETTE_MEMO_STATS,";
  prerr_endline "                    BAGUETTE_MINIMISE_STATS, BAGUETTE_PROBE_STATS and";
  prerr_endline
    "                    BAGUETTE_WAKE_STATS (=1), BAGUETTE_RETENTION_TRACE=N,";
  prerr_endline
    "                    BAGUETTE_RETENTION_TRACE_HEAP=1. BAGUETTE_TEST_VALUE_CHOICE";
  prerr_endline "                    is for the test suites only.";
  exit exit_usage

(* A limit from the command line or the environment. A value that is neither an integer
   nor `none` is a usage error and not a silent `none`, because a mistyped budget that
   quietly means "no budget" is exactly the failure a budget exists to stop. *)
let set_limit what r v =
  match Encoding.limit_of_string ~what v with
  | l -> r := l
  | exception Encoding.Bad_limit (what, v) ->
      Printf.eprintf
        "%s: %S is not a limit. Give a non-negative integer, or `none` for no limit.\n"
        what v;
      usage ()

(* Where a run without --proof writes its proof (M9-no-proof-T5, D-0163). It is decided
   here and nowhere else. The user decided on 2026-11-19 that such a run writes its proof
   and KEEPS it. The DIRECTORY is still the user's to confirm: what follows is the
   proposal on record, and changing it is an edit to [default_proof_prefix] alone.

     baguette DIR/foo.fzn            ->  ./foo.opb and ./foo.pbp, in the CURRENT directory
     baguette /tmp/mznfileXYZ.fzn    ->  ./baguette-proof.opb and .pbp, and a stderr note

   The result is a PREFIX, as --proof's argument is: the run appends .opb and .pbp. Only a
   `.fzn` extension is dropped, so no model file is ever its own proof's name (`foo` gives
   foo.opb, and a model called `x.pbp` gives x.pbp.pbp).

   The second line is the MiniZinc case. `minizinc --solver baguette m.mzn` flattens to a
   temporary `mznfile<random>.fzn` and passes only that path after the flags (measured on
   MiniZinc 2.10.1: neither the argv, the environment nor the .fzn names the .mzn), so a
   name from the model would be a new meaningless name on every run. A fixed name in the
   current directory is the next best thing, and the note on stderr gives its full path
   because the user never typed it. `--proof PREFIX` and `--no-proof` are both extraFlags
   of tools/baguette.msc, so a MiniZinc user can name the proof or skip it.

   A file of the same name is OVERWRITTEN, as `--proof PREFIX` always has done, because
   it is the output of a previous run, like a compiler's. Two runs of the same model, or
   two MiniZinc runs, in the same directory at the same time therefore write over each
   other; give each its own --proof. *)
let mzn_temp_model model =
  let b = Filename.basename model in
  String.starts_with ~prefix:"mznfile" b && Filename.check_suffix b ".fzn"

let default_proof_prefix model =
  let b = Filename.basename model in
  if mzn_temp_model model then "baguette-proof"
  else if Filename.check_suffix b ".fzn" then Filename.chop_suffix b ".fzn"
  else b

(* The command line, into [options]. Two rules hold for every option.

   The environment is read first and the command line second, so a flag beats the
   environment variable of the same limit ([Encoding.limits_from_env] reads
   BAGUETTE_MAX_ORDER_WIDTH, _MAX_DIRECT_VALUES, _WIDTH_WARN, _BITS_ABOVE,
   _MAX_ENCODING_CLAUSES and _MAX_HEAP_MB).

   A value that does not parse is a usage error, exit 2, and never a silent default.
   A measurement run whose flag was silently not in force compares the default against
   itself and reads as "no change"; CLAUDE.md records that trap twice (a before/after
   that used the same binary on both sides). The same rule holds for the
   contradictions checked after the loop: --no-proof with --proof, --chrono without
   --cdcl, --e2e without --proof. *)
let parse_args argv =
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
  let time_limit = ref None in
  let no_proof = ref false in
  let restarts = ref Restart.No_restarts in
  let phase_saving = ref false in
  let search = ref Search.Annotated in
  let reuse_trail = ref false in
  let cdcl = ref Search.default_config.Search.cdcl in
  let chrono = ref Search.default_config.Search.chrono in
  (* [restarts_given] and [search_given] let `-f` fill only what was not asked for
     explicitly, in either order on the command line (the standard flags, M7-T32). *)
  let restarts_given = ref false and search_given = ref false in
  let intermediate = ref false in
  let n_solutions = ref None in
  let free_search = ref false in
  let seed = ref None in
  let threads = ref None in
  let mzn_stats = ref false in
  let verbose = ref false in
  let e2e = ref false in
  (* A standard flag's integer argument. Malformed is a usage error, as everywhere in
     this parser. *)
  let int_arg flag ~ok ~what i =
    if i + 1 >= Array.length argv then usage ();
    match int_of_string_opt argv.(i + 1) with
    | Some n when ok n -> n
    | _ ->
        Printf.eprintf "%s: %S is not %s.\n" flag argv.(i + 1) what;
        usage ()
  in
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
      | "--no-proof" ->
          no_proof := true;
          go (i + 1)
      | "--e2e" ->
          e2e := true;
          go (i + 1)
      (* The opt-in search strategies (M10-search-strategy-T2 and T3, D-0137). A
         malformed policy is a usage error, never a silent `none`. *)
      | "--restarts" ->
          if i + 1 >= Array.length argv then usage ();
          (match Restart.of_string argv.(i + 1) with
          | Ok p ->
              restarts := p;
              restarts_given := true
          | Error msg ->
              Printf.eprintf "--restarts: %s\n" msg;
              usage ());
          go (i + 2)
      | "--phase-saving" ->
          phase_saving := true;
          go (i + 1)
      | "--search" ->
          if i + 1 >= Array.length argv then usage ();
          (match argv.(i + 1) with
          | "annotation" -> search := Search.Annotated
          | "activity" -> search := Search.Activity_order
          | "alternate" -> search := Search.Alternate
          | other ->
              Printf.eprintf "--search: %S is not annotation, activity or alternate\n"
                other;
              usage ());
          search_given := true;
          go (i + 2)
      | "--reuse-trail" ->
          reuse_trail := true;
          go (i + 1)
      | "--cdcl" ->
          cdcl := true;
          go (i + 1)
      | "--chrono" ->
          if i + 1 >= Array.length argv then usage ();
          (match int_of_string_opt argv.(i + 1) with
          | Some t when t >= 0 -> chrono := Some t
          | _ ->
              Printf.eprintf "--chrono: %S is not a level count >= 0\n" argv.(i + 1);
              usage ());
          go (i + 2)
      | "--time-limit" ->
          if i + 1 >= Array.length argv then usage ();
          (match float_of_string_opt argv.(i + 1) with
          | Some s when s >= 0. && Float.is_finite s -> time_limit := Some s
          | _ ->
              Printf.eprintf
                "--time-limit: %S is not a number of seconds. Give a non-negative number.\n"
                argv.(i + 1);
              usage ());
          go (i + 2)
      (* The encoding's width limits. The two refusals are off by default since M7-T1
         turned the old hard caps into options (D-0065: the hardware limits become
         options, defaulting off); --width-warn is a warning and defaults to the old
         cap, 10000. They set Encoding's refs rather than riding in [options], because
         the front end consults them during [Compile.compile] and the .opb writer
         consults them again later. There is no single call site to thread them
         through, and a ref that the CLI sets once, before anything is compiled, is
         honest about that. *)
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
      (* The two resource budgets (M7-T8, exit 5 when exceeded), set as refs for the
         same reason: they are consulted deep inside [Compile] and again by the Gc
         alarm, with no single call site to thread through. Default none, per
         D-0065. *)
      | "--max-encoding-clauses" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--max-encoding-clauses" Encoding.encoding_budget argv.(i + 1);
          go (i + 2)
      | "--max-heap-mb" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--max-heap-mb" Encoding.heap_limit_mb argv.(i + 1);
          go (i + 2)
      (* The threshold above which an integer goes on the bits encoding, its binary
         digits instead of one Boolean per value (M8-bits-encoding-T2, D-0130 section
         10). The same shape, consulted by [Compile] at every declaration; [set_limit]
         gives it `none`'s spelling and the typo refusal of the other five. *)
      | "--bits-above" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--bits-above" Encoding.bits_above argv.(i + 1);
          go (i + 2)
      (* The MiniZinc standard flags (M7-T32, D-0150), mapped as the header says. *)
      | "-a" ->
          all_solutions := true;
          go (i + 1)
      | "-i" ->
          intermediate := true;
          go (i + 1)
      | "-n" ->
          n_solutions :=
            Some (int_arg "-n" ~ok:(fun n -> n >= 1) ~what:"a positive integer" i);
          go (i + 2)
      | "-f" ->
          free_search := true;
          go (i + 1)
      | "-t" ->
          let ms =
            int_arg "-t"
              ~ok:(fun n -> n >= 0)
              ~what:"a time limit in milliseconds (a non-negative integer)" i
          in
          time_limit := Some (float_of_int ms /. 1000.);
          go (i + 2)
      | "-r" ->
          seed := Some (int_arg "-r" ~ok:(fun _ -> true) ~what:"an integer seed" i);
          go (i + 2)
      | "-p" ->
          threads :=
            Some (int_arg "-p" ~ok:(fun n -> n >= 1) ~what:"a positive integer" i);
          go (i + 2)
      | "-s" ->
          stats := true;
          mzn_stats := true;
          go (i + 1)
      | "-v" ->
          verbose := true;
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
  (* `-f` is Chuffed's free search: the annotation's order alternating with the activity
     order under restarts (D-0137 section 4), with phase saving as Chuffed's SAT layer
     has it, and Luby restarts on D-0137's unit of 100 conflicts (section 0,
     [Restart.default_unit]). An explicit --search or --restarts wins wherever it sits
     on the line. *)
  if !free_search then (
    if not !search_given then search := Search.Alternate;
    (if not !restarts_given then
       restarts :=
         match Restart.of_string "luby" with
         | Ok p -> p
         | Error msg -> failwith ("Restart.of_string \"luby\": " ^ msg));
    phase_saving := true);
  (* --chrono sets a threshold of the CDCL loop (M19-config-T11, D-0224). Under the
     default search it would be silently ignored, so it is refused. *)
  if !chrono <> None && not !cdcl then (
    prerr_endline
      "baguette: --chrono (or BAGUETTE_CHRONO) sets how far the CDCL loop backjumps, and \
       needs --cdcl (or BAGUETTE_CDCL=1).";
    exit exit_usage);
  (* The two flags contradict each other, and a silent choice between them would leave
     a measurement whose flag was never in force (M9-no-proof-T2). A usage error, exit
     2, and no file is touched. *)
  if !no_proof && !proof_prefix <> None then (
    prerr_endline
      "baguette: --no-proof and --proof PREFIX contradict each other: one asks for no \
       proof and the other for where to write it. Give one of them.";
    exit exit_usage);
  if !e2e && !proof_prefix = None then (
    prerr_endline
      "baguette: --e2e writes a proof to be checked against cake_pb_cp's .opb, so it \
       needs --proof PREFIX.";
    exit exit_usage);
  match !model with
  | None -> usage ()
  | Some m ->
      (* M9-no-proof-T5: from here on [proof_prefix] is [None] only under --no-proof. *)
      let proof_prefix, proof_note =
        match !proof_prefix with
        | Some p -> (Some p, false)
        | None when !no_proof -> (None, false)
        | None -> (Some (default_proof_prefix m), mzn_temp_model m)
      in
      {
        model = m;
        proof_prefix;
        proof_note;
        proof_comments = !proof_comments;
        all_solutions = !all_solutions;
        time = !time;
        stats = !stats;
        time_limit = !time_limit;
        no_proof = !no_proof;
        restarts = !restarts;
        phase_saving = !phase_saving;
        search = !search;
        reuse_trail = !reuse_trail;
        cdcl = !cdcl;
        chrono = !chrono;
        intermediate = !intermediate;
        n_solutions = !n_solutions;
        seed = !seed;
        threads = !threads;
        mzn_stats = !mzn_stats;
        verbose = !verbose;
        e2e = !e2e;
      }

(* ------------------------------------- --time: the solver's own CPU phases (M1-T35) *)

(* --time prints, on stderr, how much process CPU each phase of the run took, so that
   solve time can be told apart from process start-up (M1-T35). Why that is needed: the
   proof benchmark (M3-T5) measured a floor of 4.0 ms to start this binary and 4.6 ms
   to start the checker, and found 15 of the 18 models in the suite sitting AT that
   floor with 9-66% spread. Their "solve ms" column timed `exec`, not this solver, and
   until the solver could report its own numbers no timing claim about it was
   supportable from the model suite in either direction. That is why bench/README.md
   says D-0026's falsifier cannot be run (D-0026 made reasons declarative data and
   predicted it would cost no speed; M3-T5 was to test that prediction).

   ---------------------------------------------------------------------------
   The clock is CPU time, not wall time
   ---------------------------------------------------------------------------

   Every number [--time] reports is [Sys.time], process CPU. The one exception is the
   --time-limit CHECK and the `wall=` field beside `cpu=` on the `limit:` lines, which
   read the wall clock since M6-T10 (bin/dune links `unix` for Unix.gettimeofday and
   nothing else). The harnesses kill on wall time, and a CPU limit under load loses
   that race and leaves no stats behind; a limit and a measurement want different
   clocks. For the measurements, CPU is the better instrument rather than a compromise,
   and both halves of that were measured on this switch rather than assumed:

     * RESOLUTION. The smallest non-zero delta of [Sys.time] over 2000 consecutive
       samples is exactly 1e-6 s. It is NOT the 10 ms CLK_TCK granularity of times(2)
       that [Sys.time] used to have; this runtime reaches clock_gettime.
     * WHAT IT COUNTS. CLOCK_PROCESS_CPUTIME_ID: user + system CPU consumed by this
       process since the process was created. So it EXCLUDES every moment the process
       spent off the CPU (descheduled behind another session's `dune build`, or
       blocked on I/O), which is precisely the noise bench/README.md warns about. And
       it INCLUDES the CPU burned before OCaml ever reached this file, which is what
       makes [startup] below measurable at all.
     * THE ALTERNATIVE WAS WORSE. /proc/self/schedstat reports nanoseconds and looks
       finer. Measured here, its smallest non-zero delta is 1.9 ms, because the
       scheduler only updates it at its own tick. It cannot see a 400 us parse.

   Two consequences, to be repeated wherever these numbers are quoted:

   1. A CPU number and a wall number are different measurements. On a busy machine CPU
      is BELOW wall, and the difference is time the process was not running. It is not
      an error bar, and the two must not be averaged.
   2. [startup] IS process start-up. It is reported so that it can be subtracted, not
      folded in. D-0023 (the move to VeriPB 3.0) and D-0025 (its default flip) both
      retracted a speed claim, and the way to avoid a third is to publish the
      contaminated part as its own number.

   ---------------------------------------------------------------------------
   The [search] phase split into proof emission and the rest (M1-T47)
   ---------------------------------------------------------------------------

   The [search] phase is propagation, search AND the proof lines emitted during them,
   and every emission point is below [Search.solve], out of this file's reach. So the
   writer keeps its own accumulator around its output calls ([Writer.emitted_us]), and
   [search] is reported as two more rows, [emit] and [propag] (M1-T47 separated proof
   emission time from propagation time this way).

   THEY ARE BOUNDS, NOT FIGURES. [Writer] accumulates the time it spends WRITING a
   line; the time spent BUILDING that line's body (Pol.to_string_cited,
   Opb.constr_to_string, the Printf.sprintf at each rule's call site) is spent before
   the writer's output call is entered and is not in [emit]. So:

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

  (* The derived rows [emit] and [propag]. They are a SPLIT of [search], not phases of
     their own, so they are deliberately not in [phases]: putting them there would make
     the sum that produces [other] count the search twice. [emit_lines] is a count, not a
     duration, and is printed with a `lines` unit so that nothing reading `$4 == "us"`
     picks it up as a timing. *)
  let emit_us = ref 0
  let emit_lines = ref 0
  let have_emit = ref false

  (* The cost of ONE [Sys.time] read, in nanoseconds, measured on this machine under
     this load rather than taken from a table. It is what [emit] and [propag] each
     carry once per emitted line. On a 545-line proof it is half of [emit], far too
     large to leave folded in silently.

     Called from [report], AFTER every number the report prints has been taken, so the
     ~0.4 ms it costs lands in no phase and contaminates nothing. That placement is
     the whole reason this is a function and not a constant: a calibration run before
     the solve would show up in `rest` and move the very table it exists to correct.

     MINIMUM OF BURSTS, NOT A MEAN, for the reason bench/README.md section 2 gives for
     every other number in this project: a mean folds in whatever else the machine was
     doing, and several sessions build on the same machine. Nine bursts of 256 reads,
     minimum taken, holds inside a few percent. A single 512-read burst was tried first
     and ranged 836..1871 ns across five consecutive runs of the same model, which
     would have made the published correction swing by a factor of two. *)
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

  (* The phase in flight, for the `limit: killed` line [solve] prints on a signal
     (M6-T9). One store per phase, on or off; it is read by nothing else. *)
  let current = ref "startup"

  (* Free when timing is off: one store, one dereference and the call itself. A phase
     whose body raises records nothing, which is why the report prints an `other` row
     instead of pretending the rows always add up. *)
  let phase name f =
    current := name;
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
        "Encoding.write_opb: the .opb built, written and closed (0 under --no-proof)"
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
    | "pbpclose" -> "the .pbp flushed and closed"
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

(* ----------------------------------------------------- the proof channel and audit *)

(* The proof channel: PREFIX.pbp, which the run keeps (see the header and
   [default_proof_prefix]). *)
let open_proof_channel opts =
  (* Under --no-proof, the null channel. Nothing is written through it (the writer over
     it is [Writer.create ~null:true] and every rule returns before rendering); it
     exists so that the writer has a channel to be over and the pipeline below keeps its
     one shape. [parse_args] has already refused `--no-proof` beside `--proof`, and gives
     every other run a prefix. *)
  match opts.proof_prefix with
  | _ when opts.no_proof -> open_out Filename.null
  | Some prefix -> open_out (prefix ^ ".pbp")
  | None -> invalid_arg "open_proof_channel: no prefix outside --no-proof"

let audit_enabled () =
  (* The I-X2 audit: every constraint id the writer mints is deleted exactly once,
     checked at the conclusion. The library defaults it off and turns it on with
     BAGUETTE_PROOF_AUDIT=1 (docs/ARCHITECTURE.md section 6). The CLI inverts that
     default deliberately, and BAGUETTE_PROOF_AUDIT=0 turns it off: the audit is cheap
     at these sizes, it has already caught one real defect (D-0015: a root
     refutation's intermediate steps left undeleted at level 0), and a user running the
     solver should get the check without having known to ask for it. *)
  match Sys.getenv_opt "BAGUETTE_PROOF_AUDIT" with Some "0" -> false | _ -> true

(* ----------------------------------------------- measurement knobs (environment) *)

(* The search's measurement knobs, read from the environment when [solve] builds its
   [Search.config]. They are environment variables rather than flags because each is a
   MEASUREMENT knob, not a user-facing choice: it exists so that a cost can be measured
   with a feature on and off, by anyone, on the same binary. Unset, each one gives the
   library's default, so a normal run is unaffected. Every one follows [parse_args]'s
   rule: a value that does not parse FAILS with exit 2 rather than falling back to the
   default. Other switches are read where they act (BAGUETTE_CDCL and BAGUETTE_CHRONO by
   [Search.default_config], the encoding limits by [Encoding.limits_from_env],
   BAGUETTE_HASHCONS, BAGUETTE_PROBE and the rest by their own modules); [usage] lists
   them all.

   [retention_policy] is [Search.config.retention], the learned-constraint database's
   eviction policy (M2-L4 made the policies swappable): BAGUETTE_RETENTION, plus
   BAGUETTE_RETENTION_TRACE=N for a trace of the database. The default is
   [Retention.default], `tiered` since D-0226. M2-L4's test (c) measures .pbp bytes and
   checker time with the policy on and off. *)
let retention_policy () =
  (match Sys.getenv_opt "BAGUETTE_RETENTION_TRACE" with
  | None -> ()
  | Some v -> (
      match int_of_string_opt v with
      | Some n when n >= 0 -> Retention.trace_every := n
      | _ ->
          prerr_endline
            (Printf.sprintf
               "baguette: BAGUETTE_RETENTION_TRACE=%S is not a count. Use N >= 0." v);
          exit 2));
  let bad v =
    prerr_endline
      (Printf.sprintf
         "baguette: BAGUETTE_RETENTION=%S is not a policy. Use off (or keep_all), fifo:N \
          or lbd:N, where N is the database cap, or \
          tiered[:core=2,mid=6,first=2000,inc=300,mid_every=10000] (D-0139)."
         v);
    exit 2
  in
  (* The tiered policy (D-0139: the database made evictable in three tiers by
     LBD): `tiered`, or `tiered:` followed by comma-separated KEY=N overriding
     [Retention.default_tier_params] (keys core, mid, first, inc, mid_every). An unknown
     key, a repeated one or a bad number FAILS, by the same rule as the rest. *)
  let tiered v spec =
    let d = Retention.default_tier_params in
    let seen = Hashtbl.create 5 in
    let set (p : Retention.tier_params) kv =
      match String.index_opt kv '=' with
      | None -> bad v
      | Some i -> (
          let k = String.sub kv 0 i in
          let n = String.sub kv (i + 1) (String.length kv - i - 1) in
          if Hashtbl.mem seen k then bad v;
          Hashtbl.replace seen k ();
          match int_of_string_opt n with
          | None -> bad v
          | Some n -> (
              match k with
              | "core" -> { p with core = n }
              | "mid" -> { p with mid = n }
              | "first" -> { p with first = n }
              | "inc" -> { p with inc = n }
              | "mid_every" -> { p with mid_every = n }
              | _ -> bad v))
    in
    let params =
      if spec = "" then d else List.fold_left set d (String.split_on_char ',' spec)
    in
    try Retention.tiered ~params () with Invalid_argument _ -> bad v
  in
  match Sys.getenv_opt "BAGUETTE_RETENTION" with
  | None -> Retention.default
  | Some ("off" | "keep_all") -> Retention.keep_all
  | Some "tiered" -> tiered "tiered" ""
  | Some v when String.length v > 7 && String.sub v 0 7 = "tiered:" ->
      tiered v (String.sub v 7 (String.length v - 7))
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

(* [Search.config.pb], BAGUETTE_PB_ANALYSIS=on|off (M6-T9). `off`, which is
   [Search.no_pb], sends every conflict down the clause path (1UIP clause learning over
   order literals, M2-L3) and never asks PB conflict analysis. It exists so that PB
   analysis's accepted cost, an order of magnitude on width_sat_depth when it was wired
   in (D-0062), can be measured on real instances rather than argued about. *)
let pb_analysis () =
  match Sys.getenv_opt "BAGUETTE_PB_ANALYSIS" with
  | None | Some "on" -> true
  | Some "off" -> false
  | Some v ->
      prerr_endline
        (Printf.sprintf
           "baguette: BAGUETTE_PB_ANALYSIS=%S is not a setting. Use on or off." v);
      exit 2

(* BAGUETTE_NODE_LIMIT=N stops the search exactly as --time-limit does, at the first
   node entry past N nodes (M6-T9). A time stop lands on a different node on every run,
   so two binaries cannot be compared byte for byte under it; a node stop lands on the
   same node every time, so "the proofs of the same N-node prefix are identical" is a
   checkable claim about a performance change. *)
let node_limit () =
  match Sys.getenv_opt "BAGUETTE_NODE_LIMIT" with
  | None -> None
  | Some v -> (
      match int_of_string_opt v with
      | Some n when n >= 0 -> Some n
      | _ ->
          prerr_endline
            (Printf.sprintf
               "baguette: BAGUETTE_NODE_LIMIT=%S is not a node count. Use a non-negative \
                integer."
               v);
          exit 2)

(* [Search.config.propagate_learned], BAGUETTE_PROPAGATE_LEARNED=on|off. `off` is the
   build in which every learned constraint is proof-only, written to the proof and never
   propagated, which is what this solver was before M2-L12 made learned units and
   clauses propagate; M2-L12 has to be able to measure against it. *)
let propagate_learned () =
  match Sys.getenv_opt "BAGUETTE_PROPAGATE_LEARNED" with
  | None | Some "on" -> true
  | Some "off" -> false
  | Some v ->
      prerr_endline
        (Printf.sprintf
           "baguette: BAGUETTE_PROPAGATE_LEARNED=%S is not a setting. Use on or off." v);
      exit 2

(* [Search.config.rest_satisfied], BAGUETTE_REST_SATISFIED=on|off (M11-complexity-T17).
   On, a satisfied learned clause rests on its true literal until a backtrack: D-0173
   found that the learned clauses which "cannot prune" are the satisfied ones. The
   pruning is the same but the propagation order differs, so the trees and proofs do
   too, which makes it a change of default behaviour for the user to decide; the
   default is off. *)
let rest_satisfied () =
  match Sys.getenv_opt "BAGUETTE_REST_SATISFIED" with
  | None -> Search.default_config.Search.rest_satisfied
  | Some "on" -> true
  | Some "off" -> false
  | Some v ->
      prerr_endline
        (Printf.sprintf
           "baguette: BAGUETTE_REST_SATISFIED=%S is not a setting. Use on or off." v);
      exit 2

(* -------------------------------------------------- --stats: the reports on stderr *)

(* What the encoding cost, on stderr under --stats. This is the counter half of the
   diagnostic that replaced the width refusal when M7-T1 made it an option. The warning
   half fires as a variable is declared ([Encoding.declare_int]) and does not wait to
   be asked. This half is here because the TOTAL is the number the per-variable cap
   never bounded: a thousand variables at width 9 999 was always ten million clauses
   and always slipped through.

   Its text is written for a reader who has not read D-0028 (a justification's size is
   proportional to the declared domain width), by the same rule as the warning. *)
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
    (Encoding.order_width_limit_string ());
  (* M7-T8. The two budgets whose exhaustion is exit 5, printed beside the total they
     bound so a reader comparing "ladder + direct" against "budget" is reading two
     numbers in the same units, on adjacent lines. *)
  Printf.eprintf
    "stats: %-10s %10s        --max-encoding-clauses (bounds ladder+direct)\n" "budget"
    (Encoding.encoding_budget_string ());
  Printf.eprintf "stats: %-10s %10s        --max-heap-mb (MB of OCaml heap)\n" "heap"
    (Encoding.heap_limit_string ());
  (* How many variables went on the bits encoding (M8-bits-encoding-T2, D-0130 section
     10), how many bound rows that cost, and how many eligible-by-width variables the
     scope rule held back, by family: the line D-0130 section 12 says a comparison must
     read. *)
  Printf.eprintf
    "stats: %-10s %10d vars   bits-encoded (--bits-above %s); held back: %s\n" "bits"
    c.Encoding.c_bits_vars
    (Encoding.bits_above_string ())
    (match c.Encoding.c_held_back with
    | [] -> "none"
    | hs -> String.concat ", " (List.map (fun (f, n) -> Printf.sprintf "%s: %d" f n) hs));
  Printf.eprintf "stats: %-10s %10d lines  bound rows (2 per bits variable)\n" "bitsrows"
    c.Encoding.c_bits_rows;
  (* Choice groups posted, one per maxmin scope with a bits variable, each n selector
     rows and one clause (maxmin over bits, M8-bits-encoding-T3, D-0134 section 2.5). *)
  Printf.eprintf "stats: %-10s %10d groups selector rows + clause (maxmin over bits)\n"
    "choices" c.Encoding.c_choices

(* ------------------------------------------- ending a run: resource and write failure *)

(* [Some code] when a resource arm ended the proof before raising, with the status to
   exit with. The proof is then complete and there is nothing to warn of. Ending the
   proof is M6-T24's rule (D-0225): an interrupted run closes its proof where it stands,
   with the strongest conclusion it has. *)
let proof_ended : int option ref = ref None

(* Exit 5, or 0 when the proof was ended with an incumbent. A resource overrun (M7-T8)
   can fire at a DECLARATION, before any file exists, or at [ensure_direct], which runs
   inside [start_proof] with the .opb already on disk and the .pbp part-written. The
   guard cannot tell a reader which from inside [Encoding], and half a proof that
   veripb happens to parse is the worst outcome available here, so unless the proof was
   ended the binary says the cautious thing whenever a proof was being written. *)

let exit_out_of_resource opts =
  let warn_partial_proof () =
    match opts.proof_prefix with
    | None -> ()
    | Some p ->
        Printf.eprintf
          "  A proof was being written: %s.opb / %s.pbp are INCOMPLETE -- the run \
           stopped while\n\
          \  writing them. Do not check them and do not keep them; they are not a proof of\n\
          \  anything. Re-run with a larger budget, or with none.\n"
          p p
  in
  let code =
    match !proof_ended with
    | Some code -> code
    | None ->
        warn_partial_proof ();
        exit_resource
  in
  flush stderr;
  exit code

(* Exit 6: a write that failed, reported in one line instead of the runtime's
   `Fatal error: exception Sys_error` (M22-review-T5, D-0248). What [solve] writes is the
   .opb, its .opb.rows body, the .pbp, the e2e prefix and stdout, and OCaml reports a
   failure of any of them as [Sys_error], or as [Fun.Finally_raised (Sys_error _)] when it
   is the .pbp's [close_out] in [solve]'s [finally], which flushes the last of the buffer.
   A full disk names no file ("No space left on device"), so the line names the proof's.
   The final answer is printed after that [close_out] and a stopped run's marker after its
   conclusion's flush, so a run that ends here has printed no verdict on a proof that is
   not there; an optimisation run may have printed improving solutions before it, as a
   stopped one does. The proof is left as it is, incomplete, and the line says so. *)
let exit_write_failed opts msg =
  (match opts.proof_prefix with
  | Some p when not opts.no_proof ->
      Printf.eprintf
        "baguette: a write failed (%s); the proof %s.opb / %s.pbp is INCOMPLETE, do not \
         check or keep it\n"
        msg p p
  | _ -> Printf.eprintf "baguette: a write failed (%s)\n" msg);
  flush stderr;
  exit exit_write

(* What the bits arm minted into the proof (M8-bits-encoding-T2, D-0130 section 10).
   Every count is a level-0 line retired by the conclusion's sweep. [atoms/prune] is
   GCS's quadratic made visible: atoms minted per bits-arm pruning line written. *)
let report_atoms (a : Encoding.atom_stats) =
  Printf.eprintf
    "stats: %-10s %10d atoms  order atoms minted by red pairs over bits variables\n"
    "atoms" a.Encoding.a_atoms;
  Printf.eprintf "stats: %-10s %10d lines  sparse-chain links between minted atoms\n"
    "atomlinks" a.Encoding.a_links;
  Printf.eprintf
    "stats: %-10s %10d pairs  rup bridge pairs for order variables in mixed rows\n"
    "bridges" a.Encoding.a_bridges;
  Printf.eprintf "stats: %-10s %10d pairs  degree-0 bound lines for order variables\n"
    "boundlines" a.Encoding.a_bound_lines;
  Printf.eprintf "stats: %-10s %10d lines  bits-arm pol lines (prunings and conflicts)\n"
    "bitsprune" a.Encoding.a_bits_prunings;
  if a.Encoding.a_bits_prunings > 0 then
    Printf.eprintf "stats: %-10s %10.3f        atoms minted per bits-arm pruning line\n"
      "atoms/prune"
      (float_of_int a.Encoding.a_atoms /. float_of_int a.Encoding.a_bits_prunings)

(* The SHAPE of the proof that was just written, on stderr under --stats: how many
   lines are `pol` and how many `rup`, and the tokens the `pol` lines carry, in total and
   at the widest one, with that one's origin (M8-bits-encoding-T5, D-0131).

   Why the shape matters, as D-0127 measured it on the checker: VeriPB 3.0.2 checks a
   `rup` by unit propagation, which is linear in what it walks, and a `pol` by
   cutting-planes arithmetic whose every `+` costs the size of the accumulator. So a
   `pol` of Theta(w) tokens over a variable of declared width w is the one line in a
   proof whose check time grows faster than its byte count. Since D-0131 the solver
   writes its ladder walks as `rup`; what is left as `pol` is a derivation the checker
   cannot reach by propagation (a counting global's, a learned PB row's), and this
   report is how a wide one is seen by name. *)
let report_proof_shapes (sh : Writer.shape_stats) =
  prerr_endline
    "stats: proof-line shapes (M8-bits-encoding-T5, D-0131). A `rup` is checked by unit";
  prerr_endline
    "stats: propagation, linear in what it walks; a `pol` by arithmetic that costs the";
  prerr_endline
    "stats: accumulator's size per `+`, so a Theta(w)-token `pol` is the line to look at.";
  Printf.eprintf "stats: %-10s %10d lines  `rup` lines written\n" "rup" sh.Writer.n_rup;
  Printf.eprintf "stats: %-10s %10d lines  `pol` lines written\n" "pol" sh.Writer.n_pol;
  Printf.eprintf "stats: %-10s %10d tokens over every `pol` (operands + operators)\n"
    "pol-tokens" sh.Writer.pol_tokens;
  if sh.Writer.n_pol = 0 then
    Printf.eprintf "stats: %-10s %10s        no `pol` written\n" "pol-widest" "-"
  else
    Printf.eprintf "stats: %-10s %10d tokens in the widest `pol` -- %s\n" "pol-widest"
      sh.Writer.pol_tokens_max sh.Writer.pol_widest

(* Under --no-proof, the line that says what this run is NOT, printed in place of the
   proof-shape and atom reports: those would read all zeros here, which to anyone
   grepping `stats:` looks like a proof with no `pol` in it rather than no proof. *)
let report_no_proof () =
  Printf.eprintf "stats: %-10s %10d %-6s %s\n" "no-proof" 1 "bool"
    "--no-proof: NO PROOF EXISTS for this run; the answer on stdout is UNVERIFIED";
  prerr_endline
    "stats: and is not a result (SPEC 1, D-0126). A measurement instrument: what the";
  prerr_endline
    "stats: proof costs is what the same run WITH a proof costs beyond this one. No";
  prerr_endline "stats: proof-shape or atom counters: nothing was written."

(* The opt-in search strategies' counters (restarts, phase saving, the activity order,
   D-0137), printed only when one of them is on, so that a default run's --stats is
   unchanged line for line. *)
let search_name = function
  | Search.Annotated -> "annotation"
  | Search.Activity_order -> "activity"
  | Search.Alternate -> "alternate"

let report_strategy opts (st : Search.stats) =
  if
    opts.restarts <> Restart.No_restarts
    || opts.phase_saving
    || opts.search <> Search.Annotated
  then (
    Printf.eprintf "stats: %-10s %10d runs   %s\n" "restarts" (Search.stats_restarts st)
      (Printf.sprintf "restarts taken under --restarts %s (M10-T2, D-0137)"
         (Restart.to_string opts.restarts));
    Printf.eprintf "stats: %-10s %10d nodes  %s\n" "unexplored"
      st.Search.restart_unexplored
      "second children a restart left undispatched (in the M1-T36 identity)";
    Printf.eprintf "stats: %-10s %10d levels %s\n" "kept" st.Search.restart_targets
      "levels kept by restarts, summed (--reuse-trail; 0 for full restarts)";
    (match Search.stats_activity st with
    | None -> ()
    | Some a ->
        Printf.eprintf "stats: %-10s %10d bumps  %s\n" "activity" (Activity.n_bumps a)
          (Printf.sprintf "variable bumps under --search %s (%d rescales)"
             (search_name opts.search) (Activity.n_rescales a)));
    match Search.stats_phase st with
    | None -> ()
    | Some ph ->
        Printf.eprintf "stats: %-10s %10d vals   %s\n" "phases" (Phase.n_saves ph)
          "values saved at a level's undo (--phase-saving)";
        Printf.eprintf "stats: %-10s %10d decs   %s\n" "phase-used" (Phase.n_used ph)
          "decisions whose value a saved phase chose")

(* [Search.stats] rendered on stderr, one `stats: ` line each, under --stats: the
   search-tree counters (M1-T36: a real node counter in Search) and the learning
   counters after them.

   WHY THIS IS NOT FOLDED INTO --time. The two instruments cost different things and
   must be separable for that reason. --time takes a [Sys.time] per phase and one per
   emitted proof line, and bench/run_bench.sh therefore runs it on its own dedicated
   repeats so that none of it lands in a number printed as "solve ms" (M1-T47). These
   counters cost three int increments per node and no clock reads, so they can be left
   on during a timed run. That is the point: the tree size and the time have to be
   readable off the SAME run before "the same tree costs no more" (D-0026's prediction)
   means anything.

   STDERR ONLY, like the timings, because SPEC 2.2 pins stdout byte for byte.

   The unit word is the third field and it is `nodes`/`decs`/`levels`, never `us`, so
   that anything reading the timing report's `$4 == "us"` cannot pick these up as
   durations. `emitln` follows the same discipline with its `lines` unit. *)
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
  Printf.eprintf "stats: %-10s %10d nodes  %s\n" "conflicts" st.Search.conflicts
    "nodes whose propagation failed, root included (M6-T9)";
  Printf.eprintf "stats: %-10s %10d levels %s\n" "maxdepth" st.Search.max_depth
    "deepest decision stack reached: the depth of the TREE, not of the proof";
  Printf.eprintf "stats: %-10s %10d %-6s %s\n" "exhausted"
    (if exhausted then 1 else 0)
    "bool" "1 if the search closed its whole tree (UNSAT), 0 if it stopped at a solution";
  Printf.eprintf "stats: %-10s %10d nodes  %s\n" "skipped" st.Search.skipped
    "siblings NOT explored: one per backjump (M2-L3). 0 means no backjump happened";
  Printf.eprintf "stats: %-10s %10d cls    %s\n" "learned" st.Search.n_learned
    "1UIP clauses derived and put on the page, level 0 (M2-L3, D-0044 fork ii)";
  Printf.eprintf "stats: %-10s %10d asks   %s\n" "later"
    !Baguette_core.Reason.materialisations
    "deferred reasons materialised (D-0124): trace once per entry, 1UIP, and the closure";
  Printf.eprintf "stats: %-10s %10d memos  %s\n" "cites"
    !Baguette_core.Analysis.memo_entries
    (Printf.sprintf
       "citation memos built for the decision closure (M7-T27 a3), %d ints = %.1f MB in \
        all"
       !Baguette_core.Analysis.memo_ints
       (float_of_int !Baguette_core.Analysis.memo_ints *. 8. /. 1048576.));
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
  (* Learned constraints that propagate (M2-L12): step 1 applies learned unit clauses
     as level-0 bounds, step 2 registers multi-literal learned clauses as engine
     instances. [glob-prune] is the one to read: a learned unit that never moves a bound
     is a bound the search had already re-derived for itself, so a build with units
     applied and this counter at 0 would have changed nothing. [cls-inst] is step 2's
     population, and [cls-decl] counts the clauses neither step could take (a [Lit.Eq],
     or a name the encoding does not declare). It is printed because "step 1 captured
     the unit population" is a claim it can refute. *)
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
  (* The learned PB ROW as a propagator (M2-L13). D-0054 separated the two objects a
     learned row is: a proof line, and a runtime propagator over the order literals it
     already names, built by Pb.of_terms. It is NOT built by Learned.to_linear_row, the
     proof-side gate M2-L13 removed, so do not read `pb-convert` as a success measure
     for it: that counter IS the gate. `pb-prune` and `pb-confl` are the honest pair,
     counted off the trail (since M2-T7 every trail entry carries the instance that
     pushed it), and they are what M2-L12's measured zero (`cls-prune`) has to be
     compared against. *)
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
  (* PB conflict analysis (M2-L6: eliminate the pivot by linear combination and
     reduction, with the clause path as fallback). [pb-fallback] is the one to read
     first. The clause path is PERMANENT (D-0044: the learned object is a PB inequality
     and a clause is its degenerate case, so the clause path always remains), and a
     build in which PB analysis never succeeded would be green in every other counter
     here. A rate of 1.00 means the PB path did nothing on this model. *)
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
  (* Every reason among the RECORDED fallbacks (the first [Search.pb_reason_cap]),
     counted, most frequent first (M8-bits-encoding-T3, D-0134 section 11). A row with
     a bits term offers no PB row (D-0132 section 2.7, the bits encoding for Linear), so
     over bits the clause path's share moves to "no PB row for instance int_lin_le" and
     its kin. This is the line that says by how much, which `pb-why` (the first reason
     only) cannot. *)
  (match Search.stats_pb_fallbacks st with
  | [] -> ()
  | reasons ->
      let counts = Hashtbl.create 8 in
      List.iter
        (fun r ->
          Hashtbl.replace counts r
            (1 + Option.value (Hashtbl.find_opt counts r) ~default:0))
        reasons;
      let sorted =
        List.sort
          (fun (r1, n1) (r2, n2) -> if n1 <> n2 then compare n2 n1 else compare r1 r2)
          (Hashtbl.fold (fun r n acc -> (r, n) :: acc) counts [])
      in
      Printf.eprintf "stats: %-10s %10d recd   %s\n" "pb-whys" (List.length reasons)
        (String.concat "; "
           (List.map (fun (r, n) -> Printf.sprintf "%d x %s" n r) sorted)));
  Printf.eprintf "stats: %-10s %10d pivots %s\n" "pb-steps" st.Search.n_pb_steps
    "pivots eliminated by linear combination + reduction, over all analyses";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-convert" st.Search.n_pb_converts
    "...learned PB rows Learned.to_linear_row accepts -- INCLUDING the empty \
     contradiction";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-stronger" st.Search.n_pb_stronger
    "...of those, where the SAME conflict's clause does NOT convert. M2-L6 test (a)";
  (* [pb-nondeg], M2-L11's test (b). M2-L11 gave PB analysis the order ladder chain as
     a row, the reason Linear actually uses, so that a learned inequality can be
     non-trivial. READ THIS BESIDE [pb-convert] AND [pb-stronger], NEVER INSTEAD OF
     EITHER. A learned row that is the EMPTY CONTRADICTION is strictly stronger than the
     clause it replaces and still useless as a propagation result; it also CONVERTS (to
     a zero-term Linear), so neither [pb-convert] nor [pb-stronger] can tell the two
     apart. That is deliberate, and it is what test_ladder.ml's degenerate control pins.
     [pb-nondeg] is the counter that can, so a claim that PB learning improved is a
     claim about this line.

     Re-measured 2026-09-18 (M2-L4), by solving every model in test/models/ with `--stats`
     and summing each line -- not read off an earlier note, which is how the figure this
     replaces went stale:

       39 models; pb-learned 38; pb-nondeg 28; pb-convert 36; pb-stronger 36.

     **10 of those 36 conversions are the empty contradiction** -- backjump_lineq_unsat
     (3), near_limit_unsat (3), offset_unsat (4), every one of them the int_lin_eq family
     whose two halves add to 0 >= k in one elimination. So 26 of the 36 are conversions
     that could actually propagate, and the same 10 inflate [pb-stronger].

     So the non-degenerate count is 28 of 38 LEARNED ROWS, and 26 of 36 is the count of
     CONVERSIONS that could propagate, a different question. (An earlier version of this
     note read "26 of 36 NON-degenerate on the same 38 models", mixing the two, on a
     miscounted suite.)

     [pb-lifted] says whether lib/core/ladder.ml fired at all. The lift is a retry after
     the bare model row fails, so 0 here means this build derives exactly what PB
     analysis derived before M2-L11. *)
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-nondeg" st.Search.n_pb_nondegenerate
    "...learned PB rows that are NOT the empty contradiction. M2-L11 test (b)";
  Printf.eprintf "stats: %-10s %10d rows   %s\n" "pb-lifted" st.Search.n_pb_lifted
    "...learned by resolving against model row PLUS a ladder chain (M2-L11); 0 = M2-L6";
  Printf.eprintf "stats: %-10s %10d rungs  %s\n" "pb-rungs" st.Search.n_pb_rungs
    "order-encoding ladder rows those analyses cited, summed (D-0028)";
  (* The backjump's own level set, against the one the learned PB row names (M2-L15,
     backjumping on the PB row). REPORTED AND NOT ACTED ON: lib/core/search.ml's
     [pb_level_verdict] has the argument, and the short form is that the nogood is a
     clause over DECISIONS, so only the decision closure answers the question the filter
     asks. [lvl-narrow] is the dangerous arm -- the PB set is a strict subset and would
     license a jump the closure does not -- and every count in it is a conflict at which
     [Search.backjump_on_pb] emits a clause veripb refuses. [lvl-assert] is the SAT
     solver's backjump level looking deeper than the closure's deepest decision, which is
     exactly the temptation Le Berre et al. (arXiv 2107.13085) warn carries no guarantee
     over PB. *)
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
  (* The identity these counters have to satisfy, stated above [Search.stats] and
     checked here on every --stats run rather than only under BAGUETTE_DEBUG: nodes =
     2 * decisions + 1 - skipped on an exhausted tree, <= on a stopped one. Binary
     branching with every push landing means an exhausted tree visits both sides of
     every decision, and each backjump skips one sibling (the `- skipped` term,
     M2-L3). If this line ever prints, one of the counters is counting the wrong event
     and no number above may be quoted. See [Search.stats_consistent]. *)
  if not (Search.stats_consistent st ~exhausted) then
    Printf.eprintf
      "stats: INCONSISTENT -- nodes=%d is not %s 2 * decisions + 1 - skipped = %d. The \
       counters are wrong; do not quote them (M1-T36, M2-L3).\n"
      st.Search.nodes
      (if exhausted then "=" else "<=")
      (Search.stats_expected_nodes st)

(* The engine's propagation counters, on stderr under --stats (M2-T6, which also added
   the self-wake veto counted as `vetoed`). The first three are the ones GCS prints
   under `-s` (propagations, effectfulPropagations, contradictingPropagations), defined
   in [Engine.counters] so that the two solvers' figures can be divided by the same
   thing. Counted by the engine, not read from the proof, as the search-tree counters
   are. *)
module Engine = Baguette_core.Engine

let report_engine_counters ?families (c : Engine.counters) ~nodes =
  let per n = if nodes > 0 then float_of_int n /. float_of_int nodes else 0.0 in
  (* Which FAMILY the runs belong to, per node, most runs first (M6-T20, which found
     learned clauses running on every bound change of every variable they name). *)
  (match families with
  | None -> ()
  | Some rows ->
      prerr_endline
        "stats: propagator runs by family (M6-T20): instances, runs/node, effectful/node";
      List.iteri
        (fun i (name, n, r, e) ->
          if i < 14 then
            Printf.eprintf "stats: %-28s %6d inst %10.1f runs/node %8.2f eff/node\n" name
              n (per r) (per e))
        rows);
  Printf.eprintf
    "stats: %-10s %10d runs   propagator runs taken off the queue (%.1f/node)\n" "props"
    c.Engine.c_runs (per c.Engine.c_runs);
  Printf.eprintf
    "stats: %-10s %10d runs   ...that returned Fixpoint having changed a domain \
     (%.1f/node)\n"
    "eff" c.Engine.c_effectful (per c.Engine.c_effectful);
  Printf.eprintf "stats: %-10s %10d runs   ...that returned Conflict\n" "contra"
    c.Engine.c_contra;
  (* How many snapshots the multi-deduction propagators took, against how many domain
     changes they made. I-P6 (M6-T19): a pass photographs the store once and makes
     every deduction from that one snapshot. Before M6-T19 a pass restarted after every
     pruning, so passes = deductions + calls. *)
  let pc = Baguette_core.Propagator.pass_counters in
  Printf.eprintf
    "stats: %-10s %10d snaps  passes of alldiff/cumulative/gcc/element, one snapshot \
     each (M6-T19, I-P6)\n"
    "passes" pc.Baguette_core.Propagator.passes;
  Printf.eprintf "stats: %-10s %10d chgs   ...domain changes those passes made\n"
    "deductions" pc.Baguette_core.Propagator.deductions;
  Printf.eprintf "stats: %-10s %10d wakes  watcher wakes delivered to the queue\n" "wakes"
    c.Engine.c_wakes;
  Printf.eprintf "stats: %-10s %10d wakes  ...dropped by the M2-T5 trigger mask\n"
    "masked" c.Engine.c_masked;
  Printf.eprintf "stats: %-10s %10d wakes  ...dropped by the M2-T6 self-wake veto\n"
    "vetoed" c.Engine.c_vetoed;
  Printf.eprintf
    "stats: %-10s %10d wakes  ...declined by the instance's own advisor (M6-T20, I-P7)\n"
    "advised" c.Engine.c_advised;
  Printf.eprintf
    "stats: %-10s %10d runs   ...of the props, SEEDED: dirty seed slots run at a node's \
     entry (M6-T18; every instance, every propagate, before it)\n"
    "seeded" c.Engine.c_seeded;
  Printf.eprintf
    "stats: %-10s %10d slots  seed slots SKIPPED as clean (M6-T18): seeded + skipped is \
     the old seeded\n"
    "skipped" c.Engine.c_skipped

(* The wall clock --time-limit is checked against (M6-T10), counted from this module's
   initialisation, which is process start to within the runtime's own start-up. [Sys.time]
   stays the clock of every measurement (see the clock comment above). *)
let wall_start = Unix.gettimeofday ()
let wall () = Unix.gettimeofday () -. wall_start

(* The wall clock at which the stop first said yes (M6-T21, the overshoot study), so
   the `limit:` line can split an overshoot into the stop's latency ([fired] minus the
   limit) and the finaliser's ([wall] minus [fired]). NaN until then, and on a
   node-limit stop. *)
let stop_fired_at = ref Float.nan

(* The `limit:` line of a stopped run (M6-T9: a --time-limit that stops cleanly and
   reports stats and incumbent). One line, always (not gated on --stats), so that a
   results file built from stderr alone can say what a stopped run was doing.
   Space-separated `key=value` fields follow the `limit:` tag, and
   scripts/corpus_run.sh copies them into its detail column, so a field renamed here is
   a column renamed there. `cpu=` is Sys.time at the moment of the report; `wall=` is
   the clock the limit was checked against. *)

let report_limit opts (st : Search.stats) ~(engine : Engine.t) ~best ~signal =
  let c = Engine.counters engine in
  Printf.eprintf
    "limit: reached time-limit=%s cpu=%.2fs wall=%.2fs nodes=%d decisions=%d \
     conflicts=%d learned=%d pb-learned=%d db=%d maxdepth=%d incumbent=%s props=%d \
     eff=%d contra=%d at=%s fired=%s signal=%s\n\
     %!"
    (match opts.time_limit with None -> "none" | Some s -> Printf.sprintf "%gs" s)
    (Sys.time ()) (wall ()) st.Search.nodes st.Search.decisions st.Search.conflicts
    st.Search.n_learned st.Search.n_pb_learned
    (* HELD at the stop, not now: the stop's own I-X2 sweep has emptied the database
       by the time this prints, so [Retention.size] would read 0 on every run. *)
    (let db = Search.stats_db st in
     Retention.n_added db - Retention.n_evicted db)
    st.Search.max_depth
    (match best with None -> "none" | Some (_, v) -> string_of_int v)
    c.Engine.c_runs c.Engine.c_effectful c.Engine.c_contra
    (* Where the stop landed: a node entry, a poll inside propagation (M6-T21), or a
       poll inside a conflict's trace (M6-T23, D-0149: the stop was never asked there,
       and a run overshot its limit by more than 300 s). *)
    (if st.Search.stopped_in_propagation then "propagation"
     else if st.Search.stopped_in_trace then "trace"
     else "node")
    (if Float.is_nan !stop_fired_at then "none" else Printf.sprintf "%.2fs" !stop_fired_at)
    (Option.value ~default:"none" signal)

(* MiniZinc's statistics format, on STDOUT under `-s` only (the standard flags, M7-T32):
   one `%%%mzn-stat: name=value` line each and `%%%mzn-stat-end`, printed once, after the
   run's last marker. The names are the FlatZinc specification's standard ones, each read
   from a counter `--stats` already prints on stderr, so nothing here is counted twice:
   failures are the search's conflicts, nogoods its learned clause and PB rows,
   propagations the propagator runs off the queue. No nSolutions: MiniZinc's solns2out
   counts the solutions itself and prints that line after this block. initTime is the wall
   clock from process start to the search's entry (parse, compile, the .opb, the proof's
   header); solveTime is the wall clock of the search after it. *)
let report_mzn_stats (st : Search.stats) ~(engine : Engine.t) ~init_time ~solve_time
    ~objective =
  let c = Engine.counters engine in
  let line k v = Printf.printf "%%%%%%mzn-stat: %s=%s\n" k v in
  let int k v = line k (string_of_int v) in
  int "nodes" st.Search.nodes;
  int "failures" st.Search.conflicts;
  int "restarts" (Search.stats_restarts st);
  int "peakDepth" st.Search.max_depth;
  int "nogoods" (st.Search.n_learned + st.Search.n_pb_learned);
  int "propagations" c.Engine.c_runs;
  (match objective with None -> () | Some v -> int "objective" v);
  line "initTime" (Printf.sprintf "%.6f" init_time);
  line "solveTime" (Printf.sprintf "%.6f" solve_time);
  print_string "%%%mzn-stat-end\n";
  flush stdout

(* -------------------------------------------------------------------- the run *)

(* The pipeline of the header, for one model: compile, write the .opb, open the proof,
   search, print the answer, then the reports. Every exception it raises is mapped to
   an exit status by the main program. *)
let solve opts (m : Model.t) =
  (* The .opb's rows go to disk as they are minted, never to the heap: the heap was one
     of the three places M7-T27 found the memory wall (D-0123, family C). With a proof
     prefix the body is written to PREFIX.opb.rows and [write_opb] splices it under the
     header, then removes it; under --no-proof there is no .opb to write and the rows
     are dropped at the door. Set BEFORE [Compile.compile], which is where
     [Encoding.create] runs. The at_exit is for the runs that end in exit 5 or an
     uncaught exception with the body half-written: the .opb is INCOMPLETE then anyway
     (the warning of [exit_out_of_resource]), and the body should not outlive it. The
     same holds for the --e2e prefix file. *)
  (match opts.proof_prefix with
  | Some prefix ->
      let rows = prefix ^ ".opb.rows" in
      Encoding.row_sink := Encoding.Stream_rows_to rows;
      at_exit (fun () ->
          if Sys.file_exists rows then try Sys.remove rows with Sys_error _ -> ());
      if opts.e2e then (
        let pre = prefix ^ ".e2e-prefix" in
        Encoding.e2e_request := Some pre;
        at_exit (fun () ->
            if Sys.file_exists pre then try Sys.remove pre with Sys_error _ -> ()))
  | None -> Encoding.row_sink := Encoding.Discard_rows);
  let compiled = Timing.phase "compile" (fun () -> Compile.compile m) in
  let store = compiled.Compile.store in
  let encoding = compiled.Compile.encoding in
  if opts.stats then report_encoding_cost (Encoding.cost encoding);
  (* The MiniZinc case of [default_proof_prefix] names a file the user never typed, so
     say where it is. Printed after the model is read, so a refused model names no file
     it did not write. *)
  (match opts.proof_prefix with
  | Some p when opts.proof_note ->
      let p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p in
      Printf.eprintf
        "baguette: the proof is written to %s.opb and %s.pbp (the model is MiniZinc's \
         temporary file; --proof PREFIX names the proof, --no-proof skips it)\n\
         %!"
        p p
  | _ -> ());
  (* I-X5: the .opb is complete and on disk before any proof rule can cite it. Its
     comment names the model's BASENAME, not the path (M1-T37, see the header). *)
  Timing.phase "opb" (fun () ->
      match opts.proof_prefix with
      | Some prefix ->
          let oc = open_out (prefix ^ ".opb") in
          Encoding.write_opb
            ~comments:[ "baguette: " ^ Filename.basename opts.model ]
            encoding oc;
          close_out oc
      | None -> ());
  let proof_oc, ctx =
    Timing.phase "proofopen" (fun () ->
        let proof_oc = open_proof_channel opts in
        let writer =
          Writer.create ~comments:opts.proof_comments ~audit:(audit_enabled ())
            ~null:opts.no_proof proof_oc
        in
        (* Explanations are hash-consed so that a rebuilt derivation shares one proof
           line (D-0172). With no line ever written there is nothing to share, so under
           --no-proof a build is not hash-consed, nor given an identity, at all. *)
        if opts.no_proof then Baguette_core.Explanation.set_hashcons false;
        Encoding.start_proof encoding writer;
        (* The context needs no model row: every propagator instance carries its own
           row id (D-0011: one propagator instance, one model row; D-0015 made the row
           part of the Explanation). M1-T31 removed the ambient row and the
           [Explanation.Trivial] constructor that needed it, which this call used to
           guard with a raising [model_id] thunk. *)
        let ctx = Justify.create ~writer ~encoding in
        (proof_oc, ctx))
  in
  let check assignment =
    Model.check_assignment m (assignment_values m store assignment)
  in
  (* The search-tree counters, always allocated and always threaded: they cost three
     increments per node whether or not anyone asks to see them, and a counter that is
     only wired up under a flag is a counter no test exercises. --stats decides whether it
     is PRINTED, not whether it is kept. *)
  let stats = Search.stats_create () in
  let writer = ctx.Justify.writer in
  (* An incumbent the proof records, which is one a stopped run can return (D-0225). *)
  let have_incumbent () = Writer.has_incumbent writer in
  (* Where `-s`'s initTime ends and its solveTime starts. *)
  let t_search = ref 0. in
  (* A run stopped from outside (M6-T9, M6-T24, D-0225). SIGTERM (an outer `timeout`),
     SIGINT and SIGXCPU do not exit. The first one sets [stop_signal], which
     [config.stop] reads with the clock, so the search ends at its next poll exactly as
     under --time-limit: proof ended, `limit:` line, exit 0. If it has not stopped
     [signal_grace] seconds later, or a second signal comes (MiniZinc sends SIGINT then
     SIGTERM), the proof is ended where it stands, as soon as no line is half written
     ([Writer.when_idle]): a valid prefix plus the three final lines. The `killed` line
     is then the report, with the counters the clean stop would have printed.

     RoundingSat does the same (a flag read by its search, and the bounds it has in the
     conclusion). Nothing can be done about SIGKILL. *)
  let stop_signal = ref None in
  let signal_name s =
    if s = Sys.sigterm then "TERM"
    else if s = Sys.sigint then "INT"
    else if s = Sys.sigxcpu then "XCPU"
    else string_of_int s
  in
  let killed_line name =
    Printf.eprintf
      "limit: killed signal=%s phase=%s cpu=%.2fs wall=%.2fs nodes=%d decisions=%d \
       conflicts=%d learned=%d pb-learned=%d maxdepth=%d props=%d eff=%d contra=%d\n\
       %!"
      name !Timing.current (Sys.time ()) (wall ()) stats.Search.nodes
      stats.Search.decisions stats.Search.conflicts stats.Search.n_learned
      stats.Search.n_pb_learned stats.Search.max_depth
      (Engine.counters compiled.Compile.engine).Engine.c_runs
      (Engine.counters compiled.Compile.engine).Engine.c_effectful
      (Engine.counters compiled.Compile.engine).Engine.c_contra
  in
  (* Ends the proof and the process. [Writer.when_idle] makes sure no line and no
     improving solution is half out. Nothing to do for a proof that has ended: the run is
     about to report its answer by itself. *)
  let stop_now report code =
    Writer.when_idle writer (fun () ->
        if not (Writer.is_finished writer) then (
          let code = code () in
          Writer.conclude_interrupted writer;
          report ();
          if code = exit_ok && not (have_incumbent ()) then
            print_string "=====UNKNOWN=====\n";
          exit code))
  in
  let signal_grace = 5. in
  let on_signal s =
    let first = Option.is_none !stop_signal in
    stop_signal := Some (signal_name s);
    if first then
      ignore
        (Unix.setitimer Unix.ITIMER_REAL
           { Unix.it_interval = 0.; it_value = signal_grace })
    else stop_now (fun () -> killed_line (signal_name s)) (fun () -> exit_ok)
  in
  List.iter
    (fun s -> Sys.set_signal s (Sys.Signal_handle on_signal))
    [ Sys.sigterm; Sys.sigint; Sys.sigxcpu ];
  Sys.set_signal Sys.sigalrm
    (Sys.Signal_handle
       (fun _ ->
         match !stop_signal with
         | Some name -> stop_now (fun () -> killed_line name) (fun () -> exit_ok)
         | None -> ()));
  (* The heap budget also ends the proof before it exits (M6-T24). A run that has an
     incumbent has an answer to return, so it ends as a stopped run (exit 0); one that has
     none is still exit 5. *)
  let resource_code () = if have_incumbent () then exit_ok else exit_resource in
  (Encoding.resource_exit :=
     fun () -> stop_now (fun () -> killed_line "heap-budget") resource_code);
  let outcome =
    Fun.protect
      ~finally:(fun () -> Timing.phase "pbpclose" (fun () -> close_out proof_oc))
      (fun () ->
        Timing.phase "search" (fun () ->
            (* Writer's emission accumulator (the [emit] row of --time) is process-wide
               and cumulative: it has already counted Encoding.start_proof, which ran in
               [proofopen]. So what belongs to [search] is the DIFFERENCE across this
               call and not the total. Sampled inside the phase so that the two brackets
               nest. *)
            let e0 = Writer.emitted_us () and l0 = Writer.emitted_lines () in
            t_search := wall ();
            let config =
              {
                Search.default_config with
                retention = retention_policy ();
                propagate_learned = propagate_learned ();
                rest_satisfied = rest_satisfied ();
                pb = pb_analysis ();
                restarts = opts.restarts;
                phase_saving = opts.phase_saving;
                search = opts.search;
                reuse_trail = opts.reuse_trail;
                cdcl = opts.cdcl;
                chrono = opts.chrono;
                stop =
                  (let by_time =
                     match opts.time_limit with
                     | None -> fun () -> false
                     | Some s ->
                         fun () ->
                           let w = wall () in
                           w >= s
                           &&
                           (if Float.is_nan !stop_fired_at then stop_fired_at := w;
                            true)
                   in
                   let by_signal () =
                     Option.is_some !stop_signal
                     &&
                     (if Float.is_nan !stop_fired_at then stop_fired_at := wall ();
                      true)
                   in
                   match node_limit () with
                   | None -> fun () -> by_signal () || by_time ()
                   | Some n ->
                       fun () -> stats.Search.nodes > n || by_signal () || by_time ());
              }
            in
            let r =
              try
                match compiled.Compile.objective with
                | None ->
                    `Satisfy
                      (Search.solve ~engine:compiled.Compile.engine ~store ~ctx ~check
                         ~stats ~config ?order:compiled.Compile.order ())
                | Some objective ->
                    (* Each improving solution is printed AS IT IS FOUND (branch and
                       bound, M5-T1), which is the FlatZinc convention SPEC 2.2 describes:
                       a running report, so that a user who interrupts a long optimisation
                       has still been told the best answer so far. The consequence for
                       --time is that the solution printing of an optimisation run is
                       inside the `search` phase and not inside `output`, where a
                       satisfaction run's is; the `output` phase then holds only the final
                       marker. That is the honest placement, since the printing really
                       does happen there. *)
                    `Optimise
                      (Search.optimise ~engine:compiled.Compile.engine ~store ~ctx ~check
                         ~stats ~config ~objective ?order:compiled.Compile.order
                         ~on_solution:(fun assignment ->
                           print_string
                             (Output.solution m (assignment_values m store assignment));
                           flush stdout)
                         ())
              with
              | Search.Stopped { best } -> `Stopped best
              | (Out_of_memory | Encoding.Heap_too_large _ | Encoding.Encoding_too_large _)
                as e ->
                  (* The synchronous resource arms, caught where the proof can still be
                     ended (M6-T24). [Writer.idle] is false when the exception came out of
                     a write, and the proof is then left as it is, incomplete. *)
                  if Writer.idle writer then (
                    let code = resource_code () in
                    Writer.conclude_interrupted writer;
                    proof_ended := Some code);
                  raise e
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
    | `Stopped _ -> false
  in
  (match outcome with
  | `Stopped best ->
      report_limit opts stats ~engine:compiled.Compile.engine ~best ~signal:!stop_signal
  | _ -> ());
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
      | `Optimise Search.Opt_unsat -> print_string Output.unsatisfiable
      (* The FlatZinc standard's marker for "stopped with nothing to report" (M6-T9),
         normative in SPEC 2.2 under "A stopped run". A stopped run that DID print
         solutions (an optimisation run's improving ones) prints nothing more: their
         `----------` lines are already out, and the absence of `==========` is exactly
         the statement that the last one is not proved optimal. *)
      | `Stopped None -> print_string "=====UNKNOWN=====\n"
      | `Stopped (Some _) -> ());
      flush stdout);
  if opts.mzn_stats then
    report_mzn_stats stats ~engine:compiled.Compile.engine ~init_time:!t_search
      ~solve_time:(wall () -. !t_search)
      ~objective:
        (match outcome with
        | `Optimise (Search.Opt (_, v)) | `Stopped (Some (_, v)) -> Some v
        | _ -> None);
  if opts.stats then (
    report_stats stats ~exhausted;
    report_strategy opts stats;
    report_engine_counters
      ~families:(Engine.family_table compiled.Compile.engine)
      (Engine.counters compiled.Compile.engine)
      ~nodes:stats.Search.nodes;
    if opts.no_proof then report_no_proof ()
    else (
      report_proof_shapes (Writer.shape_stats (Justify.writer ctx));
      report_atoms (Encoding.atom_stats encoding)))

(* ------------------------------------------- MiniZinc standard flags (M7-T32) *)

(* What the standard flags became, on stderr (D-0150): the notes on -p and -r under
   --stats, -s or -v, and under -v also the resolved search and limit. A run that asked
   for none of them keeps its stderr empty (M1-T49: diagnostics are off unless asked
   for). D-0150's warning for -f is gone since D-0148 fixed the refused nogoods of
   M7-T31 (D-0154). *)
let report_std_flags opts =
  if opts.stats || opts.verbose then (
    (match opts.threads with
    | Some n when n > 1 ->
        Printf.eprintf "baguette: -p %d accepted; baguette runs on one thread.\n" n
    | _ -> ());
    match opts.seed with
    | Some r ->
        Printf.eprintf
          "baguette: -r %d accepted and unused: the search draws no random number.\n" r
    | None -> ());
  if opts.verbose then
    Printf.eprintf
      "baguette: -v: search=%s restarts=%s phase-saving=%b time-limit=%s threads=1 \
       improving-solutions=every-one%s\n\
       %!"
      (search_name opts.search)
      (Restart.to_string opts.restarts)
      opts.phase_saving
      (match opts.time_limit with None -> "none" | Some s -> Printf.sprintf "%gs" s)
      (if opts.intermediate || opts.all_solutions then " (asked, and printed anyway)"
       else " (printed anyway)")

(* Enumeration is refused on a SATISFACTION model with exit 3 (D-0150), after the model
   is read, because whether it is one is a property of the model, not of the command
   line. It needs two things that
   do not exist: a search that goes on past a solution ([Search.solve] returns the
   first), and a proof shape for "no other solution" -- VeriPB 3.0's `solx` excludes a
   solution only under a preserved set, which this project has no encoding for (see
   [Writer.solution_excluding]). Printing one solution and letting `----------` stand
   for "the only one" would be a claim nothing proves. On an optimisation model `-a` is
   `-i`, and `-n` is not used (the FlatZinc specification: satisfaction problems only). *)
let refuse_enumeration opts (m : Model.t) =
  match m.Model.objective with
  | Model.Minimize _ | Model.Maximize _ -> ()
  | Model.Satisfy -> (
      let refuse what =
        Printf.eprintf
          "baguette: %s on a satisfaction model is not implemented: the search stops at \
           the first solution, and the proof has no shape yet for \"no other solution\" \
           (VeriPB's solx needs a preserved set; M7-T32, D-0150). Re-run without it.\n"
          what;
        exit exit_unsupported
      in
      if opts.all_solutions then refuse "every solution (-a, --all)";
      match opts.n_solutions with
      | Some n when n > 1 -> refuse (Printf.sprintf "-n %d" n)
      | _ -> ())

(* --------------------------------------------------------------------- main *)

(* The minor heap size. It is up to 4 M words (32 MB), not OCaml 5.1's 256 k words
   (2 MB), and never more than the address-space limit allows (M6-T2, D-0198).

   WHY LARGER. The solver allocates 14 to 23 words per thousand instructions
   everywhere, mostly data that dies within a branch or a conflict: trail entries of a
   level that is undone, an analysis's terms, a proof line's literals. In a 2 MB
   nursery much of it is promoted before it dies and the major collector pays for it
   again. At 4 M words promotion falls 2 to 9 times, and the instructions by a median
   7 % without the proof and 12 % with it (D-0198 sections 2 and 4 have the tables).

   THE ADDRESS SPACE. OCaml 5.1 reserves the minor heaps of all [max_domains] = 128
   possible domains in one mapping, so a 4 M-word nursery reserves 4 GiB of address
   space it never touches. Under [ulimit -v 4000000], which every suite and lane here
   runs under, the runtime then aborts at startup ("Not enough heap memory to reserve
   minor heaps"); the gate found it. So the size is cut until the reservation is at
   most an EIGHTH of the soft address-space limit read from /proc/self/limits: about
   490 k words under a 4 GB cap, the full 4 M under the 32 GB cap of the corpus scripts
   or with no limit, and never below the runtime's default. No /proc (not Linux) reads
   as no limit. A quarter was tried first and lost the lane's lot-sizing [activity]
   run, whose major heap alone is 3.2 GB of its 4 GB cap, to an Out_of_memory (D-0198
   section 2).

   It changes WHEN memory is reclaimed, never a value: nothing in [lib/] reads an
   address, so stdout, proofs and --stats are the same bytes. It costs up to 32 MB
   resident per process. An explicit [s=] in OCAMLRUNPARAM or CAMLRUNPARAM wins, so
   [OCAMLRUNPARAM=s=256k] gives back the old behaviour without a rebuild. The test
   binaries do not link this file and keep the default. *)
let minor_heap_words_max = 4 * 1024 * 1024
let max_domains = 128

let runparam_sets_minor_heap () =
  let sets v =
    List.exists
      (fun kv -> String.length kv >= 2 && kv.[0] = 's' && kv.[1] = '=')
      (String.split_on_char ',' v)
  in
  match Sys.getenv_opt "OCAMLRUNPARAM" with
  | Some v -> sets v
  | None -> ( match Sys.getenv_opt "CAMLRUNPARAM" with Some v -> sets v | None -> false)

(* The soft "Max address space" of /proc/self/limits in bytes, or [None] for "unlimited" or
   when the file cannot be read. *)
let address_space_limit () =
  match open_in "/proc/self/limits" with
  | exception Sys_error _ -> None
  | ic ->
      let rec scan () =
        match input_line ic with
        | exception End_of_file -> None
        | l when String.starts_with ~prefix:"Max address space" l -> (
            match List.filter (( <> ) "") (String.split_on_char ' ' l) with
            | _ :: _ :: _ :: soft :: _ -> int_of_string_opt soft
            | _ -> None)
        | _ -> scan ()
      in
      Fun.protect ~finally:(fun () -> close_in_noerr ic) scan

let minor_heap_words () =
  let default = (Gc.get ()).Gc.minor_heap_size in
  match address_space_limit () with
  | None -> minor_heap_words_max
  | Some bytes ->
      let fits = bytes / 8 / (max_domains * (Sys.word_size / 8)) in
      Stdlib.max default (Stdlib.min minor_heap_words_max fits)

let () =
  if not (runparam_sets_minor_heap ()) then
    Gc.set { (Gc.get ()) with Gc.minor_heap_size = minor_heap_words () }

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
  (* The writer's per-line clock (the [emit] row, M1-T47) is a syscall a line and stays
     off unless the numbers are being asked for; --time is the only thing in the tree
     that opens it. *)
  Writer.time_emission := opts.time;
  if opts.time then at_exit Timing.report;
  (* The heap budget's Gc alarm (M7-T8), armed as early as possible and after the
     options are read. The alarm is the backstop for everything the clause budget
     cannot predict, so it wants to be armed before the first allocation that is not
     argument parsing. It installs nothing at all unless --max-heap-mb (or
     BAGUETTE_MAX_HEAP_MB) was given. *)
  Encoding.install_heap_guard ();
  (* The heap budget is also polled on a CPU-time ticker, ten times a second
     ([Encoding.heap_poll_seconds]), because the alarm reads the heap only at the end of
     a major cycle and a cycle on a heap of several GB can outlast the climb to the
     address-space limit (D-0200). The poll covers every phase, every granularity
     of propagator (D-0200 §2 has the run whose root propagation did 127 runs in 42 s).
     The handler ends the run where it stands, as the alarm does. ITIMER_VIRTUAL counts
     this process's user time only, so it does not tick while a write blocks. Installed
     only under --max-heap-mb, so a run without it has no timer and no handler. *)
  (match Encoding.current_heap_limit_mb () with
  | None -> ()
  | Some _ ->
      Sys.set_signal Sys.sigvtalrm (Sys.Signal_handle (fun _ -> Encoding.poll_heap ()));
      ignore
        (Unix.setitimer Unix.ITIMER_VIRTUAL
           {
             Unix.it_interval = Encoding.heap_poll_seconds;
             it_value = Encoding.heap_poll_seconds;
           }));
  if not (Sys.file_exists opts.model) then (
    Printf.eprintf "no such file: %s\n" opts.model;
    exit exit_usage);
  report_std_flags opts;
  Timing.record "args" (Timing.now () - t_main);
  (* The reader, by the file's extension (M23-inputs-T2, D-0230): `.scp` is the input
     format of CakeML's cake_pb_cp, read by lib/scp/ into the same Model.t; anything else
     is FlatZinc. The end-to-end chain (--e2e, M14) is FlatZinc's alone: D-0228 (a
     relational problem between the readers and the solver, with .scp as a second input)
     leaves it out for a .scp in its section 14, so the flag is refused, exit 2, rather
     than run against a translation of a file that was never FlatZinc. *)
  let is_scp = Filename.check_suffix opts.model ".scp" in
  if is_scp && opts.e2e then (
    prerr_endline
      "baguette: --e2e is not available on a .scp input (D-0228 section 14, D-0230)";
    exit exit_usage);
  let read_model path =
    if is_scp then Baguette_scp.Reader.of_file path else Builder.of_file path
  in
  match
    Timing.phase "parse" (fun () -> Fz_error.catch (fun () -> read_model opts.model))
  with
  | exception Out_of_memory ->
      prerr_string (Encoding.out_of_memory_message ());
      flush stderr;
      exit exit_resource
  | Error e ->
      prerr_endline (Fz_error.to_string e);
      exit exit_usage
  | Ok m -> (
      refuse_enumeration opts m;
      match Fz_error.catch (fun () -> solve opts m) with
      | Ok () -> exit exit_ok
      | exception (Sys_error msg | Fun.Finally_raised (Sys_error msg)) ->
          exit_write_failed opts msg
      | Error e ->
          (* Exit 3. Compile raises through the front end's error type for everything
             SPEC 2.1 requires a diagnostic for: an unimplemented builtin, a domain the
             encoding cannot express, an objective, a search annotation that is not what
             the search actually does. *)
          prerr_endline (Fz_error.to_string e);
          exit exit_unsupported
      | exception Baguette_proof.E2e.Not_covered why ->
          (* Exit 3: the model has a construct the solver-written --e2e prefix does not
             cover (D-0187). Refused before the search, like an unsupported
             builtin; the external bridge (tools/e2e/bridge.py) is the path for it. *)
          Printf.eprintf
            "baguette: --e2e: %s (D-0187). Run without --e2e and bridge the proof with \
             tools/e2e/bridge.py.\n"
            why;
          exit exit_unsupported
      | exception Search.Unsound_solution assignment ->
          (* Exit 4, I-P1 (soundness: a propagator never removes a value that belongs to
             a solution). The solver found an assignment its own propagators accepted
             and the model rejects. That is a propagator soundness bug, and the only
             correct thing to do with it is stop. *)
          Printf.eprintf
            "baguette: INTERNAL -- a propagator is unsound (I-P1). The search returned \
             an assignment that does not satisfy the model:\n";
          List.iter
            (fun (v, value) ->
              Printf.eprintf "  %s = %d\n" (Model.var m (Var.to_int v)).Model.v_name value)
            assignment;
          exit exit_internal
      | exception Writer.Audit_failed msg ->
          (* Exit 4, I-X2: some constraint id was minted and never retired. The answer
             may well be right, but the proof is not one we are entitled to stand
             behind. *)
          Printf.eprintf "baguette: INTERNAL -- proof audit failed (I-X2): %s\n" msg;
          exit exit_internal
      | exception Encoding.Encoding_too_large o ->
          (* Exit 5, the predictive guard, --max-encoding-clauses (M7-T8, D-0071). Not
             exit 3: this model is legal and a larger budget answers it. Not exit 4:
             nothing is broken. The whole point
             of the row is that a harness can tell this apart from both, and from the
             exit 134 it replaces. [Encoding] refuses before it allocates, so there is
             no partial encoding and no partial proof to warn about. *)
          prerr_string (Encoding.overrun_message o);
          exit_out_of_resource opts
      | exception Out_of_memory ->
          (* Exit 5. One allocation the runtime could not map: the one failure of this
             kind that can be caught (D-0200). "Fatal error: allocation failure during
             minor GC" cannot be, which is why the budget's poll exists. *)
          prerr_string (Encoding.out_of_memory_message ());
          exit_out_of_resource opts
      | exception Encoding.Heap_too_large o ->
          (* Exit 5, the reactive guard, caught synchronously at a declaration. Its
             sibling, the Gc alarm, cannot come through here: it fires at an arbitrary
             point and exits with this same status itself. Same wording either way. *)
          prerr_string (Encoding.heap_message o);
          exit_out_of_resource opts
      | exception Encoding.Width_too_large (x, lo, hi) ->
          (* Exit 4, the width limit (D-0041: a declared width limit, because a proof
             nobody can store is not an answer; M1-T54 gave it this arm). The sibling of
             the [Unrepresentable] arm below, and exit 4 for the same reason:
             lib/flatzinc/compile.ml refuses an over-wide declared domain first, with a
             positioned diagnostic and exit 3 (which is the right code, because an
             over-wide domain is a MODEL problem, not an invariant failure). So reaching
             the encoding's own raise through this binary means Compile's pass did not
             cover the path.

             Measured before adding this, with Compile's pass disabled: the binary died
             on "Fatal error: exception Baguette_proof.Encoding.Width_too_large(...)",
             exit 2 -- the same code as a bad command line.

             Two-reader wording, as I-X8 requires (no row whose arithmetic wrapped is
             committed to the .opb, whoever the caller): reached
             through a different caller of Encoding, this exception is the documented
             contract rather than a bug.

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
          (* Exit 4, a row the .opb could not commit (M1-T58). [Encoding] is the
             *committing door* for the .opb: it raises this when a row's arithmetic does
             not fit a 63-bit int, because writing the row would put a constraint in the
             file that is not the one posted and veripb would verify the wrong model
             (D-0029: an arithmetic limit enforced at compile time; I-X8).

             Without this arm the CLI would die on an uncaught exception, "Fatal error:
             exception Baguette_proof.Encoding.Unrepresentable(...)", exit 2, with no
             context and no warning about the artefact. It is the twin of the
             [Checked.Overflow] arm below (M1-T34).

             Why it is exit 4 and not exit 3, by the same argument as Overflow's: a
             model genuinely over the arithmetic limit is rejected by
             lib/flatzinc/compile.ml's cap first, with a positioned diagnostic and
             exit 3. So reaching HERE means the cap did not cover the path, which is an
             invariant this binary states about itself failing -- not a model problem.
             Reporting it as one would send the reader to rescale a model when the bug
             is in the checking.

             What is NOT the same as Overflow, and is the reason I-X8 exists: this
             exception is raised by the module that writes the artefact, on behalf of
             *any* caller. This binary reaches Encoding only through Compile's cap, with
             either reader, so this is unreachable from here. A caller that drives
             Encoding directly, as the test suite does, has no such cap in front of it,
             and for those this exception is the contract rather than a bug. The message
             therefore says which of the two the reader is looking at instead of asserting
             it is a baguette bug outright. *)
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
          (* Under OCAMLRUNPARAM=b, say WHERE (M6-T9). The arm exists because the cap
             has a hole, and the only way to find the hole is the raise site; wave 31's
             sweep reached this on 2014_rectangle-packing with nothing to go on. *)
          if Printexc.backtrace_status () then prerr_string (Printexc.get_backtrace ());
          (* Exit 4, an integer overflow past the compile-time cap (M1-T34). D-0029
             decided that overflow RAISES rather than wrapping or quietly declining, and
             put a compile-time cap in front of the raise so that no model the CLI accepts
             can reach it. This arm is what happens if that cap is ever wrong, and without
             it the CLI would die on an uncaught exception -- "Fatal error: exception
             Baguette_core.Checked.Overflow(...)", exit 2, no context.

             Three deliberate choices:

             * It is attached to [solve] and nowhere else. Neither reader can raise
               this. builder.ml computes through Checked and turns an overflow into a
               positioned diagnostic ([lin_terms], fixed in M22-review-T1 when its
               constant fold could overflow) or drops the fact ([facts_of],
               [infer_bounds]); lexer.ml, parser.ml and model.ml compute nothing that
               can overflow. lib/scp/reader.ml turns an overflow into a positioned
               refusal ([ck]). [Compile.compile], [Search.solve] and
               the encoding can, and all three are inside [solve].

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
