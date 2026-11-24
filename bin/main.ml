(* The baguette CLI.
     baguette MODEL.fzn [--proof PREFIX | --no-proof] [--proof-comments] [--all] [--time]

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

   **A run without --proof writes its proof and KEEPS it** (M9-no-proof-T5, D-0163, the
   user's decision of 2026-11-19). docs/SPEC.md 1: "The proof is not a debugging aid. It
   is a primary output", so the default run writes PREFIX.opb and PREFIX.pbp under a name
   [default_proof_prefix] takes from the model -- `./foo.opb` and `./foo.pbp` for
   `foo.fzn`, in the current directory -- and leaves them there. `--proof PREFIX` chooses
   the name. Until T5 such a run wrote the .pbp to a temporary file and deleted it (and
   no .opb at all), so the answer it printed came with a proof nobody could check.

   **Except under `--no-proof` (M9-no-proof-T2, D-0126), which is off by default and is
   a MEASUREMENT INSTRUMENT, not a mode of the solver.** It keeps every Explanation (the
   mutators take one by type, I-P4), the learning and the independent solution check
   I-S1, and skips what makes bytes: the .opb rows ([Encoding.row_sink] at
   [Discard_rows], and the ladder loop short-circuited to its count), the .pbp (a
   [Writer.t] over [Filename.null] built by [Writer.create ~null:true], whose every rule
   mints its id and writes nothing), every justification and trace ([Justify] and
   [Trace] return at their entry under that writer, before forcing anything), the
   proof-side deletion of learned rows and the audit I-X2. [Encoding.start_proof] is
   still called, through that writer, because element and alldiff embed its
   [Writer.fresh] ids in their explanations and D-0126's id rule wants those identical
   in both modes. Since D-0161 it mints the root lemmas' ids without reading the lemmas,
   and [Search] no longer builds what only a proof line reads (an improving solution's
   literal family, a decision's bits atom, I-S4's walk over the cut). What it prints is
   UNVERIFIED and SPEC 1 says it is not a result;
   `--stats` says so on stderr. `make check` proves every model AND runs it again under
   this flag: stdout and the exit code must be byte-identical
   (scripts/run_model_tests.sh), which is the one direct test that proof logging never
   steers the search.

   **The .opb comment names the model's BASENAME, not the path it was given** (M1-T37).
   `.opb` bytes are the one column M3-T5 found trustworthy at every row, and while the
   header read `"baguette: " ^ opts.model` that column was not a property of the model at
   all: the same file measured as `test/models/x.fzn` and as `/tmp/x.fzn` produced .opb
   files ~16 bytes apart, so two people's byte counts could legitimately disagree about
   the same model. The basename is kept rather than the comment dropped because a human
   holding a .opb and a .pbp in a temp directory still needs to know which model they
   belong to, and the *directory* is the one part of the path that person already knows:
   they typed it. bench/run_bench.sh checks this property on every run -- see
   `opb_path_independence` there -- so the dependence cannot come back unnoticed.

   **The MiniZinc standard flags** (M7-T32, D-0150, SPEC 2.2). `minizinc --solver
   baguette` passes a solver only the flags its `tools/baguette.msc` declares in
   `stdFlags`, always BEFORE the model file, and each one here is a thin mapping onto a
   long option that already existed: `-t MS` is `--time-limit MS/1000`; `-s` is `--stats`
   plus a `%%%mzn-stat:` block on stdout at the end of the run (the one way stdout
   differs with a flag, and only with this one); `-f` is `--search alternate --restarts
   luby --phase-saving` for whichever of the three was not given explicitly (Chuffed's
   free search, D-0137 section 4; the refused proofs that made it unsafe were M7-T31's,
   fixed by D-0148, and the default search stays the fixed one by the user's choice, D-0154);
   `-i` and, on an optimisation model, `-a` ask for every improving solution, which this
   CLI prints anyway, each with its own `soli` line in the proof; `-r SEED` is accepted
   and unused (nothing on the CLI's path draws a random number); `-p N` is accepted and
   the run uses one thread; `-v` says on stderr what the flags became. REFUSED, exit 3,
   after the model is read: `-a` and `-n N > 1` on a SATISFACTION model, because
   enumerating solutions needs a proof shape for "no other solution" that the writer
   does not have (VeriPB 3.0's `solx` needs a preserved set, see [Writer]) and a search
   that continues past a solution, which [Search.solve] does not do. The .msc therefore
   declares `-i` and not `-a`, and MiniZinc itself then answers `-a` on a satisfaction
   model with "Solver does not support all solutions". *)

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
  restarts : Restart.policy; (* M10-search-strategy-T2, D-0137: --restarts *)
  phase_saving : bool; (* M10-search-strategy-T2, D-0137: --phase-saving *)
  search : Search.search_mode; (* M10-search-strategy-T3, D-0137: --search *)
  reuse_trail : bool; (* M10-search-strategy-T3, D-0137: --reuse-trail *)
  (* M7-T32, D-0150: the MiniZinc standard flags. See the header. *)
  intermediate : bool; (* -i: every improving solution; printed anyway *)
  n_solutions : int option; (* -n N; N > 1 on a satisfaction model is refused *)
  seed : int option; (* -r SEED: accepted, unused *)
  threads : int option; (* -p N: accepted, one thread *)
  mzn_stats : bool; (* -s: --stats and the %%%mzn-stat block on stdout *)
  verbose : bool; (* -v: the flags' mapping, on stderr *)
  e2e : bool;
      (* M14-e2e-verification-T3, D-0187: --e2e, the proof is written to be checked
         against cake_pb_cp's .opb, its prefix deriving this run's .opb from it *)
}

(* Exit codes. 0 covers both SAT and UNSAT: an UNSAT model is a successful run that
   proved something, not a failure, and scripts/run_model_tests.sh reads a non-zero exit
   as the solver having fallen over. *)
let exit_ok = 0
let exit_usage = 2
let exit_unsupported = 3
let exit_internal = 4

(* M7-T8 / D-0071. A RESOURCE overrun: the run asked for more of the machine than the
   budget it was given allows. Distinct from all four above on purpose. It is not 3,
   because the model is legal FlatZinc that a bigger budget would answer; it is not 4,
   because no invariant failed; and it is emphatically not the exit 134 of the OCaml
   runtime's own `Fatal error: allocation failure`, which is what D-0068's corpus run
   saw nine times and could not tell apart from a crash. The number lives in
   [Encoding] because the Gc alarm exits with it directly, and this binding is here so
   that a reader of this table sees all five. *)
let exit_resource = Encoding.exit_resource

let usage () =
  prerr_endline
    "usage: baguette MODEL.fzn [--proof PREFIX | --no-proof] [--proof-comments] [--all] \
     [--time] [--stats] [--max-order-width N] [--max-direct-values N] [--width-warn N] \
     [--max-encoding-clauses N] [--max-heap-mb N] [--bits-above W] [--time-limit S] \
     [--restarts POLICY] [--phase-saving] [--search ORDER] [--reuse-trail] [-a] [-i] [-n \
     N] [-f] [-t MS] [-r SEED] [-p N] [-s] [-v]";
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
  prerr_endline "                    search had printed a solution: a stopped run).";
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
    "  BAGUETTE_RETENTION=off|fifo:N|lbd:N|tiered[:K=N,...]  the learned-constraint";
  prerr_endline
    "                    retention policy; tiered (D-0139) takes keys core, mid,";
  prerr_endline "                    first, inc and mid_every, e.g. tiered:first=500";
  prerr_endline
    "                    (M2-L4). Default `off`: measured, see lib/core/retention.ml.";
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

(* M9-no-proof-T5 (D-0163). WHERE A RUN WITHOUT --proof WRITES ITS PROOF, decided here and
   nowhere else. The user decided on 2026-11-19 that such a run writes its proof and KEEPS
   it. The DIRECTORY is still the user's to confirm: what follows is the proposal on
   record, and changing it is an edit to [default_proof_prefix] alone.

     baguette DIR/foo.fzn            ->  ./foo.opb and ./foo.pbp, in the CURRENT directory
     baguette /tmp/mznfileXYZ.fzn    ->  ./baguette-proof.opb and .pbp, and a stderr note

   The result is a PREFIX, as --proof's argument is: the run appends .opb and .pbp. Only a
   `.fzn` extension is dropped, so no model file is ever its own proof's name (`foo` gives
   foo.opb, and a model called `x.pbp` gives x.pbp.pbp).

   The second line is the MiniZinc case. `minizinc --solver baguette m.mzn` flattens to a
   temporary `mznfile<random>.fzn` and passes only that path after the flags (measured on
   MiniZinc 2.10.1: neither the argv, the environment nor the .fzn names the .mzn), so a
   name from the model would be a new meaningless name on every run. A fixed name in the
   current directory is the next best thing; the note on stderr gives its full path,
   because the user never typed it. `--proof PREFIX` and `--no-proof` are both extraFlags
   of tools/baguette.msc, so a MiniZinc user can name the proof or skip it.

   A file of the same name is OVERWRITTEN, as `--proof PREFIX` always has done: it is the
   output of a previous run, like a compiler's. Two runs of the same model, or two MiniZinc
   runs, in the same directory at the same time therefore write over each other; give each
   its own --proof. *)
let mzn_temp_model model =
  let b = Filename.basename model in
  String.starts_with ~prefix:"mznfile" b && Filename.check_suffix b ".fzn"

let default_proof_prefix model =
  let b = Filename.basename model in
  if mzn_temp_model model then "baguette-proof"
  else if Filename.check_suffix b ".fzn" then Filename.chop_suffix b ".fzn"
  else b

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
  let time_limit = ref None in
  let no_proof = ref false in
  let restarts = ref Restart.No_restarts in
  let phase_saving = ref false in
  let search = ref Search.Annotated in
  let reuse_trail = ref false in
  (* M7-T32 (D-0150). [restarts_given] and [search_given] let `-f` fill only what was
     not asked for explicitly, in either order on the command line. *)
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
     this parser: a flag that was not in force is the trap CLAUDE.md records twice. *)
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
      (* M10-search-strategy-T2 (D-0137). A malformed policy is a usage error, never a
         silent `none`: a measurement whose flag was not in force is the trap CLAUDE.md
         records twice. *)
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
      (* M7-T8, the same shape and for the same reason: consulted deep inside
         [Compile] and again by the Gc alarm, with no single call site to thread
         through. Default none, per D-0065. *)
      | "--max-encoding-clauses" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--max-encoding-clauses" Encoding.encoding_budget argv.(i + 1);
          go (i + 2)
      | "--max-heap-mb" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--max-heap-mb" Encoding.heap_limit_mb argv.(i + 1);
          go (i + 2)
      (* M8-bits-encoding-T2 (D-0130 section 10): the same shape, consulted by [Compile]
         at every declaration. [set_limit] gives it `none`'s spelling and the typo
         refusal of the other five. *)
      | "--bits-above" ->
          if i + 1 >= Array.length argv then usage ();
          set_limit "--bits-above" Encoding.bits_above argv.(i + 1);
          go (i + 2)
      (* M7-T32 (D-0150): the MiniZinc standard flags. See the header. *)
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
  (* M7-T32: `-f` is Chuffed's free search, the alternation of the annotation with the
     activity order under restarts (D-0137 section 4), with phase saving as Chuffed's SAT
     layer has it and Luby on D-0137's unit of 100 conflicts (section 0). An explicit
     --search or --restarts wins wherever it sits on the line. *)
  if !free_search then (
    if not !search_given then search := Search.Alternate;
    (if not !restarts_given then
       restarts :=
         match Restart.of_string "luby" with
         | Ok p -> p
         | Error msg -> failwith ("Restart.of_string \"luby\": " ^ msg));
    phase_saving := true);
  (* M9-no-proof-T2 (D-0126): the two flags contradict each other, and a silent choice
     between them is the trap CLAUDE.md records twice -- a measurement whose flag was
     never in force. A usage error, exit 2, and no file is touched. *)
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
        intermediate = !intermediate;
        n_solutions = !n_solutions;
        seed = !seed;
        threads = !threads;
        mzn_stats = !mzn_stats;
        verbose = !verbose;
        e2e = !e2e;
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

   Every number [--time] reports is [Sys.time], process CPU. (The one exception is the
   --time-limit CHECK and the `wall=` field beside `cpu=` on the `limit:` lines: M6-T10
   made the limit wall-clock -- bin/dune now links `unix` for Unix.gettimeofday and
   nothing else -- because the harnesses kill on wall time and a CPU limit under load
   loses that race and leaves no stats behind. A limit and a measurement want different
   clocks.) For the measurements, CPU is the better instrument rather than a compromise,
   and both halves of that were measured on this switch rather than assumed:

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
  (* M6-T9: the phase in flight, for the SIGTERM line in [solve]. One store per phase,
     on or off; it is read by nothing else. *)
  let current = ref "startup"

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

(* ------------------------------------------------------------------ running *)

(* The proof channel: PREFIX.pbp, which the run keeps (M9-no-proof-T5, see the header and
   [default_proof_prefix]). *)
let open_proof_channel opts =
  (* M9-no-proof-T2: the null channel. Nothing is written through it -- the writer over
     it is [Writer.create ~null:true] and every rule returns before rendering -- and it
     exists so that the writer has a channel to be over and the pipeline below keeps its
     one shape. [parse_args] has already refused `--no-proof` beside `--proof`, and gives
     every other run a prefix. *)
  match opts.proof_prefix with
  | _ when opts.no_proof -> open_out Filename.null
  | Some prefix -> open_out (prefix ^ ".pbp")
  | None -> invalid_arg "open_proof_channel: no prefix outside --no-proof"

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
         "baguette: BAGUETTE_RETENTION=%S is not a policy. Use off, fifo:N or lbd:N, \
          where N is the database cap, or \
          tiered[:core=2,mid=6,first=2000,inc=300,mid_every=10000] (D-0139)."
         v);
    exit 2
  in
  (* D-0139: `tiered`, or `tiered:` followed by comma-separated KEY=N overriding
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
  | Some "off" -> Retention.keep_all
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

(* [Search.config.pb], from the environment (M6-T9), with the same discipline as the two
   knobs either side of it. `off` is [Search.no_pb]: every conflict goes down the M2-L3
   clause path and PB conflict analysis is never asked. It exists so that D-0062's cost --
   an order of magnitude on width_sat_depth, accepted when PB analysis was wired in --
   can be measured on real instances rather than argued about. A measurement knob, not a
   user-facing choice; anything but on/off/unset FAILS. *)
let pb_analysis () =
  match Sys.getenv_opt "BAGUETTE_PB_ANALYSIS" with
  | None | Some "on" -> true
  | Some "off" -> false
  | Some v ->
      prerr_endline
        (Printf.sprintf
           "baguette: BAGUETTE_PB_ANALYSIS=%S is not a setting. Use on or off." v);
      exit 2

(* M6-T9. BAGUETTE_NODE_LIMIT=N stops the search exactly as --time-limit does, at the
   first node entry past N nodes. A MEASUREMENT knob: a CPU-time stop lands on a
   different node on every run, so two binaries cannot be compared byte for byte under
   it; a node stop lands on the same node every time, so "the proofs of the same N-node
   prefix are identical" is a checkable claim about a performance change. Anything but
   a non-negative integer FAILS, as with the other knobs. *)
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

(* [Search.config.rest_satisfied] (M11-complexity-T17, D-0173), with the same discipline:
   anything other than on, off or unset FAILS. A measurement knob for a default-behaviour
   change the user decides: on, learned clauses rest while satisfied (same pruning, another
   propagation order, so other trees and proofs). *)
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
    (Encoding.order_width_limit_string ());
  (* M7-T8. The two budgets whose exhaustion is exit 5, printed beside the total they
     bound so a reader comparing "ladder + direct" against "budget" is reading two
     numbers in the same units, on adjacent lines. *)
  Printf.eprintf
    "stats: %-10s %10s        --max-encoding-clauses (bounds ladder+direct)\n" "budget"
    (Encoding.encoding_budget_string ());
  Printf.eprintf "stats: %-10s %10s        --max-heap-mb (MB of OCaml heap)\n" "heap"
    (Encoding.heap_limit_string ());
  (* M8-bits-encoding-T2 (D-0130 section 10). How many variables went on bits, how many
     bound rows that cost, and how many eligible-by-width variables the scope rule held
     back, by family -- the line D-0130 section 12 says a comparison must read. *)
  Printf.eprintf
    "stats: %-10s %10d vars   bits-encoded (--bits-above %s); held back: %s\n" "bits"
    c.Encoding.c_bits_vars
    (Encoding.bits_above_string ())
    (match c.Encoding.c_held_back with
    | [] -> "none"
    | hs -> String.concat ", " (List.map (fun (f, n) -> Printf.sprintf "%s: %d" f n) hs));
  Printf.eprintf "stats: %-10s %10d lines  bound rows (2 per bits variable)\n" "bitsrows"
    c.Encoding.c_bits_rows;
  (* M8-bits-encoding-T3 (D-0134 section 2.5): choice groups posted -- one per maxmin
     scope with a bits variable, each n selector rows and one clause. *)
  Printf.eprintf "stats: %-10s %10d groups selector rows + clause (maxmin over bits)\n"
    "choices" c.Encoding.c_choices

(* M7-T8. A resource overrun can fire at a DECLARATION, before any file exists, or at
   [ensure_direct], which runs inside [start_proof] with the .opb already on disk and
   the .pbp part-written. The guard cannot tell a reader which from inside [Encoding],
   and half a proof that veripb happens to parse is the worst outcome available here,
   so the binary says the cautious thing whenever --proof was asked for. *)
(* M6-T24 (D-0225): [Some code] when a resource arm ended the proof before raising, with
   the status to exit with. The proof is then complete and there is nothing to warn of. *)
let proof_ended : int option ref = ref None

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

(* M8-bits-encoding-T5 (D-0131). The SHAPE of the proof that was just written, on
   stderr under --stats: how many lines are `pol` and how many `rup`, and the tokens the
   `pol` lines carry, in total and at the widest one, with that one's origin.

   Written for a reader who has not read D-0127: VeriPB 3.0.2 checks a `rup` by unit
   propagation, which is linear in what it walks, and a `pol` by cutting-planes
   arithmetic whose every `+` costs the size of the accumulator -- so a `pol` of
   Theta(w) tokens over a variable of declared width w is the one line in a proof whose
   check time grows faster than its byte count. After D-0131 the solver writes its
   ladder walks as `rup`; what is left as `pol` is a derivation the checker cannot
   reach by propagation (a counting global's, a learned PB row's), and this report is
   how a wide one is seen by name. *)
(* M8-bits-encoding-T2 (D-0130 section 10): what the bits arm minted into the proof.
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

(* M9-no-proof-T2 (D-0126). The line that says what this run is NOT, printed in place of
   the proof-shape and atom reports: those would read all zeros here, which to anyone
   grepping `stats:` looks like a proof with no `pol` in it rather than no proof. *)
let report_no_proof () =
  Printf.eprintf "stats: %-10s %10d %-6s %s\n" "no-proof" 1 "bool"
    "--no-proof: NO PROOF EXISTS for this run; the answer on stdout is UNVERIFIED";
  prerr_endline
    "stats: and is not a result (SPEC 1, D-0126). A measurement instrument: what the";
  prerr_endline
    "stats: proof costs is what the same run WITH a proof costs beyond this one. No";
  prerr_endline "stats: proof-shape or atom counters: nothing was written."

(* M10-search-strategy (D-0137): the opt-in strategies' counters, printed only when one
   of them is on, so that a default run's --stats is unchanged line for line. *)
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
  (* The identity these counters have to satisfy, stated above [Search.stats] and
     checked here on every --stats run rather than only under BAGUETTE_DEBUG. Binary
     branching with every push landing means an exhausted tree visits both sides of
     every decision. If this line ever prints, one of the counters is counting the
     wrong event and no number above may be quoted. *)
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
  (* M8-bits-encoding-T3 (D-0134 section 11): every reason among the RECORDED fallbacks
     (the first [Search.pb_reason_cap]), counted, most frequent first. A row with a bits
     term offers no PB row (D-0132 section 2.7), so over bits the clause path's share
     moves to "no PB row for instance int_lin_le" and its kin; this is the line that
     says by how much, which `pb-why` (the first reason only) cannot. *)
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

(* M2-T6. The engine's propagation counters, on stderr under --stats: the three GCS
   prints under `-s` (propagations, effectfulPropagations, contradictingPropagations),
   defined in [Engine.counters] so that the two solvers' figures can be divided by the
   same thing. Counted by the engine, not read from the proof (M1-T36). *)
module Engine = Baguette_core.Engine

let report_engine_counters ?families (c : Engine.counters) ~nodes =
  let per n = if nodes > 0 then float_of_int n /. float_of_int nodes else 0.0 in
  (* M6-T20: which FAMILY the runs belong to, per node, most runs first. *)
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
  (* M6-T19 / I-P6: how many snapshots the multi-deduction propagators took, against
     how many domain changes they made. Before M6-T19 passes = deductions + calls. *)
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

(* M6-T10. The wall clock --time-limit is checked against, counted from this module's
   initialisation, i.e. process start to within the runtime's own start-up. [Sys.time]
   stays the clock of every measurement (see the clock comment above). *)
let wall_start = Unix.gettimeofday ()
let wall () = Unix.gettimeofday () -. wall_start

(* M6-T9. One line, always (not gated on --stats), so that a results file built from
   stderr alone can say what a stopped run was doing. Space-separated `key=value`
   fields after the `limit:` tag; scripts/corpus_run.sh copies it into its detail
   column, so a field renamed here is a column renamed there. [cpu_s] is Sys.time at the
   moment of the report, the same clock the limit was checked against. *)
(* M6-T21: the wall clock at which the stop first said yes, so the `limit:` line can
   split an overshoot into the stop's latency ([fired] minus the limit) and the
   finaliser's ([wall] minus [fired]). NaN until then, and on a node-limit stop. *)
let stop_fired_at = ref Float.nan

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
    (* M6-T21: where the stop landed -- a node entry, or a poll inside propagation. *)
    (if st.Search.stopped_in_propagation then "propagation"
     else if st.Search.stopped_in_trace then "trace" (* M6-T23, D-0149 *)
     else "node")
    (if Float.is_nan !stop_fired_at then "none" else Printf.sprintf "%.2fs" !stop_fired_at)
    (Option.value ~default:"none" signal)

(* M7-T32 (D-0150). MiniZinc's statistics format, on STDOUT under `-s` only: one
   `%%%mzn-stat: name=value` line each and `%%%mzn-stat-end`, printed once, after the
   run's last marker. The names are the FlatZinc specification's standard ones, each
   read from a counter `--stats` already prints on stderr, so nothing here is counted
   twice: failures are the search's conflicts, nogoods its learned clause and PB rows,
   propagations the propagator runs off the queue. No nSolutions: MiniZinc's solns2out
   counts the solutions itself and prints that line after this block. initTime is the wall clock from
   process start to the search's entry (parse, compile, the .opb, the proof's header);
   solveTime is the wall clock of the search after it. *)
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

let solve opts (m : Model.t) =
  (* M7-T27 (b), D-0123 family C: the .opb's rows go to disk as they are minted, never
     to the heap. With --proof the body is written to PREFIX.opb.rows and [write_opb]
     splices it under the header, then removes it; under --no-proof there is no .opb to
     write and the rows are dropped at the door. Every other run has a prefix
     (M9-no-proof-T5). Set BEFORE [Compile.compile], which is
     where [Encoding.create] runs. The at_exit is for the runs that end in [exit 5] or
     an uncaught exception with the body half-written: the .opb is INCOMPLETE then
     anyway ([incomplete_proof_warning]), and the body should not outlive it. *)
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
  (* I-X5: the .opb is complete and on disk before any proof rule can cite it. The
     comment names the BASENAME, not the path -- M1-T37, see this file's header. *)
  (* M9-no-proof-T5: the MiniZinc case of [default_proof_prefix] names a file the user
     never typed, so say where it is. Printed after the model is read, so a refused model
     names no file it did not write. *)
  (match opts.proof_prefix with
  | Some p when opts.proof_note ->
      let p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p in
      Printf.eprintf
        "baguette: the proof is written to %s.opb and %s.pbp (the model is MiniZinc's \
         temporary file; --proof PREFIX names the proof, --no-proof skips it)\n\
         %!"
        p p
  | _ -> ());
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
        (* D-0172: with no line ever written there is nothing to share, so a build is not
           hash-consed (nor given an identity) at all under --no-proof. *)
        if opts.no_proof then Baguette_core.Explanation.set_hashcons false;
        Encoding.start_proof encoding writer;
        (* Every propagator instance carries its own row id (D-0011/D-0015). This used
           to install a [model_id] thunk that raised, because [Explanation.Trivial]
           could still reach the proof layer and there was no honest way to guess
           which row it meant. M1-T31 removed the field: there is no ambient row to
           install, so there is nothing to guard here. *)
        let ctx = Justify.create ~writer ~encoding in
        (proof_oc, ctx))
  in
  let check assignment =
    Model.check_assignment m (assignment_values m store assignment)
  in
  (* M1-T36. Always allocated and always threaded: the counters cost three increments
     per node whether or not anyone asks to see them, and a counter that is only wired
     up under a flag is a counter no test exercises. --stats decides whether it is
     PRINTED, not whether it is kept. *)
  let stats = Search.stats_create () in
  let writer = ctx.Justify.writer in
  (* M6-T24 (D-0225). An incumbent the proof records, i.e. one a stopped run can return. *)
  let have_incumbent () = Writer.has_incumbent writer in
  (* M7-T32: where `-s`'s initTime ends and its solveTime starts. *)
  let t_search = ref 0. in
  (* M6-T9, M6-T24 (D-0225). A run stopped from outside. SIGTERM (an outer `timeout`),
     SIGINT and SIGXCPU do not exit: the first one raises [stop_signal], which
     [config.stop] reads with the clock, so the search ends at its next poll exactly as
     under --time-limit -- proof ended, `limit:` line, exit 0. If it has not stopped
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
  (* M6-T24: the heap budget ends the proof before it exits. A run that has an incumbent
     has an answer to return, so it ends as a stopped run (exit 0); one that has none is
     still exit 5. *)
  let resource_code () = if have_incumbent () then exit_ok else exit_resource in
  (Encoding.resource_exit :=
     fun () -> stop_now (fun () -> killed_line "heap-budget") resource_code);
  let outcome =
    Fun.protect
      ~finally:(fun () -> Timing.phase "pbpclose" (fun () -> close_out proof_oc))
      (fun () ->
        Timing.phase "search" (fun () ->
            (* M1-T47. Writer's accumulator is process-wide and cumulative -- it has
               already counted Encoding.start_proof, which ran in [proofopen] -- so
               what belongs to [search] is the DIFFERENCE across this call and not the
               total. Sampled inside the phase so that the two brackets nest. *)
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
                  (* M6-T24: the synchronous resource arms, caught where the proof can
                     still be ended. [Writer.idle] is false when the exception came out of
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
      (* M6-T9. The FlatZinc standard's marker for "stopped with nothing to report";
         SPEC 2.2 does not list it yet (a request is filed). A stopped run that DID
         print solutions -- an optimisation run's improving ones -- prints nothing
         more: their `----------` lines are already out, and the absence of
         `==========` is exactly the statement that the last one is not proved
         optimal. *)
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

(* D-0150. What the standard flags became, on stderr: the two notes under --stats, -s or
   -v (so a run that asked for none of them keeps its stderr empty, M1-T49), and under -v
   also the resolved search and limit. D-0150's warning for -f is gone since D-0148 closed
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

(* D-0150. Enumeration is refused on a SATISFACTION model, after it is read (whether it
   is one is a property of the model, not of the command line). It needs two things that
   do not exist: a search that goes on past a solution ([Search.solve] returns the
   first), and a proof shape for "no other solution" -- VeriPB 3.0's `solx` excludes a
   solution only under a preserved set, which this project has no encoding for
   ([Writer.solution_excluding]). Printing one solution and letting `----------` stand
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

(* M6-T2 (D-0198). The minor heap is up to 4 M words (32 MB), not OCaml 5.1's 256 k words
   (2 MB). The solver allocates 14 to 23 words per thousand instructions everywhere, mostly data
   that dies within a branch or a conflict: trail entries of a level that is undone, an
   analysis's terms, a proof line's literals. In a 2 MB nursery much of it is promoted before
   it dies and the major collector pays for it again. At 4 M words promotion falls 2 to 9
   times, and the instructions by a median 7 % without the proof and 12 % with it (D-0198 §2
   and §4 have the tables).

   THE ADDRESS SPACE. OCaml 5.1 reserves the minor heaps of all [max_domains] = 128 possible
   domains in one mapping, so a 4 M-word nursery reserves 4 GiB of address space it never
   touches. Under [ulimit -v 4000000], which every suite and lane here runs under, the
   runtime then aborts at startup ("Not enough heap memory to reserve minor heaps"); the
   gate found it. So the size is cut until the reservation is at most an EIGHTH of the soft
   address-space limit read from /proc/self/limits: about 490 k words under a 4 GB cap, the
   full 4 M under the 32 GB cap of the corpus scripts or with no limit, and never below the
   runtime's default. No /proc (not Linux) reads as no limit. A quarter was tried first and
   lost the lane's lot-sizing [activity] run, whose major heap alone is 3.2 GB of its 4 GB
   cap, to an Out_of_memory (D-0198 §2).

   It changes WHEN memory is reclaimed, never a value: nothing in [lib/] reads an address, so
   stdout, proofs and --stats are the same bytes. It costs up to 32 MB resident per process.
   An explicit [s=] in OCAMLRUNPARAM or CAMLRUNPARAM wins, so [OCAMLRUNPARAM=s=256k] gives
   back the old behaviour without a rebuild. The test binaries do not link this file and keep
   the default. *)
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
  (* M1-T47. The writer's per-line clock is a syscall a line and stays off unless the
     numbers are being asked for; --time is the only thing in the tree that opens it. *)
  Writer.time_emission := opts.time;
  if opts.time then at_exit Timing.report;
  (* M7-T8. As early as possible and after the options are read: the alarm is the
     backstop for everything the clause budget cannot predict, so it wants to be armed
     before the first allocation that is not argument parsing. Installs nothing at all
     unless --max-heap-mb was asked for. *)
  Encoding.install_heap_guard ();
  (* D-0200. The alarm reads the heap only at the end of a major cycle, and a cycle on a
     heap of several GB can outlast the climb to the address-space limit. So the budget is
     also polled on a CPU-time ticker, ten times a second: every phase, every granularity
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
  match
    Timing.phase "parse" (fun () -> Fz_error.catch (fun () -> Builder.of_file opts.model))
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
      | Error e ->
          (* Compile raises through the front end's error type for everything SPEC 2.1
             requires a diagnostic for: an unimplemented builtin, a domain the encoding
             cannot express, an objective, a search annotation that is not what the
             search actually does. *)
          prerr_endline (Fz_error.to_string e);
          exit exit_unsupported
      | exception Baguette_proof.E2e.Not_covered why ->
          (* M14-e2e-verification-T3 (D-0187): the model has a construct the solver-written
             prefix does not cover. Refused before the search, like an unsupported
             builtin; the external bridge (tools/e2e/bridge.py) is the path for it. *)
          Printf.eprintf
            "baguette: --e2e: %s (D-0187). Run without --e2e and bridge the proof with \
             tools/e2e/bridge.py.\n"
            why;
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
      | exception Encoding.Encoding_too_large o ->
          (* M7-T8 / D-0071. The predictive guard. Not exit 3: this model is legal and
             a larger budget answers it. Not exit 4: nothing is broken. The whole point
             of the row is that a harness can tell this apart from both, and from the
             exit 134 it replaces. [Encoding] refuses before it allocates, so there is
             no partial encoding and no partial proof to warn about. *)
          prerr_string (Encoding.overrun_message o);
          exit_out_of_resource opts
      | exception Out_of_memory ->
          (* D-0200. One allocation the runtime could not map: the one failure of this
             kind that can be caught. "Fatal error: allocation failure during minor GC"
             cannot be, which is why the budget's poll exists. *)
          prerr_string (Encoding.out_of_memory_message ());
          exit_out_of_resource opts
      | exception Encoding.Heap_too_large o ->
          (* The reactive guard, caught synchronously at a declaration. Its sibling --
             the Gc alarm -- cannot come through here: it fires at an arbitrary point
             and exits with this same status itself. Same wording either way. *)
          prerr_string (Encoding.heap_message o);
          exit_out_of_resource opts
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
          (* M6-T9: under OCAMLRUNPARAM=b, say WHERE. The arm exists because the cap
             has a hole, and the only way to find the hole is the raise site; wave 31's
             sweep reached this on 2014_rectangle-packing with nothing to go on. *)
          if Printexc.backtrace_status () then prerr_string (Printexc.get_backtrace ());
          (* M1-T34. D-0029 decided that overflow RAISES rather than wrapping or quietly
             declining, and put a compile-time cap in front of the raise so that no model
             the CLI accepts can reach it. This arm is what happens if that cap is ever
             wrong, and without it the CLI would die on an uncaught exception -- "Fatal
             error: exception Baguette_core.Checked.Overflow(...)", exit 2, no context.

             Three deliberate choices:

             * It is attached to [solve] and nowhere else. [Builder.of_file] cannot
               raise this: builder.ml computes through Checked and turns an overflow
               into a positioned diagnostic ([lin_terms], M22-review-T1) or drops the
               fact ([facts_of], [infer_bounds]); lexer.ml, parser.ml and model.ml
               compute nothing that can overflow. [Compile.compile], [Search.solve] and
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
