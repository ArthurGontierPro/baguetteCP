(* A Gc.create_alarm heap guard: a shared test helper that aborts a test binary
   before it grows past a memory threshold, naming the binary and the cap it
   crossed, rather than letting `ulimit -v` (or nothing, when a session forgets
   to set one) kill it anonymously (M1-T53).

   M1-T53 weighed two routes: wrap the (tests) stanzas in a capped runner, or
   install a Gc alarm in a shared helper. This module is the second route,
   chosen because it is "the more honest fix" the roadmap row names: `ulimit -v`
   kills the process with an opaque MemoryError-shaped death that says nothing
   about which test caused it, whereas this alarm fires from inside the process
   and can name the binary and the threshold. It fails the test, not the
   machine.

   What this cannot see: only the OCaml minor/major heap, via
   [Gc.quick_stat ().heap_words]. A Bigarray, a C stub's own malloc, or any
   allocation outside the OCaml GC's bookkeeping does not move that counter and
   slips past this guard entirely -- exactly the kind of allocation `ulimit -v`
   (which counts the whole process's virtual memory, OCaml heap or not) would
   still catch. The two routes are complementary, not substitutes for each
   other: `ulimit -v 4000000` in CLAUDE.md's wrapped invocation remains the
   outer backstop; this alarm is the inner, self-naming one. Wrapping the
   (tests) stanzas themselves is still open -- it is the other route this
   task weighed and did not take, see WORKLOG.md.

   Usage: call [Mem_guard.install ()] once, as the first line of a test file's
   [let () = ...] body, before any test that allocates runs. The default
   threshold (2048 MB) is far above what any model in this suite should need
   under D-0028's width discipline, and comfortably below the 15 GB box shared
   by every concurrent session. Adoption by a suite this session does not own
   is a one-line addition: `Mem_guard.install ();` as the first line of that
   file's own [let () = ...] block (test_trace.ml, test_engine.ml,
   test_proof.ml and test_endtoend.ml do not have it yet -- cross-session
   request).

   This module has no unconditional top-level side effect, so linking it into
   test_compile.exe / test_output.exe changes nothing about their normal
   output. It has exactly one gated one: with MEM_GUARD_DEMO set in the
   environment, the module deliberately allocates past a tight cap and lets
   the alarm trip, as a hand-run demonstration that the mechanism works. Run
   it through either binary that links this module, with a timeout, e.g.:

     MEM_GUARD_DEMO=1 timeout 30 ./_build/default/test/unit/test_output.exe

   Because module initialisers run in dependency order, that demo runs and
   exits *before* test_output's own tests start -- it does not run them. *)

let word_bytes = Sys.word_size / 8

(* The cap an [install] with no explicit [limit_mb] uses. The environment override is
   not a convenience: without it the *installed* guard is unobservable, because the only
   thing that could demonstrate it is an allocation big enough to trip 2 GB, which is
   precisely the allocation this guard exists to prevent anyone running. With it, a
   one-line run proves a given binary's guard is armed:

     BAGUETTE_TEST_HEAP_CAP_MB=8 ./_build/default/test/unit/test_prop.exe   -> exit 3

   MEM_GUARD_DEMO below does NOT prove that: it installs a guard of its own, so it fires
   whether or not the binary ever called [install]. Telling those two apart is the whole
   point (M1-T53). *)
let default_limit_mb () =
  match Sys.getenv_opt "BAGUETTE_TEST_HEAP_CAP_MB" with
  | None | Some "" -> 2048
  | Some s -> (
      match int_of_string_opt (String.trim s) with
      | Some n when n > 0 -> n
      | _ ->
          Printf.eprintf
            "mem_guard: BAGUETTE_TEST_HEAP_CAP_MB=%S is not a positive number of MB\n%!" s;
          exit 2)

(* Arming and firing are two different claims, and only one of them is testable by
   allocating. Most binaries in this suite have a major heap so small that no cap above
   zero is ever crossed -- measured 2026-09-17: at BAGUETTE_TEST_HEAP_CAP_MB=1 only
   test_prop.exe and test_output.exe abort; the other ten exit 0. That is *not* evidence
   their guard is armed, and it is not evidence it is missing either: the run simply
   cannot tell. So arming announces itself on request, which can be checked in every
   binary regardless of how little it allocates:

     BAGUETTE_TEST_HEAP_CAP_ANNOUNCE=1 ./_build/default/test/unit/test_core.exe

   A binary that prints no `mem_guard: armed` line has not called [install], whatever its
   heap does. Without this, "the guard is installed everywhere" would be a claim nothing
   could falsify -- which is the failure mode M1-T53 is itself an instance of. *)
let install ?limit_mb ?(label = Filename.basename Sys.executable_name) () =
  let limit_mb = match limit_mb with Some n -> n | None -> default_limit_mb () in
  if Sys.getenv_opt "BAGUETTE_TEST_HEAP_CAP_ANNOUNCE" <> None then
    Printf.eprintf "mem_guard: armed at %d MB in %s\n%!" limit_mb label;
  let limit_words = limit_mb * 1024 * 1024 / word_bytes in
  let alarm = ref None in
  let check () =
    let heap_words = (Gc.quick_stat ()).Gc.heap_words in
    if heap_words > limit_words then (
      let heap_mb = heap_words * word_bytes / 1024 / 1024 in
      Printf.eprintf
        "\n\
         mem_guard: %s aborted -- OCaml heap reached %d MB, past the %d MB cap \
         (Gc.create_alarm, M1-T53)\n\
         %!"
        label heap_mb limit_mb;
      (match !alarm with
      | Some a ->
          Gc.delete_alarm a;
          alarm := None
      | None -> ());
      exit 3)
  in
  alarm := Some (Gc.create_alarm check)

(* ---------------------------------------------------------- hand-run demo only *)

let demo () =
  (* Deliberately trips the alarm: a 100 MB cap, allocated past in 20 MB steps
     so a major GC (and so the alarm) gets a chance to run between steps,
     capped at 400 MB total -- "a few hundred MB", per the house rule, and
     always run under an external `timeout`. *)
  install ~limit_mb:100 ~label:"mem_guard demo" ();
  let chunks = ref [] in
  for step = 1 to 20 do
    chunks := Bytes.create (20 * 1024 * 1024) :: !chunks;
    Gc.full_major ();
    Printf.printf "demo: allocated step %d (%d MB so far) and the alarm has not fired\n%!"
      step (step * 20)
  done;
  print_endline "FAIL mem_guard demo: allocated past the cap without the alarm firing";
  exit 1

let () = if Sys.getenv_opt "MEM_GUARD_DEMO" <> None then demo ()
