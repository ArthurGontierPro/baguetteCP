(* Debug-mode invariant checking.

   docs/INVARIANTS.md asks that assertions guarded by BAGUETTE_DEBUG=1 check as many of
   the invariants as is affordable. The flag is read once, at module initialisation, so
   the common (disabled) path is a single boolean test that the compiler can hoist. *)

let enabled =
  match Sys.getenv_opt "BAGUETTE_DEBUG" with
  | Some ("1" | "true" | "yes" | "on") -> true
  | _ -> false

(* [check name f] evaluates [f] only when debugging is on. Raising rather than using
   [assert] so the message survives a build with -noassert, and so the invariant tag
   (an id of docs/INVARIANTS.md such as I-D2, holes are never at the bounds, or I-T1,
   backtracking restores every domain exactly) reaches the person reading the failure. *)
let check name f = if enabled && not (f ()) then failwith ("invariant violated: " ^ name)

(* ------------------------------------------------------ the consistency oracle gate

   A second, independent gate, added by M2-T10: at every search node it checks each
   propagator's claimed consistency level against a brute-force oracle. [enabled] above
   buys the invariant assertions, which are cheap enough that a debug run of the whole
   suite stays in seconds. The consistency oracle is not in that class: it enumerates
   tuples over live domains at every search node, so its cost is a product of domain sizes
   and it would dominate anything it was folded into. Hence its own switch rather than a
   third meaning for BAGUETTE_DEBUG -- someone debugging an invariant violation should not
   silently pay for brute force, and someone auditing consistency levels should not have
   to turn on assertions that force every deferred justification (see
   [Store.check_agreement]'s header for why that changes what a run can observe).

   Read once, at module initialisation, so the disabled path is one boolean test. *)
let consistency_enabled =
  match Sys.getenv_opt "BAGUETTE_CONSISTENCY" with
  | Some ("1" | "true" | "yes" | "on") -> true
  | _ -> false

(* The tuple budget per (instance, variable, value) support search. An instance whose
   scope is too wide for brute force is SKIPPED and counted, never quietly passed: see
   [Engine.oracle_skipped]. The default is deliberately small -- the 15 GB of RAM of the
   laptop is shared by every session running there, and an unbounded product over domains
   is exactly the shape that reaches the ceiling. Raise it for a deliberate, explained
   audit. *)
let consistency_cap =
  match Option.map int_of_string_opt (Sys.getenv_opt "BAGUETTE_CONSISTENCY_CAP") with
  | Some (Some n) when n > 0 -> n
  | _ -> 4096

(* The oracle's REPORT, separately again, and this one is not fussiness.

   The solver writes nothing to stderr without --time, and scripts/run_model_tests.sh
   enforces it per model; that standing contract comes from M1-T49, which found that a
   gate diffing stdout alone could not see timings printed unasked. So a trace line
   printed whenever BAGUETTE_CONSISTENCY is on would fail every model for writing it
   (all 57 of them at the time) -- which
   is what happened the first time this was wired, and it would have made the one suite
   the oracle most needs to run over the one suite it could not run over.

   BAGUETTE_CONSISTENCY therefore CHECKS and stays silent; BAGUETTE_CONSISTENCY_TRACE
   additionally reports. Reading the counters directly ([Engine.oracle_stats]) is the
   third way and is what test/unit/test_consistency.ml uses. *)
let consistency_trace =
  match Sys.getenv_opt "BAGUETTE_CONSISTENCY_TRACE" with
  | Some ("1" | "true" | "yes" | "on") -> true
  | _ -> false
