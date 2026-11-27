(* probe.ml: PROBING at the root -- failed literals, asserted negated at level 0
   (M19-config-T8, docs/DECISIONS.md D-0250; the SAT technique of Freeman's POSIT and of
   Lynce and Marques-Silva, the root "probing" of Chuffed and of CP-SAT).

   Consistency level: none -- this is not a propagator, it is a pass of the search before
   the first decision. Governing records: D-0250 (the rule, the measurement, the default),
   D-0018 (why a failed one-decision node's nogood is RUP), D-0077 (the level-0 clause a
   pruning rests on, and who retires it), docs/SPEC.md 3.4 (the search).

   Opt-in: BAGUETTE_PROBE=off|root, read once ([mode]); [off], the default, never calls
   [root] and leaves the search byte-identical to a build without this module.

   ---------------------------------------------------------------------------
   The rule
   ---------------------------------------------------------------------------

   After the root fixpoint and before the first decision, for each CANDIDATE literal [l]:

     open level 1, push [l] as a decision, propagate;
     fixpoint  -> undo the level, retire its lines: nothing is kept;
     conflict  -> [l] FAILED: write the level's trace and the conflict's line (the lines
                  any failed node writes), then, at level 0, the unit clause [~l]; undo
                  the level and retire its lines; push [~l] at level 0 with that clause as
                  its justification, and propagate at the root again. A conflict there is
                  the root conflict, closed by the search's own [close_root_conflict].

   The candidates are, in store order, every unfixed variable whose domain spans at most
   [width_cap] values, and for each its two BOUND literals: [x <= lo] (x = lo) and
   [x >= hi] (x = hi). For a Boolean those are its two polarities. A bound that fails
   moves, so the next pass probes the new bound (bounds shaving). Passes repeat while the
   last one failed a literal, until the BUDGET runs out: a number of propagator runs
   ([Engine.runs], counted over the whole probing including the root propagations it
   triggers), which is deterministic, or a CPU cap, which is not and is there for the
   propagators whose one run is expensive (see [default_budget]). The search's stop (the
   time limit) is polled between two probes and inside each propagation, as at a node.

   ---------------------------------------------------------------------------
   Why it is sound, and why the proof needs no new rule
   ---------------------------------------------------------------------------

   A probe is EXACTLY a one-decision search node: [Search.branch_split]'s first child at
   the root, with the same push ([Explanation.decision], [Reason.none]) and the same
   propagation. When it fails, D-0018's argument gives its nogood [~l] as `rup`: negate
   it, that asserts [l], and the trace lines just written (each "facts -> claim", decision
   free) unit propagate the level's prunings in order up to the conflict's line, which is
   falsified. The only difference from the node is WHERE the clause is filed: at level 0
   rather than at level 1, because no decision of level 0 is in it, so it is globally
   valid; [Justify.with_level 0] files it there and the wipe of level 1 does not take it.

   The negation [~l] is then a level-0 PRUNING whose explanation is that clause and whose
   reason has no facts -- the shape of D-0077's assignment clause at p = 0
   ([Search.branch_assign], [Reason.none] because no decision is active). [Trace] writes
   its line [~l] (or, past a hole, the settled bound with the holes' facts: I-X9, a line
   justifies the bound as recorded on the trail) as it writes any level-0 line,
   permanently, and the clause stays live until the end of the search: the search records
   its id with the assignment clauses ([stats.assign_clauses_rev]) and
   [retire_assign_clauses] deletes it with them (I-X2: every id is deleted exactly once).

   No [Explanation.t] constructor and no proof rule is added. What is added is ORDER: the
   lines of a failed probe are the lines of the node it is, written before the search
   starts.

   Two traps of CLAUDE.md's proof discipline, and how this stands against them. A `rup`
   over a contradictory database accepts anything (D-0053, D-0066): a probe's unit clause
   is written on a database the root fixpoint left consistent, and test_search_strategy.ml
   flips the derived literal of a probe on SATISFIABLE models and asserts the checker's
   RUP wording, which is the load-bearing check, not the answer.

   ---------------------------------------------------------------------------
   Consistency with docs/SPEC.md 3.4
   ---------------------------------------------------------------------------

   The tree is still the annotation's (or the default's), depth first, explored once. A
   failed literal changes the ROOT DOMAINS the search starts from, by a pruning every
   solution satisfies, exactly as a stronger root propagator would; it takes no decision
   the search reports and changes no variable or value choice rule. So it is a
   propagation, not a strategy substitution, and 3.4's "anything else MUST be refused"
   does not bear on it. It does change which node the first-fail rule meets first (a
   domain is smaller), the same way any propagator does. A sentence is proposed for 3.4
   in D-0250 section 5; it is not written into SPEC.md.

   ---------------------------------------------------------------------------
   What it does not do (D-0250 section 7)
   ---------------------------------------------------------------------------

   No necessary assignments (a literal implied by both polarities of a Boolean): its
   proof needs the two implications as clauses, so the SURVIVING level's trace written as
   well, which is not the failed-node shape and costs a trace walk per survivor. No
   learning from a probe's conflict: the 1UIP clause would be stronger than [~l] at times,
   but it would put a learned constraint on the engine for each failure. No equality
   merging, no LP. *)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer

type mode = Off | Root

let mode_of_env () =
  match Sys.getenv_opt "BAGUETTE_PROBE" with
  | None | Some ("" | "off") -> Off
  | Some "root" -> Root
  | Some v ->
      (* The discipline of BAGUETTE_CDCL: a misspelt switch FAILS rather than silently
         running the default. *)
      prerr_endline
        (Printf.sprintf "baguette: BAGUETTE_PROBE=%S is not a setting. Use off or root." v);
      exit 2

let current : mode option ref = ref None

(* Read once, then remembered; [set_mode] is the tests' door. *)
let mode () =
  match !current with
  | Some m -> m
  | None ->
      let m = mode_of_env () in
      current := Some m;
      m

let set_mode m = current := Some m

(* The budget, in propagator runs ([Engine.runs]), the CPU cap and the width cap. Defaults
   chosen on the census of D-0250 section 3: run to completion, the pass costs a median of
   3.8 M runs and 0.7 s, but a run is not a unit of time (2011_pentominoes_04 spends 0.19
   s per probe at 23 runs each, black-hole 14 half a second), so the runs budget, which is
   deterministic, is backed by a CPU cap, which is not. The cap fires only where a pass is
   heavy, and there it makes the probe set depend on the machine's speed; under the
   default [off] nothing is read. BAGUETTE_PROBE_BUDGET (runs), BAGUETTE_PROBE_CPU
   (seconds, 0 for none) and BAGUETTE_PROBE_WIDTH override them for measurement; a
   malformed value FAILS. *)
let default_budget = 5_000_000
let default_cpu_cap = 10
let default_width_cap = 64

let int_env name default =
  match Sys.getenv_opt name with
  | None | Some "" -> default
  | Some v -> (
      match int_of_string_opt v with
      | Some n when n >= 0 -> n
      | _ ->
          prerr_endline
            (Printf.sprintf "baguette: %s=%S is not a setting. Use an integer >= 0." name
               v);
          exit 2)

let budget_override : int option ref = ref None
let set_budget b = budget_override := Some b

let budget () =
  match !budget_override with
  | Some b -> b
  | None -> int_env "BAGUETTE_PROBE_BUDGET" default_budget

let width_cap () = int_env "BAGUETTE_PROBE_WIDTH" default_width_cap
let cpu_cap () = int_env "BAGUETTE_PROBE_CPU" default_cpu_cap

(* What the search lends this pass: the steps a failed node writes, which are Search's and
   must stay one rule for both (D-0250 section 2). *)
type hooks = {
  state_conflict : Store.conflict -> unit;
      (** the conflict's own line, [Search.state_conflict] *)
  bridges : Lit.t list -> unit;
      (** [Search.bridges] over the open decisions (a bound probe never settles, so it
          writes nothing; called so the shape is the node's) *)
  close_root : Store.conflict -> Writer.cid;
      (** [Search.close_root_conflict]: the empty clause *)
  root_clause : Writer.cid -> unit;
      (** a level-0 clause the search retires at its end (D-0077's list) *)
}

type result = Fixpoint | Refuted of Writer.cid

(* The search's stop fired during the pass. [Search] turns it into its own [Limit_hit];
   the proof is ended where it stands, which a probe level open on the page allows as
   any open level does (I-X2's interrupted exemption). *)
exception Stopped

type census = {
  mutable candidates : int;  (** variables in scope at the first pass *)
  mutable probed : int;  (** literals pushed *)
  mutable failed : int;  (** literals that failed, i.e. units asserted at level 0 *)
  mutable passes : int;
  mutable runs : int;  (** propagator runs spent, the budget's currency *)
  mutable cpu : float;  (** seconds of CPU, for the census only, never for a choice *)
  mutable budget_hit : bool;
  mutable refuted : bool;
  mutable stopped : bool;  (** the search's stop fired during the pass *)
  mutable units : Writer.cid list;
      (** the level-0 unit clauses written, newest first: the tests flip them *)
}

let last : census option ref = ref None

let stats_enabled () =
  match Sys.getenv_opt "BAGUETTE_PROBE_STATS" with
  | Some ("1" | "on") -> true
  | _ -> false

let report c =
  if stats_enabled () then
    Printf.eprintf
      "probe: candidates=%d probed=%d failed=%d passes=%d runs=%d cpu=%.3f budget_hit=%b \
       refuted=%b stopped=%b\n\
       %!"
      c.candidates c.probed c.failed c.passes c.runs c.cpu c.budget_hit c.refuted
      c.stopped

let propagate ~stop ~poll_runs engine store =
  match
    if poll_runs > 0 then Engine.propagate ~stop ~poll_runs engine store
    else Engine.propagate engine store
  with
  | r -> r
  | exception Engine.Stopped -> raise Stopped

(* One side of one variable. [`Lo] probes [x <= lo], [`Hi] probes [x >= hi]. Answers
   [`Survived], [`Failed] (the negation is now on the root) or [`Refuted cid]. *)
let probe_one ~engine ~store ~(ctx : Justify.ctx) ~trace ~stop ~poll_runs ~hooks census v
    side =
  let d = Store.get store v in
  let lo = Domain.lo d and hi = Domain.hi d in
  let name = Store.name store v in
  (* The decision literal, and the atom [Search.branch_split] would mint for the same
     split: [x_ge_(lo+1)] for the low side, [x_ge_hi] for the high one. *)
  let lit, atom =
    match side with
    | `Lo -> (Lit.le name lo, Lit.ge name (lo + 1))
    | `Hi -> (Lit.ge name hi, Lit.ge name hi)
  in
  if not (Writer.is_null ctx.Justify.writer) then Justify.ensure_lit ctx atom;
  let w = ctx.Justify.writer in
  census.probed <- census.probed + 1;
  Store.new_level store;
  Writer.set_level w 1;
  let decided = Reason.because ~concludes:None Reason.none (Explanation.decision lit) in
  (match
     match side with
     | `Lo -> Store.set_hi store v lo decided
     | `Hi -> Store.set_lo store v hi decided
   with
  | Store.Changed -> ()
  | Store.Unchanged | Store.Conflict _ ->
      invalid_arg "Probe: a bound probe on an unfixed domain did not narrow it");
  if Debug.enabled then
    Debug.check "D-0018: a probe's decision is the first trail entry of level 1"
      (fun () ->
        Store.level store = 1 && Store.is_level_start store (Store.trail_length store - 1));
  let leave () =
    Store.backtrack store;
    Writer.set_level w 0;
    Justify.wipe_level ctx 1
  in
  match propagate ~stop ~poll_runs engine store with
  | Engine.Fixpoint ->
      leave ();
      `Survived
  | Engine.Conflict c -> (
      (* The failed node's lines, in D-0018's order: its trace, its conflict line, its
         bridges; then its nogood, filed at level 0. *)
      (try Trace.emit ~stop ctx trace store with Trace.Stopped -> raise Stopped);
      hooks.state_conflict c;
      hooks.bridges [ lit ];
      let neg = Lit.negate lit in
      let unit = Explanation.clause [ neg ] in
      let cid = Justify.with_level ctx 0 (fun () -> Justify.emit ctx unit) in
      hooks.root_clause cid;
      census.units <- cid :: census.units;
      leave ();
      census.failed <- census.failed + 1;
      let because = Reason.because ~concludes:None Reason.none unit in
      (match
         match side with
         | `Lo -> Store.set_lo store v (lo + 1) because
         | `Hi -> Store.set_hi store v (hi - 1) because
       with
      | Store.Changed -> ()
      | Store.Unchanged | Store.Conflict _ ->
          invalid_arg "Probe: the negation of a failed bound probe did not narrow");
      match propagate ~stop ~poll_runs engine store with
      | Engine.Fixpoint -> `Failed
      | Engine.Conflict c -> `Refuted (hooks.close_root c))

(* The pass. Called by [Search.search_core] at level 0, before the first decision, under
   [mode () = Root] only. *)
let rec root ~engine ~store ~(ctx : Justify.ctx) ~trace ~stop ~poll_runs ~hooks : result =
  let t0 = Sys.time () in
  let runs0 = !Engine.runs in
  let census =
    {
      candidates = 0;
      probed = 0;
      failed = 0;
      passes = 0;
      runs = 0;
      cpu = 0.;
      budget_hit = false;
      refuted = false;
      stopped = false;
      units = [];
    }
  in
  last := Some census;
  let finish r =
    census.runs <- !Engine.runs - runs0;
    census.cpu <- Sys.time () -. t0;
    (match r with Refuted _ -> census.refuted <- true | Fixpoint -> ());
    report census;
    r
  in
  if Store.level store <> 0 then invalid_arg "Probe.root: called above level 0";
  (* A stop during the pass still reports what it spent, then leaves as the search's. *)
  try pass ~engine ~store ~ctx ~trace ~stop ~poll_runs ~hooks census runs0 ~finish
  with Stopped ->
    census.stopped <- true;
    ignore (finish Fixpoint : result);
    raise Stopped

and pass ~engine ~store ~ctx ~trace ~stop ~poll_runs ~hooks census runs0 ~finish =
  let budget = budget () and cap = width_cap () in
  match propagate ~stop ~poll_runs engine store with
  | Engine.Conflict c -> finish (Refuted (hooks.close_root c))
  | Engine.Fixpoint -> (
      let in_scope v =
        let d = Store.get store v in
        (not (Domain.is_fixed d)) && Domain.hi d - Domain.lo d < cap
      in
      let n = Store.n_vars store in
      for i = 0 to n - 1 do
        if in_scope (Var.of_int i) then census.candidates <- census.candidates + 1
      done;
      let exception Done of result in
      let cpu = float_of_int (cpu_cap ()) and t0 = Sys.time () in
      let spent () =
        !Engine.runs - runs0 >= budget || (cpu > 0. && Sys.time () -. t0 >= cpu)
      in
      try
        let again = ref true in
        while !again do
          again := false;
          census.passes <- census.passes + 1;
          for i = 0 to n - 1 do
            let v = Var.of_int i in
            List.iter
              (fun side ->
                if in_scope v then (
                  if spent () then (
                    census.budget_hit <- true;
                    raise (Done Fixpoint));
                  if stop () then raise Stopped;
                  match
                    probe_one ~engine ~store ~ctx ~trace ~stop ~poll_runs ~hooks census v
                      side
                  with
                  | `Survived -> ()
                  | `Failed -> again := true
                  | `Refuted cid -> raise (Done (Refuted cid))))
              [ `Lo; `Hi ]
          done
        done;
        finish Fixpoint
      with Done r -> finish r)
