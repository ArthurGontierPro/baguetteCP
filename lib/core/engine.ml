(* engine.ml: the propagation fixpoint (M1-T10, Part 1).

   docs/ARCHITECTURE.md section 5: "A priority queue of propagator ids ... pops, runs,
   applies the resulting changes to the trail, and re-queues the propagators watching
   the changed variables." This is that queue, minus the cost-class ordering
   (docs/ARCHITECTURE.md's "cheap bounds propagators before all_different" -- M1 has no
   propagator above [Bounds] consistency yet, so a plain FIFO is honest; a priority
   ordering is a scheduling refinement for when that stops being true, not a
   correctness requirement, and adding one now would be sorting a list of one).

   Waking is by watched variable, not "run everyone again" (the task's explicit
   requirement, and the only way I-P2 -- fixpoint means propagating again changes
   nothing -- can be cheap to hold). [Store] does not track "who changed since I last
   looked" itself, so this module keeps its own trail cursor and, after each
   propagator call, diffs the trail against it to find the newly-touched variables
   (docs/ARCHITECTURE.md section 3: the trail is exactly the log of domain changes,
   most-recent-first). That is O(new entries) per propagator call, not O(n_vars); for
   the domain sizes and propagator counts M1 deals with, simplicity here is worth more
   than a smarter incremental cursor would be.

   This module never touches the proof (the task's Part 1 instruction, and
   docs/ARCHITECTURE.md's "Deferred explanations"): a [Conflict] hands back whatever
   [Explanation.t] the failing propagator built, unrendered, and it is search's job
   (search.ml) to decide whether and how a reason is ever turned into proof rules.

   M2-T5 adds two things to that picture.

   (1) Trigger masking. Waking was by watched variable but not by *kind* of change: a
   propagator that reads only [lo] and [hi] was re-run when some other propagator punched
   a hole in the middle of a domain, which by construction cannot change what it computes.
   Each instance now carries a [trigger] saying which [Domain.change] kinds wake it, and
   [watchers_of_new_entries] classifies each new trail entry and drops the wakes the
   trigger does not want.

   (2) [check_fixpoint], the I-P2 re-run check. This is not a nicety; it is the safety net
   that makes (1) testable at all. An over-aggressive mask does not crash and does not
   make the proof fail - everything that WAS derived was still derived correctly, so
   veripb is happy - it just silently prunes less, and in the worst case reports an
   assignment that violates a constraint nobody woke to check. The only direct evidence is
   "at the fixpoint, some propagator still has something to say", which is exactly I-P2,
   and exactly what [check_fixpoint] looks for. It runs under BAGUETTE_DEBUG, and it is
   the thing to switch on first when a starved wake is suspected.

   M2-T7 adds the third thing this module owns: it is the only place that knows WHICH
   propagator is running, so it is the only place that can record it. [Store] holds the
   trail and stamps each entry, but [Store] cannot see a [Propagator.instance] at all
   (the dependency runs the other way), so the engine brackets every [run] with
   [Store.with_running] and then reads the stamp back in [check_attribution]. See
   [Store.entry]'s [prop] field for why the id is stamped from here rather than passed in
   by the propagator.

   M6-T21 (D-0136) adds the fourth: a STOP POLL between two propagator runs. [propagate]
   takes the caller's [?stop] predicate (the search passes [config.stop], i.e. the clock
   `--time-limit` reads) and asks it after every [?poll_runs]-th COMPLETED run of this
   engine -- never during one, so no propagator is ever left half-way through a domain
   update. When it says yes, the loop leaves without running anything else, does the
   same low-water reset a [Conflict] return does, records NO fixpoint (the store is not
   at one), and raises [Stopped]. Nothing here touches the proof (above), so at that
   point the writer holds exactly what it held when the call began: the node's prunings
   are trail entries with unrendered explanations, nothing more. [Search.dfs] turns
   [Stopped] into its own node-entry stop, and the run ends through M6-T9's path. Why
   the point is consistent, and what it costs (nothing measurable), is D-0136. Without
   [?stop] the loop is exactly what it was: the countdown is one decrement per run. *)

type outcome = Fixpoint | Conflict of Store.conflict

(* M6-T21: [propagate] was told to stop, between two runs; see the header. Never escapes
   [Search], which re-raises it as its node-entry stop. *)
exception Stopped

(* M6-T21: runs between two asks of [?stop], when the caller does not say. A clock read
   (Unix.gettimeofday through the CLI's closure) every 128 runs is noise next to 128
   propagator calls; on the codes model of D-0136 (47 k runs/s late in a 600 s run) 128
   runs take about 3 ms, which bounds the stop's latency there. *)
let default_poll_runs = 128

(* ------------------------------------------------------------------ triggers *)

(* Which kinds of [Domain.change] on a watched variable wake this instance. One field per
   non-[NoChange] constructor of [Domain.change], deliberately: when a new kind of change
   is added there, this record stops compiling and whoever adds it has to say what it
   means for waking, rather than having it default to "nobody cares".

   There is no [on_bound = false] instance today and it is hard to imagine a sound one -
   a bound move strictly shrinks the value set, so anything a propagator can read gets
   weaker - but the field is here rather than assumed so that the mask reads as a mask
   and not as a boolean with a long name. *)
type trigger = { on_bound : bool; on_holes : bool }

let wake_on_any = { on_bound = true; on_holes = true }
let wake_on_bounds = { on_bound = true; on_holes = false }

(* THE SOUNDNESS ARGUMENT, in full, because a mistake here is invisible (M2-T5):

   Skipping a wake is sound exactly when re-running that propagator after that change
   would have pruned nothing. For an interior hole - [Domain.Holes], which by
   construction leaves [lo] and [hi] where they were - that holds for any propagator
   whose output is a function of the bounds of its variables and nothing else. It reads
   the same [lo] and [hi] as before, so it computes the same thing, so it prunes nothing
   new. Nothing weaker than "reads only the bounds" will do: a propagator that consults
   [Domain.mem], [Domain.size] or [Domain.iter] can see the hole and must be woken.

   [Propagator.consistency] is the only per-instance declaration available, so it is what
   the default derivation below reads - and note that this is a *stretch of its meaning*.
   docs/GLOSSARY.md defines "bounds consistent" as a promise about a propagator's OUTPUT
   ("guarantees lo and hi of each variable can be extended to a solution, saying nothing
   about interior values"), while what is needed here is a statement about its INPUT.
   The two coincide for every propagator in the tree today, checked by reading them:
   [linear.ml] and [bool2int.ml] are the only [Bounds] instances (int_le, int_lt, lin_eq
   and int_eq are all [Linear.t] values), and each touches [Domain.lo] and [Domain.hi]
   and no other domain reader. [ne.ml] declares [Value] and does read [Domain.mem], and
   [bool_clause.ml] declares [Domain], so both keep [wake_on_any].

   That coincidence is not a theorem, and this is the gap to close: either
   [Propagator.instance] grows a [trigger] field that an instance states for itself, or
   docs/GLOSSARY.md's "bounds consistent" is extended to say a Bounds propagator reads
   only bounds. Both are outside this round's file ownership; M2-T5's report asks for one
   of them. Until then, a NEW [Bounds] propagator that reads holes would be starved -
   and would be caught by [check_fixpoint] below under BAGUETTE_DEBUG, which is why that
   check ships in the same round as this mask and not later. *)
let trigger_of_consistency = function
  | Propagator.Bounds -> wake_on_bounds
  | Propagator.Domain | Propagator.Value | Propagator.Checking -> wake_on_any

let default_trigger (inst : Propagator.instance) =
  trigger_of_consistency inst.Propagator.inst_consistency

let wakes_on trig (c : Domain.change) =
  match c with
  | Domain.NoChange -> false
  | Domain.Bound _ -> trig.on_bound
  | Domain.Holes _ -> trig.on_holes

(* --------------------------------------------------------------- counters *)

(* Wake bookkeeping. A masked wake is invisible in the answer and invisible in the proof
   (docs/ROADMAP.md M2-T5: "a skipped wake is invisible except in the node count"), so
   the one thing that must not also be invisible is whether the mask fires at all. These
   are process-global rather than per-engine because the interesting question is asked of
   a whole solve, across every engine a run builds. Three [incr]s on the fixpoint loop's
   hot path, which is noise next to a propagator call. *)
let runs = ref 0
let wakes = ref 0
let masked_wakes = ref 0

let reset_stats () =
  runs := 0;
  wakes := 0;
  masked_wakes := 0

let stats () = (!runs, !wakes, !masked_wakes)

(* M2-T6 deliverable 1: the three counters GCS prints under `-s`, PER ENGINE.

   [c_runs]       propagator runs taken off the queue by [propagate]          (GCS
                  `propagations`).
   [c_effectful]  runs that returned [Fixpoint] AND grew the trail, i.e. changed at
                  least one domain                                 (GCS
                  `effectfulPropagations`).
   [c_contra]     runs that returned [Conflict]                     (GCS
                  `contradictingPropagations`). A run that pruned and then failed is
                  counted here and NOT in [c_effectful]: the two are disjoint, so
                  [c_runs - c_effectful - c_contra] is exactly the number of runs that
                  did nothing at all, which is the number the wake discipline is for.
   [c_wakes] [c_masked]  the M2-T5 pair, per engine as well.

   Only the fixpoint loop counts. [check_fixpoint] (the re-checker) and the M2-T10
   consistency oracle run propagators too, but they are audits of the loop and must not
   inflate the figure they audit -- a BAGUETTE_DEBUG run reports the same counts as a
   plain one.

   Per engine and not process-global (the globals above stay, for BAGUETTE_WAKE_STATS
   and for the tests that predate this) because a solve builds exactly one engine
   ([Compile.compile]) and [bin/main.ml] prints this record beside [Search.stats],
   which is per solve too: a counter that outlived its run could not sit on the same
   `limit:` line as the node count it is divided by. Counted by the engine, never read
   from the proof (M1-T36's rule). *)
type counters = {
  mutable c_runs : int;
  mutable c_effectful : int;
  mutable c_contra : int;
  mutable c_wakes : int;
  mutable c_masked : int;
  mutable c_seeded : int;
      (** runs taken from the SEED: every [propagate] call walks one seed slot per
          instance, in id order, and runs the slots that are DIRTY (M6-T18: watching a
          change since the last joint fixpoint, woken before their slot came up, or not
          yet established). [c_runs - c_seeded] is the runs that came from wakes. Before
          M6-T18 every slot was run, so this grew by [n_instances] per call. *)
  mutable c_skipped : int;
      (** M6-T18: seed slots passed over as CLEAN -- the run the pre-M6-T18 engine made
          there and that, by [propagate]'s argument, could prune nothing.
          [c_seeded + c_skipped] is the old [c_seeded]. *)
  mutable c_vetoed : int;
      (** M2-T6 deliverable 2: self-wakes dropped because the instance's idempotence
          claim is honoured ([honours_claim]). Counted apart from [c_masked]: a mask
          drops a wake by KIND of change, the veto by WHO made it. *)
  mutable c_advised : int;
      (** M6-T20 / D-0104: wakes (and seed marks) the instance's own [inst_advise]
          declined, after the mask and the veto let them through. *)
}

let counters_create () =
  {
    c_runs = 0;
    c_effectful = 0;
    c_contra = 0;
    c_wakes = 0;
    c_masked = 0;
    c_seeded = 0;
    c_skipped = 0;
    c_vetoed = 0;
    c_advised = 0;
  }

(* Off unless asked for: BAGUETTE_WAKE_STATS=1 prints the counters to stderr at exit.
   stderr, not stdout, so that scripts/run_model_tests.sh's diff against
   test/expected/*.out is untouched by it. *)
let () =
  match Sys.getenv_opt "BAGUETTE_WAKE_STATS" with
  | Some ("1" | "true" | "yes" | "on") ->
      at_exit (fun () ->
          Printf.eprintf "baguette: propagator runs=%d wakes=%d masked=%d\n" !runs !wakes
            !masked_wakes)
  | _ -> ()

(* ------------------------------------------------------------------- engine *)

type t = {
  mutable instances : Propagator.instance array;
      (** By id, [0 .. count - 1]; the slots past [count] are [vacant] (M6-T22). *)
  mutable count : int;
      (** M6-T22 / D-0138: the number of instances. Every id-indexed array of this record
          is at least this long and grows by DOUBLING in [add]; before M6-T22 each grew
          by one, so a learned clause copied six arrays of the whole database. *)
  (* var -> ids of the propagator instances that read it. Built once at [create] time
     from each instance's [inst_vars]; instances never change their variable set after
     that, so the table does not need to be rebuilt per call. *)
  watchers : (Var.t, int list) Hashtbl.t;
  (* id -> that instance's trigger mask, indexed by [Propagator.id] (not by position in
     [instances]) because that is what the watcher lists hold. Any id with no instance
     gets [wake_on_any]: an unknown instance is one whose reads are unknown, and the safe
     answer for an unknown reader is always "wake it". *)
  mutable triggers : trigger array;
  ctr : counters;  (** M2-T6: this engine's run counters, see [counters]. *)
  mutable runs_by_id : int array;
      (** M6-T20, MEASUREMENT ONLY: runs and effectful runs PER INSTANCE, indexed by id
          and grown on demand, so [family_table] can say which propagator FAMILY the
          [c_runs] of a solve belong to. One array write per run; nothing reads them
          but the report. *)
  mutable eff_by_id : int array;
  mutable veto : bool array;
      (** M2-T6: id -> whether this instance's own prunings may skip re-waking it, i.e.
          [honours_claim]. Indexed by id like [triggers], grown by [add] like it, and an
          id with no entry is [false]: an unknown instance is re-woken. *)
  mutable born : int array;
      (** M6-T18: id -> the [epoch] of the first [Fixpoint] return after which this
          instance has been at its fixpoint, or [unborn] until there has been one. An
          instance is known to be at its fixpoint at a recorded fixpoint state only if
          it was born at or before that state's epoch. Grown by [add] with [unborn]. *)
  mutable epoch : int;  (** M6-T18: the number of [Fixpoint] returns so far. *)
  mutable fixpoints : (int * int) list;
      (** M6-T18: the joint fixpoints this engine has returned whose state is still the
          store's, as [(trail length, epoch)], most recent first and strictly decreasing
          in length. See [propagate]. *)
  mutable seen : (Store.t * int) option;
      (** M6-T18: the store [propagate] last ran on, and its low-water handle. *)
  mutable incremental : bool;
      (** M6-T18: [false] makes every call seed every instance, as before M6-T18. For
          tests that compare the two; a solve never sets it. *)
  mutable poll_left : int;
      (** M6-T21: completed runs left before [propagate] next asks its [?stop]. PER
          ENGINE and carried ACROSS calls, so a long run of short nodes still polls on
          schedule; only a call given [?stop] counts it down. *)
  mutable scopes : int array array;
      (** M6-T22 / D-0138: id -> the instance's [inst_vars] as SORTED, DEDUPLICATED
          variable ints, so [check_attribution] answers "does [id] watch [v]" by binary
          search. Indexed by id and grown by [add] like [triggers]; an id with no entry
          has the empty scope. See [in_scope] for why this replaced a walk of the
          watcher list. *)
  mutable wake_static : int list array;
      (** M6-T22 / D-0138: variable int -> the ids of the instances with NO
          [inst_watched] that read it, newest first. The wake loops' copy of [watchers]
          minus the self-watching instances, indexed by array rather than hashed. Grown
          on demand; a variable past its end has no such reader. *)
  mutable moved : Bytes.t;
      (** M11-complexity-T3 (D-0142, E1): variable int -> the bound moves (bit 1 lower,
          bit 2 upper) of the entries [watchers_of_new_entries] has walked so far, i.e.
          of this walk's NEWER entries on the variable. All zero between walks; sized
          with [wake_static]. *)
  mutable dyn_ids : int array array;
  mutable dyn_len : int array;
      (** M6-T22 / D-0138: WATCH SLOT -> the self-watching instances that CURRENTLY
          watch it, as [dyn_ids.(s).(0 .. dyn_len.(s) - 1)], in no particular order. The
          invariant, kept by [sync_watched]: [id] is there exactly once iff [s] is
          [wv1.(id)] or [wv2.(id)]. A slot is a [Propagator.watch], three per variable
          [x]: [3x] for a watch any change of [x] may falsify, [3x + 1] for one only a
          LOWER-bound move falsifies, [3x + 2] for one only an UPPER-bound move does
          (M11-complexity-T3, D-0142, E1; "The wake index by direction" below). *)
  mutable wv1 : int array;
  mutable wv2 : int array;
      (** M6-T22 / D-0138: id -> the two watch slots a self-watching instance reported
          at the end of its last run, or [-1] before its first. *)
  mutable wp1 : int array;
  mutable wp2 : int array;
      (** M6-T22 / D-0138: id -> where its entry sits in [dyn_ids.(wv1.(id))] and
          [dyn_ids.(wv2.(id))], so a watch move removes it in O(1). When both watches are
          in one slot there is one entry and [wp1] holds it. *)
  mutable births : (int * int list) list;
  mutable newborns : int list;
      (** M6-T22 / D-0138: [born], inverted. [newborns] is every id whose [born] is
          [unborn]; [births] holds, most recent first and so in DECREASING epoch, one
          [(e, ids)] per epoch some instance is born at, with exactly the ids whose [born]
          is [e]. So "every id born after epoch [e]" is [newborns] plus the head of
          [births] down to [e], and [propagate] reads and updates [born] through it in
          time proportional to the instances concerned rather than to all of them. *)
  mutable heap : int array;
  mutable heap_len : int;
      (** M6-T22 / D-0138: the DIRTY seed slots of the current [propagate] call, as a
          binary min-heap of ids, so the seed visits them in id order without walking the
          clean ones. An id is in it iff its [dirty] flag is set. Empty between calls. *)
  mutable dirty : bool array;
  mutable in_queue : bool array;
      (** M6-T22 / D-0138: [propagate]'s seed marks and queue membership, by id, kept
          from one call to the next and ALL FALSE between calls ([propagate] clears what
          it set, on every exit). They were allocated per call: two arrays of the whole
          database per search node, in the major heap once past 256 instances. *)
  mutable declined : (int * Var.t) list;
      (** M11-complexity-T3 (D-0142 section 1): under BAGUETTE_DEBUG only, the asks the
          advisors declined during the current wake walk or seed, newest first, waiting
          for [check_declined]. Always [[]] when BAGUETTE_DEBUG is off. *)
}

let unborn = max_int

(* M6-T22: the filler of [instances] past [count]. Never run: every reader of
   [instances] stops at [count]. *)
let vacant : Propagator.instance =
  {
    Propagator.id = -1;
    inst_name = "<vacant>";
    inst_consistency = Propagator.Checking;
    inst_vars = [];
    run = (fun _ -> Propagator.Fixpoint);
    inst_row = Propagator.no_row;
    inst_advise = Propagator.advise_always;
    inst_watched = None;
    inst_idempotent = false;
  }

(* M6-T22: [a] with room for index [id], doubling, the new slots [fill]. *)
let room a id fill =
  let n = Array.length a in
  if id < n then a
  else
    let b = Array.make (max (id + 1) (2 * n)) fill in
    Array.blit a 0 b 0 n;
    b

(* M6-T22 / D-0138: an instance's scope as the sorted set of its variables' ints. *)
let scope_of (inst : Propagator.instance) =
  Array.of_list
    (List.sort_uniq Int.compare (List.map Var.to_int inst.Propagator.inst_vars))

let in_scope t id v =
  id >= 0
  && id < Array.length t.scopes
  &&
  let s = t.scopes.(id) and x = Var.to_int v in
  let rec go lo hi =
    if lo >= hi then false
    else
      let mid = (lo + hi) lsr 1 in
      let y = s.(mid) in
      if y = x then true else if y < x then go (mid + 1) hi else go lo mid
  in
  go 0 (Array.length s)

(* ------------------------------------------- M6-T22: the wake index of watched literals

   D-0104 (M6-T20) gave a learned clause an advisor, two watched literals answered in
   O(1), and left the watcher table untouched: the clause's WHOLE scope stayed
   registered, so every trail entry on a variable still asked every learned clause
   naming that variable, and the clause said no unless one of its two watches was on it.
   On the codes models (D-0138: QR48, 23 367 nodes, 11 684 learned clauses of width 9 to
   16 and more) that is 439 million asks for 23 k nodes, 18 800 per node, and the asking
   -- [advises], the clause's [ask], the closure call and the cache miss on each clause
   record -- was 37 % of the cycles. A clause asked on a variable it does not watch
   always says no, so those asks decide nothing.

   An instance packed with [inst_watched] (a watched-literal advisor) is therefore
   indexed by the variables it currently WATCHES and not by its scope: [dyn_ids].
   After every run of it, whoever ran it, [sync_watched] reads the two variables back
   and moves the instance's entries. The [run] in [t.instances] is wrapped at [create] /
   [add] to do that, so no caller -- the fixpoint loop, the BAGUETTE_DEBUG re-runs, the
   consistency oracle -- can run it without the index following. A wake on [x] then asks
   exactly the instances whose advisor could say yes, the same question the full scope
   asked, so the set of instances queued is the old set (the others all answered no).

   The ORDER is kept as well: per trail entry the old walk queued the woken ids in
   ascending id order (the watcher list is newest-first and is walked by prepending),
   and [watchers_of_new_entries] merges the woken self-watching ids into the static ones
   by id. A self-watching instance never sits in [wake_static], whose lists are
   otherwise the old ones. Before its first run such an instance is in no list at all,
   which loses nothing: it was [add]ed since the last fixpoint, so [propagate] seeds it
   (rule (b)) and any wake could only have marked a slot that is dirty already.

   The watcher table [watchers] itself is unchanged -- every instance, its whole scope --
   because it is the declaration of what an instance reads, which test_engine.ml's
   wake-order oracle and the attribution argument are stated against. *)

(* ---------------------------- M11-complexity-T3 (D-0142, E1): the wake index by direction

   The index above asks a learned clause on EVERY change of a watched variable, and most
   of those changes cannot make it want a run: a watch `x >= k` is falsified only when
   [hi x] drops below [k], so a move of [lo x] can never falsify it. D-0138 section 5
   measured that half on QR48 (37.3 M wakes, 17.1 M declined) and filed it.

   So a self-watching instance reports each watch as a [Propagator.watch], which also
   says which bound move can falsify it, and the index keeps three slots per variable:
   [3x] (any change may falsify the watch), [3x + 1] (only a lower-bound move), [3x + 2]
   (only an upper-bound move). An entry on [x] asks slot [3x] always, [3x + 1] when IT OR
   A NEWER ENTRY OF THE SAME WALK moved [x]'s lower bound, and [3x + 2] likewise for the
   upper bound ([t.moved]). The seed asks by the entry's own moves.

   Why this wakes the same instances in the same order, apart from runs that do nothing.
   The ask is a function of the store, not of the entry: it answers yes iff a watch of the
   instance on [x] is false NOW, so every entry on [x] of one walk gets the same answers,
   and the old walk placed an instance at its FIRST occurrence, the OLDEST entry on [x]
   whose trigger kind it wants (the woken lists are oldest-entry-first, and a later
   occurrence is a no-op of [enqueue]/[mark_dirty]). Take an instance whose watch on [x]
   is false now, say `x >= k`. Either an entry of this walk moved [hi x] below [k], and
   then every entry on [x] at or before it in age asks the upper slot, the oldest one
   included, so the instance is placed where it was; or [hi x] was below [k] before the
   walk. Then it was false when the instance last ran: had it been falsified since, the
   walk or seed that saw that entry asked the upper slot, and the instance has run since
   or is still queued, where a second wake changes nothing. A run that leaves a false
   watch is a conflict (which ends the call and is backtracked over, both watches being
   falsified at the conflict's level) or a unit propagation, after which the clause is
   SATISFIED by its one non-false literal; so the clause is satisfied, every literal but
   the true one is false, and the run the old walk gave it changes nothing: [Pb.pass] finds no open term,
   and [rewatch] keeps the true literal and picks the latest-falsified other literal again,
   which is the same one because no falsification position has moved. That run, and the
   asks that answer no, are what goes: WORK counters (wakes, advised, props), never the
   trail. The seed only marks, so its order never mattered, and the same two cases cover
   which slots it marks. The woken ids are merged by id as before ([sort_uniq], because one
   instance can now sit in two slots of one variable).

   Under BAGUETTE_DEBUG the instances of the slots an entry does not ask are recorded as
   declined asks ([record_unasked]), so [check_declined] runs each one nothing else woke,
   as it did when they were asked: the satisfied clauses above pass it, and a watch whose
   direction was wrong would not. *)

let ensure_var t x =
  let n = Array.length t.wake_static in
  if x >= n then (
    let m = max (x + 1) (2 * n) in
    let ws = Array.make m [] in
    Array.blit t.wake_static 0 ws 0 n;
    t.wake_static <- ws;
    let mv = Bytes.make m '\000' in
    Bytes.blit t.moved 0 mv 0 n;
    t.moved <- mv;
    let di = Array.make (3 * m) [||] in
    Array.blit t.dyn_ids 0 di 0 (3 * n);
    t.dyn_ids <- di;
    let dl = Array.make (3 * m) 0 in
    Array.blit t.dyn_len 0 dl 0 (3 * n);
    t.dyn_len <- dl)

let dyn_push t x id =
  ensure_var t (x / 3);
  let len = t.dyn_len.(x) in
  let a = t.dyn_ids.(x) in
  let a =
    if len < Array.length a then a
    else
      let b = Array.make (max 4 (2 * len)) 0 in
      Array.blit a 0 b 0 len;
      t.dyn_ids.(x) <- b;
      b
  in
  a.(len) <- id;
  t.dyn_len.(x) <- len + 1;
  len

(* Swap-remove the entry at [i] of slot [x]'s slice: the order inside one slice carries
   nothing, the wake loop sorts what it wakes. The entry moved into [i] has its position
   updated; it belongs to an instance whose [wv1]/[wv2] are current. With both its
   watches on [x] it has ONE entry and both positions name it, so both are updated
   (D-0142 section 1: updating [wp1] alone left [wp2] stale, which only the
   BAGUETTE_DEBUG position check reads, and which it then reported as a lost entry). *)
let dyn_remove t x i =
  let len = t.dyn_len.(x) in
  let a = t.dyn_ids.(x) in
  let moved = a.(len - 1) in
  a.(i) <- moved;
  t.dyn_len.(x) <- len - 1;
  if i < len - 1 then (
    if t.wv1.(moved) = x then t.wp1.(moved) <- i;
    if t.wv2.(moved) = x then t.wp2.(moved) <- i)

(* Under BAGUETTE_DEBUG, after every run of a self-watching instance: the advisor must
   answer [false] for every variable of its scope it does not watch, which is the whole
   of what [inst_watched] claims and the whole of why [dyn_ids] may leave it out of
   those variables' wakes. *)
exception Bad_watch of string

let check_watched t (inst : Propagator.instance) store k1 k2 =
  let id = inst.Propagator.id in
  let a1 = k1 / 3 and a2 = k2 / 3 in
  if id >= 0 && id < Array.length t.scopes then
    Array.iter
      (fun x ->
        if x <> a1 && x <> a2 && inst.Propagator.inst_advise store (Var.of_int x) then
          raise
            (Bad_watch
               (Printf.sprintf
                  "M6-T22: propagator #%d %s reports watching variables %d and %d, but \
                   its advisor wants a wake on variable %d. [inst_watched] claims the \
                   advisor answers false off the watched variables, and Engine.dyn_ids \
                   relies on it."
                  id inst.Propagator.inst_name a1 a2 x)))
      t.scopes.(id)

let sync_watched t (inst : Propagator.instance) store
    (w : unit -> Propagator.watch * Propagator.watch) =
  let id = inst.Propagator.id in
  let a1, a2 = w () in
  let o1 = t.wv1.(id) and o2 = t.wv2.(id) in
  if a1 <> o1 || a2 <> o2 then (
    let p1 = t.wp1.(id) and p2 = t.wp2.(id) in
    let gone x = x >= 0 && x <> a1 && x <> a2 in
    if gone o1 then dyn_remove t o1 p1;
    if o2 <> o1 && gone o2 then dyn_remove t o2 p2;
    (* A kept slot keeps its entry, wherever its old position recorded it. *)
    let fresh x = x <> o1 && x <> o2 in
    let pos_of x = if fresh x then dyn_push t x id else if x = o1 then p1 else p2 in
    let q1 = pos_of a1 in
    let q2 = if a2 = a1 then q1 else pos_of a2 in
    t.wv1.(id) <- a1;
    t.wv2.(id) <- a2;
    t.wp1.(id) <- q1;
    t.wp2.(id) <- q2);
  if Debug.enabled then (
    check_watched t inst store a1 a2;
    let at x p = p >= 0 && p < t.dyn_len.(x) && t.dyn_ids.(x).(p) = id in
    if not (at a1 t.wp1.(id) && at a2 t.wp2.(id)) then
      raise
        (Bad_watch
           (Printf.sprintf "M6-T22: the wake index lost propagator #%d %s's watch entries"
              id inst.Propagator.inst_name)))

(* The instance as [t.instances] holds it: a self-watching one with its [run] wrapped so
   the index follows every run of it. *)
let indexed t (inst : Propagator.instance) =
  match inst.Propagator.inst_watched with
  | None -> inst
  | Some w ->
      let run = inst.Propagator.run in
      {
        inst with
        Propagator.run =
          (fun store ->
            let r = run store in
            sync_watched t inst store w;
            r);
      }

(* Register a NON-self-watching instance in [wake_static], once per distinct variable,
   prepending as [watchers] does. *)
let index_static t (inst : Propagator.instance) =
  if Option.is_none inst.Propagator.inst_watched then
    List.iter
      (fun x ->
        ensure_var t x;
        t.wake_static.(x) <- inst.Propagator.id :: t.wake_static.(x))
      (List.sort_uniq Int.compare (List.map Var.to_int inst.Propagator.inst_vars))

(* M2-T6: THE SELF-WAKE VETO, and the aliased-scope rule that guards it.

   Before this, a propagator that pruned was re-queued by its own prunings -- every
   watcher of a variable it moved, itself included -- so every effectful run of an
   idempotent propagator was followed by one that could not possibly do anything. GCS
   does not re-wake a propagator from its own changes when it has claimed idempotence,
   and that is the first of its two guards this copies.

   A claim ([Propagator.inst_idempotent]) is HONOURED only when the instance's scope
   names no variable twice. That is GCS's second guard -- it downgrades claims from
   aliased scopes at install time -- and it is not decoration: an idempotence argument
   is an argument over distinct variables ([linear.ml]'s is: "tightening hi(x_i) never
   moves lo(x_i)"), and once one variable stands in two places, moving it through one
   occurrence changes what the other occurrence reads. Then the very run the veto would
   skip is the one with something left to say. [inst_vars] is the scope as the instance
   reports it; a duplicate there is the alias. [Compile] merges duplicate linear terms,
   so a compiled model reaches this only through a family that keeps them, but the rule
   is checked here, per instance, and not assumed of the front end.

   A claim that is honoured but WRONG loses pruning silently -- the answer can still be
   right and the proof still verifies, since every line written was derived correctly --
   so it ships with [check_claim] below, in the same commit, under BAGUETTE_DEBUG. *)
let has_alias (vars : Var.t list) =
  let sorted = List.sort Var.compare vars in
  let rec dup = function
    | a :: (b :: _ as rest) -> Var.compare a b = 0 || dup rest
    | _ -> false
  in
  dup sorted

let honours_claim (inst : Propagator.instance) =
  inst.Propagator.inst_idempotent && not (has_alias inst.Propagator.inst_vars)

let create ?(trigger = default_trigger) (instances : Propagator.instance list) : t =
  let watchers = Hashtbl.create 64 in
  (* M11-complexity-T3 (D-0142, D-0143's request): whether [id] is already in [v]'s list
     was a [List.mem] over the list, which made building the engine quadratic in a
     variable's degree (smelt_2: variables in about 2 000 constraints). Ids are distinct
     ([t.instances] is indexed by them, instance [i] at slot [i]), so [id] can only be in
     [v]'s list if THIS instance put it there, for an earlier occurrence of [v] in its own
     scope, and then it is the head, nothing having been prepended since. So the head is
     the whole test: the same lists in the same order, in O(1) and without the table of
     pairs a first version kept, which cost smelt_2 50 MB of peak memory. *)
  List.iter
    (fun (inst : Propagator.instance) ->
      let id = inst.Propagator.id in
      List.iter
        (fun v ->
          let cur = try Hashtbl.find watchers v with Not_found -> [] in
          match cur with
          | first :: _ when first = id -> ()
          | _ -> Hashtbl.replace watchers v (id :: cur))
        inst.Propagator.inst_vars)
    instances;
  let max_id =
    List.fold_left
      (fun m (i : Propagator.instance) -> max m i.Propagator.id)
      (-1) instances
  in
  let triggers = Array.make (max (List.length instances) (max_id + 1)) wake_on_any in
  List.iter
    (fun (inst : Propagator.instance) ->
      if inst.Propagator.id >= 0 then triggers.(inst.Propagator.id) <- trigger inst)
    instances;
  let veto = Array.make (Array.length triggers) false in
  List.iter
    (fun (inst : Propagator.instance) ->
      if inst.Propagator.id >= 0 then veto.(inst.Propagator.id) <- honours_claim inst)
    instances;
  let scopes = Array.make (Array.length triggers) [||] in
  List.iter
    (fun (inst : Propagator.instance) ->
      if inst.Propagator.id >= 0 then scopes.(inst.Propagator.id) <- scope_of inst)
    instances;
  let t =
    {
      instances = Array.of_list instances;
      count = List.length instances;
      watchers;
      triggers;
      ctr = counters_create ();
      runs_by_id = Array.make (Array.length triggers) 0;
      eff_by_id = Array.make (Array.length triggers) 0;
      veto;
      born = Array.make (Array.length triggers) unborn;
      epoch = 0;
      fixpoints = [];
      seen = None;
      incremental = true;
      poll_left = default_poll_runs;
      scopes;
      wake_static = [||];
      moved = Bytes.empty;
      dyn_ids = [||];
      dyn_len = [||];
      wv1 = Array.make (Array.length triggers) (-1);
      wv2 = Array.make (Array.length triggers) (-1);
      wp1 = Array.make (Array.length triggers) (-1);
      wp2 = Array.make (Array.length triggers) (-1);
      births = [];
      newborns = List.rev_map (fun (i : Propagator.instance) -> i.Propagator.id) instances;
      heap = Array.make (Array.length triggers) 0;
      heap_len = 0;
      dirty = Array.make (Array.length triggers) false;
      in_queue = Array.make (Array.length triggers) false;
      declined = [];
    }
  in
  (* M6-T22: the wake index, in [instances] order -- the order [watchers] was built in. *)
  Array.iteri
    (fun i inst ->
      index_static t inst;
      t.instances.(i) <- indexed t inst)
    t.instances;
  t

let set_incremental t b = t.incremental <- b
let n_instances t = t.count

(* M6-T22: the instances, in id order, without the [vacant] tail. *)
let iter_instances t f =
  for i = 0 to t.count - 1 do
    f t.instances.(i)
  done

let counters t = t.ctr

(* M6-T20. [name, instances, runs, effectful runs] per propagator family, most runs
   first; ties by name so the table is deterministic. *)
let family_table t =
  let tbl = Hashtbl.create 16 in
  iter_instances t (fun (inst : Propagator.instance) ->
      let id = inst.Propagator.id in
      let r = if id < Array.length t.runs_by_id then t.runs_by_id.(id) else 0 in
      let e = if id < Array.length t.eff_by_id then t.eff_by_id.(id) else 0 in
      let n, r0, e0 =
        try Hashtbl.find tbl inst.Propagator.inst_name with Not_found -> (0, 0, 0)
      in
      Hashtbl.replace tbl inst.Propagator.inst_name (n + 1, r0 + r, e0 + e));
  let rows = Hashtbl.fold (fun name (n, r, e) acc -> (name, n, r, e) :: acc) tbl [] in
  List.sort
    (fun (na, _, ra, _) (nb, _, rb, _) ->
      if ra <> rb then compare rb ra else compare na nb)
    rows

let bump_by_id t id ~eff =
  let n = Array.length t.runs_by_id in
  if id >= n then (
    let m = max (id + 1) (2 * n) in
    let grow a = Array.append a (Array.make (m - n) 0) in
    t.runs_by_id <- grow t.runs_by_id;
    t.eff_by_id <- grow t.eff_by_id);
  t.runs_by_id.(id) <- t.runs_by_id.(id) + 1;
  if eff then t.eff_by_id.(id) <- t.eff_by_id.(id) + 1

(* Whether instance [id]'s idempotence claim is honoured by this engine. *)
let vetoes_self t id = id >= 0 && id < Array.length t.veto && t.veto.(id)

(* ------------------------------------------------- registering a LEARNED constraint *)

(* The id the next [add] will demand, which is also the id [Propagator.pack] must be
   given. Exposed rather than left to the caller to compute from [n_instances], because
   the two are the same number only because [add] keeps them so, and a caller that
   derived it for itself would silently stop agreeing the day that stops being true. *)
let next_id t = t.count

(* Register one more propagator instance, AFTER [create] -- M2-L1's half of "instantiate
   a learned constraint as a Linear instance registered with the engine".

   Three things this has to get right, each of which is an existing invariant of this
   file rather than a new rule:

   1. [propagate] indexes [t.instances] BY ID ([t.instances.(id)]) and bounds its queue
      by [n_instances], so an instance's id must equal its position. [create] gets that
      by construction from a list built in order; here it is checked, loudly, because a
      learned instance's id comes from a caller and a wrong one would silently make
      [propagate] run the wrong propagator -- which is a wrong pruning attributed to the
      right constraint, the exact shape I-T4 exists to catch.
   2. The watcher table is the ONLY thing that tells [check_attribution] an instance is
      allowed to prune a variable (its second arm). A learned row over variables this
      engine has never seen is therefore registered against those variables here, or its
      every pruning is a mis-attribution.
   3. [triggers] is indexed by id too and is sized at [create]; it grows here. The
      default for an id with no entry is [wake_on_any], so a short array is never
      *unsound* -- it just wakes more than it must -- but it would make a learned
      instance's trigger unreachable, which is a silent loss of the M2-T5 mask.

   Appending copied every id-indexed array, O(n) per learned constraint, on the argument
   that learning is bounded by conflicts. D-0138 measured what that costs when there is a
   conflict at every other node and n is the learned database: six arrays of n words in
   the major heap per conflict, and the marking they feed. Since M6-T22 the arrays grow by
   doubling and [count] says which instances exist. *)
let add ?(trigger = default_trigger) (t : t) (inst : Propagator.instance) =
  let expected = next_id t in
  if inst.Propagator.id <> expected then
    invalid_arg
      (Printf.sprintf
         "Engine.add: instance %s was packed with id #%d, but this engine's next id \
          is           #%d. Engine.propagate indexes its instance array BY ID, so the \
          two must           agree; pack with Engine.next_id."
         inst.Propagator.inst_name inst.Propagator.id expected);
  let id = inst.Propagator.id in
  t.instances <- room t.instances id vacant;
  t.count <- id + 1;
  t.wv1 <- room t.wv1 id (-1);
  t.wv2 <- room t.wv2 id (-1);
  t.wp1 <- room t.wp1 id (-1);
  t.wp2 <- room t.wp2 id (-1);
  t.dirty <- room t.dirty id false;
  t.in_queue <- room t.in_queue id false;
  index_static t inst;
  t.instances.(id) <- indexed t inst;
  let scope = scope_of inst in
  (* The instance is new, so it is in no watcher list yet: one prepend per DISTINCT
     variable is the old [List.mem]-guarded loop's result, without walking the list --
     which on a learned database is every learned clause naming the variable. *)
  Array.iter
    (fun x ->
      let v = Var.of_int x in
      let cur = try Hashtbl.find t.watchers v with Not_found -> [] in
      Hashtbl.replace t.watchers v (id :: cur))
    scope;
  t.triggers <- room t.triggers id wake_on_any;
  t.triggers.(id) <- trigger inst;
  t.veto <- room t.veto id false;
  t.veto.(id) <- honours_claim inst;
  t.scopes <- room t.scopes id [||];
  t.scopes.(id) <- scope;
  (* M6-T18: a new instance has never run, so it is at its fixpoint at no state: it is
     seeded by the next [propagate] whatever else changed, and after any later backjump
     to a fixpoint older than the one it is born at. *)
  t.born <- room t.born id unborn;
  t.born.(id) <- unborn;
  t.newborns <- id :: t.newborns;
  t.heap <- room t.heap id 0

(* The variables an instance watches, or [None] if this engine has no such instance.

   The shape [Analysis.analyse] wants (M2-L2), and it is here rather than reconstructed
   by the caller because [t.instances] is indexed by id and only [add] keeps it so. A
   caller that built this from its own list of instances would stop agreeing with the
   engine the moment a learned constraint was registered. *)
let vars_of t id =
  if id >= 0 && id < t.count then Some t.instances.(id).Propagator.inst_vars else None

(* M2-L6: the PB row instance [id] is, or [None] when it does not expose one. The same
   shape as [vars_of] and for the same reason -- lib/core/pb_analysis.ml is shown the
   engine through two narrow functions rather than being handed the instance array. *)
let row_of t store id =
  if id >= 0 && id < t.count then t.instances.(id).Propagator.inst_row store else None

(* The builtin name instance [id] was packed under, for a diagnostic that has to say
   WHICH propagator family declined to expose a row. "<unknown>" rather than a raise: a
   fallback reason nobody can read is a counter with no diagnosis behind it, but it is
   still only a message. *)
let name_of t id =
  if id >= 0 && id < t.count then t.instances.(id).Propagator.inst_name else "<unknown>"

let trigger_of t id =
  if id >= 0 && id < Array.length t.triggers then t.triggers.(id) else wake_on_any

(* Every newly-touched variable's watchers, for the trail entries pushed since
   [since] -- the positions [since .. trail_length - 1].

   This walks the trail by index ([Store.trail_entry] is O(1) and says so in its own
   comment). It used to call [Store.trail_entries], which materialises the *whole*
   trail as a fresh most-recent-first list and then kept only its first
   [trail_length - since] elements: O(|trail|) allocation on every propagator call in
   the fixpoint loop, to look at the handful of entries that call had just pushed.
   The module header above already claimed "O(new entries) per propagator call"; that
   is now true of the code as well as of the comment. M1-T24.

   The walk runs *downwards*, newest position first, and that is not cosmetic. The
   old code iterated a newest-first list prepending each entry's watchers with
   [List.rev_append], so the returned list came out oldest-entry-first with each
   entry's watcher list reversed, and [propagate] enqueues in exactly that order.
   Counting down from [trail_length - 1] to [since] performs the identical sequence
   of [rev_append]s on the identical entries, so the wake order -- and hence the
   propagation order, the search tree and the emitted proof -- is unchanged, not
   merely equal as a set. An upward walk would reverse it.

   M2-T5: each entry is now classified ([Domain.classify] off the [old]/[now] the entry
   already carries -- no new field on [Store.entry]) and a watcher whose trigger does not
   want that kind is dropped. Two things about that, both load-bearing:

   - Order is preserved exactly. [List.iter (fun id -> acc := id :: !acc) ids] is
     [List.rev_append ids] written out, and filtering inside it yields a SUBSEQUENCE of
     what the unfiltered walk returns -- never a permutation of it. So the wake order
     this file's own test ([test_engine.ml], "wake order") pins is still the order, with
     masked ids removed and nothing reordered.
   - Classification is per ENTRY, not per variable: one entry is one [Domain] operation,
     so its change is a [Bound] or a [Holes] but never both, and a watcher that wants
     bounds only cannot lose a bound move that happened to be bundled with a hole. *)
(* M6-T20 / D-0104. The advisor's answer for instance [id] on a change of [v], or [true]
   for an id this engine does not know (the safe answer, as for the trigger). Under
   BAGUETTE_DEBUG a [false] is CHECKED: the instance is run and must prune nothing and
   not fail, which is I-P7 read literally -- once the walk is over and only if nothing
   else woke it ([check_declined], D-0142 section 1). *)
exception Not_at_fixpoint of string

let check_advise (inst : Propagator.instance) (store : Store.t) v =
  let before = Store.trail_length store in
  let fail what =
    raise
      (Not_at_fixpoint
         (Printf.sprintf
            "I-P7: propagator #%d %s declined the wake for a change of %s, but a run %s"
            inst.Propagator.id inst.Propagator.inst_name (Store.name store v) what))
  in
  match inst.Propagator.run store with
  | Propagator.Conflict _ -> fail "FAILED"
  | Propagator.Fixpoint ->
      if Store.trail_length store > before then
        fail (Printf.sprintf "pruned %d entr(y/ies)" (Store.trail_length store - before))

let advises t store id v =
  if id < 0 || id >= t.count then true
  else
    let inst = t.instances.(id) in
    if inst.Propagator.inst_advise store v then true
    else (
      t.ctr.c_advised <- t.ctr.c_advised + 1;
      if Debug.enabled then t.declined <- (id, v) :: t.declined;
      false)

(* M11-complexity-T3 (D-0142 section 1): the I-P7 check of the declined asks, made once
   the walk that asked them is over and its wakes are in, and only for an instance that
   is NOT PENDING.

   I-P7 lets an advisor decline a change only "if, every change since this instance's
   last run on a variable it names having been answered [false], a run now would change
   nothing". That premise is false for an instance that some OTHER change since its last
   run woke and that has not run yet: it is in the queue (or a dirty seed slot), and a
   run of it now may well prune -- the run it is queued for. Until this record the check
   ran on the spot, at the declined ask, and so it ran such instances early and called
   their pending run a lost wake. On an integer variable that is ordinary: a learned
   clause is woken because its second watch was falsified (an entry on [y]), and before
   it runs, a change of its first watch's variable [x] that leaves that watch open is
   declined -- correctly, the clause is already queued -- and the check, run there, sees
   the unit propagation the queue is about to make. A Boolean change cannot do that: it
   fixes the variable, so the watch it touches is decided, true (the clause is satisfied
   and a run does nothing) or false (the ask says yes). That is why the alarm was on the
   integer instances only (D-0142 section 1 has the trace on 2013 rcpsp_12).

   So the check now waits for the end of the walk ([watchers_of_new_entries], after the
   caller's wakes) or of the seed ([seed_dirty] and the newborn marks), and skips every
   instance that is dirty or queued. For the rest, the premise holds -- every change of
   that walk was declined for it, and any earlier one was declined or was run since --
   and a run must change nothing, exactly as before. Each instance is checked once per
   walk, at the variable of its first declined ask. This is the whole change: without
   BAGUETTE_DEBUG [declined] stays empty and nothing here runs. *)
let check_declined t store =
  if t.declined <> [] then (
    let ds = List.rev t.declined in
    t.declined <- [];
    let seen = ref [] in
    List.iter
      (fun (id, v) ->
        if not (List.mem id !seen) then (
          seen := id :: !seen;
          if not (t.dirty.(id) || t.in_queue.(id)) then
            check_advise t.instances.(id) store v))
      ds)

(* E1 (D-0142): did this entry move [x]'s lower bound, its upper bound? A hole entry
   moves neither, a fixing entry on a wide domain can move both. *)
let lo_moved (e : Store.entry) = Domain.lo e.now <> Domain.lo e.old
let hi_moved (e : Store.entry) = Domain.hi e.now <> Domain.hi e.old

(* E1 (D-0142), under BAGUETTE_DEBUG only: the instances of the directional slots of
   [e.var] that this entry does NOT ask ([lo]/[hi] false) are recorded as declined asks, so that
   [check_declined] treats them exactly as it treated them when every watcher of the
   variable was asked: an instance that nothing else woke is run and must prune nothing.
   That is the claim the direction index rests on, checked the way I-P7 is. [self] is a
   vetoed self-wake (never asked, not recorded); [skip] an instance the seed marks
   whatever its advisor says. The trigger mask is applied as the ask would apply it. *)
let record_unasked ?(skip = fun _ -> false) t (e : Store.entry) ~lo ~hi ~self =
  let x = Var.to_int e.Store.var in
  let change = lazy (Domain.classify ~old:e.Store.old ~now:e.Store.now) in
  let record sl =
    for j = 0 to t.dyn_len.(sl) - 1 do
      let id = t.dyn_ids.(sl).(j) in
      if id <> self && (not (skip id)) && wakes_on (trigger_of t id) (Lazy.force change)
      then t.declined <- (id, e.Store.var) :: t.declined
    done
  in
  if not lo then record ((3 * x) + 1);
  if not hi then record ((3 * x) + 2)

let watchers_of_new_entries ?self t store ~since =
  (* M2-T6: [self] is the instance that pushed these entries. When its claim is
     honoured, its own id is dropped from every entry's watcher list -- a subsequence
     again, never a reordering, for the reason the bullet above gives for the mask. *)
  let vetoed = match self with Some id -> vetoes_self t id | None -> false in
  let self_id = match self with Some id -> id | None -> -1 in
  let acc = ref [] in
  (* D-0142 section 1: what this walk declines is checked after it, by its caller. *)
  if Debug.enabled then t.declined <- [];
  let wants id change v =
    if vetoed && id = self_id then (
      t.ctr.c_vetoed <- t.ctr.c_vetoed + 1;
      false)
    else if wakes_on (trigger_of t id) change then (
      incr wakes;
      t.ctr.c_wakes <- t.ctr.c_wakes + 1;
      advises t store id v)
    else (
      incr masked_wakes;
      t.ctr.c_masked <- t.ctr.c_masked + 1;
      false)
  in
  (* M6-T22: the self-watching instances of one slot that want this entry, onto [dl].
     A copy of the slice under BAGUETTE_DEBUG, as before D-0142 moved the I-P7 check
     after the walk: nothing in the walk resyncs a slice now, and the copy costs nothing
     that counts. *)
  let dl = ref [] in
  let collect change v sl =
    let nd = t.dyn_len.(sl) in
    if nd > 0 then
      let ids = if Debug.enabled then Array.sub t.dyn_ids.(sl) 0 nd else t.dyn_ids.(sl) in
      for j = 0 to nd - 1 do
        let id = ids.(j) in
        if wants id change v then dl := id :: !dl
      done
  in
  for i = Store.trail_length store - 1 downto since do
    let e : Store.entry = Store.trail_entry store i in
    let x = Var.to_int e.var in
    if x < Array.length t.wake_static then (
      let stat = t.wake_static.(x) in
      (* E1 (D-0142): the slots this entry asks are those of the bound moves of this
         entry AND of every newer entry of this walk on [x] -- see "The wake index by
         direction", and [t.moved]. *)
      let m =
        Char.code (Bytes.unsafe_get t.moved x)
        lor (if lo_moved e then 1 else 0)
        lor if hi_moved e then 2 else 0
      in
      Bytes.unsafe_set t.moved x (Char.unsafe_chr m);
      let sl = 3 * x and lo = m land 1 <> 0 and hi = m land 2 <> 0 in
      let nd =
        t.dyn_len.(sl)
        + (if lo then t.dyn_len.(sl + 1) else 0)
        + if hi then t.dyn_len.(sl + 2) else 0
      in
      if Debug.enabled then
        record_unasked t e ~lo ~hi ~self:(if vetoed then self_id else -1);
      if stat <> [] || nd > 0 then (
        let change = Domain.classify ~old:e.old ~now:e.now in
        (* M6-T22: the self-watching instances that want this entry, DESCENDING, to
           be merged into the static ones by id (see the wake index's header). One
           instance can sit in two of the slots asked (two watches on [x]), hence the
           [sort_uniq]; with one slot per variable there was nothing to remove and it
           is the [sort] it replaces. *)
        dl := [];
        if nd > 0 then (
          collect change e.var sl;
          if lo then collect change e.var (sl + 1);
          if hi then collect change e.var (sl + 2);
          match !dl with
          | _ :: _ :: _ -> dl := List.sort_uniq (fun a b -> Int.compare b a) !dl
          | _ -> ());
        let rec flush_above s =
          match !dl with
          | d :: rest when d > s ->
              acc := d :: !acc;
              dl := rest;
              flush_above s
          | _ -> ()
        in
        List.iter
          (fun id ->
            flush_above id;
            if wants id change e.var then acc := id :: !acc)
          stat;
        flush_above min_int))
  done;
  (* [t.moved] back to all zero, over the same entries. *)
  for i = since to Store.trail_length store - 1 do
    let x = Var.to_int (Store.trail_entry store i).Store.var in
    if x < Bytes.length t.moved then Bytes.unsafe_set t.moved x '\000'
  done;
  !acc

(* --------------------------------------------- attribution, checked by reading it back *)

exception Mis_attributed of string

(* M2-T7's answer to "an id that is threaded but never read changes no behaviour at all".

   After each [run], every trail entry that run pushed must be credited to the instance
   that just ran, and that instance must be one that watches the variable the entry
   changed. The second half is the one with teeth: the first catches a stamp that was
   never written, the second catches a stamp that was written with a plausible but wrong
   id -- which is exactly the failure mode M2-T3 would turn into a wrong learned clause,
   and exactly the kind of thing this codebase has repeatedly shipped green (M1-T45's
   [if true || ...], M1-T50's deliberately wrong decision literal).

   It is ON BY DEFAULT, not behind BAGUETTE_DEBUG, and that is deliberate. A Debug-gated
   check of a field nobody else reads is indistinguishable from no check at all in every
   run the suite actually makes. The cost is one binary search in the instance's sorted
   scope per NEW TRAIL ENTRY, bounded by the number of prunings, not by the trail or the
   variable count.

   Until M6-T22 the watcher table was consulted ("the short [List.mem]"), on the argument
   that it is indexed by variable. The list it returns is short only while the watchers
   of one variable are few: with a learned database it is every learned clause naming
   the variable, and D-0138 measured that walk at 15 % of a QR48 solve. [t.scopes] is
   built from the same [inst_vars] at the same two places ([create], [add]), so the
   answer is the table's. *)
let check_attribution (t : t) (inst : Propagator.instance) store ~since
    ~(conflict : Store.conflict option) =
  let id = inst.Propagator.id in
  (* M6-T22 / D-0138: membership in the instance's own sorted scope, which is the
     watcher table's answer by construction (both are built from [inst_vars], at [create]
     and at [add]). It used to be [List.mem id] over the watcher list of [e.var], and on
     a learned database that list is every learned clause naming the variable, newest
     first, with the model propagators that actually prune at its far end: on QR48 that
     walk, under OCaml's polymorphic [compare], was 15 % of the solve's cycles. *)
  let watches v = in_scope t id v in
  for i = since to Store.trail_length store - 1 do
    let e : Store.entry = Store.trail_entry store i in
    if e.Store.prop <> id then
      raise
        (Mis_attributed
           (Printf.sprintf
              "M2-T7: propagator #%d %s pruned %s, but the trail credits that change \
               to                #%d. A trail entry must name the instance that made it; \
               conflict analysis                (M2-T3) resolves an entry's reason \
               constraint through this field, so a                wrong id here is a \
               wrong learned clause. Check that Engine.propagate                brackets \
               the run with Store.with_running and that Store.apply \
               stamps                t.current_prop."
              id inst.Propagator.inst_name
              (Store.name store e.Store.var)
              e.Store.prop))
    else if not (watches e.Store.var) then
      raise
        (Mis_attributed
           (Printf.sprintf
              "M2-T7: the trail credits the change to %s to propagator #%d %s, which \
               does                not watch %s. Either the propagator pruned a variable \
               outside its own                scope -- which breaks I-P1, since \
               soundness is stated about its own                constraint -- or the \
               attribution is wrong."
              (Store.name store e.Store.var)
              id inst.Propagator.inst_name
              (Store.name store e.Store.var)))
  done;
  match conflict with
  | None -> ()
  | Some c ->
      if c.Store.c_prop <> id then
        raise
          (Mis_attributed
             (Printf.sprintf
                "M2-T7: propagator #%d %s reported a conflict, but the conflict \
                 is                  credited to #%d. A conflict is where M2-T3's \
                 resolution STARTS, so this                  id is the first constraint \
                 of the learned clause."
                id inst.Propagator.inst_name c.Store.c_prop))

(* ------------------------------------------------- I-P2, checked by re-running *)

(* I-P2: "when [engine.propagate] returns without failure, running any propagator again
   changes nothing". Until M2-T5 that invariant had no test of any kind. It is the one
   invariant that can detect an over-aggressive trigger mask, because a starved wake
   leaves a propagator with something still to say at what the engine calls a fixpoint,
   and leaves NO other trace: the answer may still be right, the proof still verifies
   (every line that was written was written correctly), and only the node count moves.

   So this runs every instance once more and fails loudly at the first one that prunes.
   "Prunes" is measured as the trail growing, which is precisely what [Store.apply]
   records for a real change and does not record for a no-op; a [Conflict] counts too,
   since a propagator that can fail at a fixpoint could have failed before it.

   It is deliberately NOT quiet-and-recoverable. An exception, with the propagator named
   and the domain move spelled out, because the failure it reports is one nobody would
   otherwise notice. Raising also leaves the store with the extra pruning applied, which
   does not matter: the run is over.

   Cost is one extra pass over every instance per [propagate] call, so it is behind
   BAGUETTE_DEBUG (see [propagate]) and off by default. Tests call it directly instead,
   the same way test_engine.ml passes [~audit:true] rather than relying on
   BAGUETTE_PROOF_AUDIT. *)
let check_fixpoint (t : t) (store : Store.t) : unit =
  let describe (inst : Propagator.instance) what =
    Printf.sprintf
      "I-P2 violated: at what the engine reported as a fixpoint, propagator #%d %s (%s) \
       %s.\n\
       A propagator with something left to say at a fixpoint means it was never woken by \
       a change it needed. The usual cause is a trigger mask that is too aggressive -- \
       see [trigger_of_consistency] in lib/core/engine.ml, and check whether this \
       propagator reads more of a domain than its declared consistency level implies."
      inst.Propagator.id inst.Propagator.inst_name
      (Propagator.consistency_to_string inst.Propagator.inst_consistency)
      what
  in
  iter_instances t (fun (inst : Propagator.instance) ->
      let before = Store.trail_length store in
      match inst.Propagator.run store with
      | Propagator.Conflict _ ->
          raise (Not_at_fixpoint (describe inst "reported a CONFLICT"))
      | Propagator.Fixpoint ->
          if Store.trail_length store > before then
            let e : Store.entry = Store.trail_entry store before in
            raise
              (Not_at_fixpoint
                 (describe inst
                    (Printf.sprintf "pruned %s from %s to %s (%s)"
                       (Store.name store e.var) (Domain.to_string e.old)
                       (Domain.to_string e.now)
                       (Domain.change_to_string (Domain.classify ~old:e.old ~now:e.now))))))

(* M2-T6: the CLAIM RE-CHECKER, GCS's companion to the veto ("re-runs every honoured
   idempotence claim ... and aborts if it infers anything").

   Called by [propagate] under BAGUETTE_DEBUG at the exact moment a claim is relied on:
   an honoured instance has just returned [Fixpoint] having pruned, and the veto is
   about to skip the re-wake its own prunings would have caused. So run it once more,
   right now, with nothing else having moved, and require that it prunes nothing and
   does not fail. Anything else is a wrong claim, and it raises [Not_at_fixpoint] with
   the instance named -- the same exception as I-P2's re-run, because it is the same
   statement made earlier and about one propagator: "this one still had something to
   say".

   [check_fixpoint] at the end of the loop would also see most wrong claims, but not
   all of them: a later run of some other propagator can wake the claimant for an
   unrelated reason and so cover the lost pruning up, at this node, while leaving the
   order of the trail (and so the proof) depending on luck. Checking at the claim is the
   only check that cannot be covered up. A re-run that prunes nothing writes nothing to
   the trail, the reason arena or the proof, so a BAGUETTE_DEBUG run answers and proves
   byte-identically to a plain one; the re-run is not counted in [counters]. *)
let check_claim (inst : Propagator.instance) (store : Store.t) : unit =
  let before = Store.trail_length store in
  let fail what =
    raise
      (Not_at_fixpoint
         (Printf.sprintf
            "M2-T6: propagator #%d %s claims single-call idempotence, and the engine \
             skipped re-waking it off its own prunings on the strength of that claim -- \
             but run again at once, with nothing else changed, it %s. The claim is wrong \
             for this instance (see the comment above Propagator.pack, the packing site \
             and the family's own header); remove it rather than this check."
            inst.Propagator.id inst.Propagator.inst_name what))
  in
  match
    Store.with_running store inst.Propagator.id (fun () -> inst.Propagator.run store)
  with
  | Propagator.Conflict _ -> fail "reported a CONFLICT"
  | Propagator.Fixpoint ->
      if Store.trail_length store > before then
        let e : Store.entry = Store.trail_entry store before in
        fail
          (Printf.sprintf "pruned %s from %s to %s" (Store.name store e.var)
             (Domain.to_string e.old) (Domain.to_string e.now))

(* ============================================================ M2-T10: the consistency
   oracle

   docs/SPEC.md 2.2 makes the `consistency` tag normative and 3.2 spells out what a
   propagator owes; [Propagator.consistency] makes the tag a constructor rather than a
   string so a typo cannot claim a level. Until this function nothing anywhere CHECKED
   the tag. The existing oracle -- test_random.ml's brute force -- checks SOUNDNESS: that
   the answer the solver reaches agrees with enumeration of the whole declared box. A
   propagator that prunes nothing at all is perfectly sound and passes every one of those
   cases, while declaring [Domain]. That gap is what this closes.

   ---------------------------------------------------------------------------
   THE ASSERTION IS "AT LEAST", NEVER "EXACTLY"
   ---------------------------------------------------------------------------

   A propagator may be stronger than it declares. [Ne] is, and says so in its own header:
   its algorithm is domain consistent for a disequality with distinct variables, and it
   declares [Value] anyway because the level bounds what an explanation is allowed to
   CLAIM (SPEC 3.2), and a conservative claim is the safe direction. So this function
   never reports "stronger than declared". It reports only the one direction that is a
   bug: a propagator that, at a fixpoint, leaves in a domain a value its own semantics
   cannot support, while declaring a level that promised otherwise.

   ---------------------------------------------------------------------------
   WHERE THE SEMANTICS COME FROM, AND THE ONE THING THIS CANNOT SEE
   ---------------------------------------------------------------------------

   The oracle needs to know which total assignments satisfy the constraint. It does NOT
   reimplement every constraint family to find out -- a second implementation is a second
   thing to get wrong, and it would have to be extended by every session that adds a
   propagator, which is exactly the discipline that let the tag go unchecked in the first
   place. Instead it uses the propagator itself, at total assignments, where SPEC 3.2's
   *checking* obligation pins the answer exactly:

     "when all its variables are fixed, it MUST report failure iff the assignment
      violates its constraint"

   So: fix every variable of the instance's scope to a candidate tuple, run the
   propagator, and read [Conflict] as "violates" and [Fixpoint] as "satisfies". That is a
   total function of the propagator's own code, needs no table, and stays correct for a
   propagator family written after this file.

   The limitation is the exact dual, and it is stated here rather than discovered later:
   **this cannot detect a wrong checking verdict.** A propagator whose total-assignment
   answer is itself wrong is consistent with itself, and this oracle will call it
   consistent. That failure is a SOUNDNESS failure, and soundness is what test_random.ml
   and test_matrix.ml check against independent enumeration of the model text. The two
   oracles are complementary and neither subsumes the other: brute force checks that the
   propagator's semantics are right, this checks that its pruning matches its declared
   strength given those semantics.

   ---------------------------------------------------------------------------
   WHAT EACH LEVEL OWES
   ---------------------------------------------------------------------------

   [Domain]   every remaining value of every variable in scope extends to an accepted
              tuple over the OTHER variables' CURRENT DOMAINS. (docs/GLOSSARY.md,
              "Domain consistent" = generalised arc consistent.)

   [Bounds]   [lo] and [hi] of every variable in scope extend to an accepted tuple over
              the other variables' INTERVALS -- [lo..hi] with holes ignored.

              That relaxation is a reading, and it is the one docs/GLOSSARY.md's
              "saying nothing about interior values" forces. It is bounds(Z), not
              bounds(D). The difference is not cosmetic: over x,y in {0,2} with
              x + y != 1 removed... concretely, `x + y = 1` with x,y in {0,2} has no
              bounds(Z) pruning to make (x = 0 wants y = 1, and 1 IS in [0,2]) while
              bounds(D) would empty both domains. [Linear], [Int_le], [Int_lt], [Pb]
              and [Bool2int] all declare [Bounds] and all are bounds(Z); asserting
              bounds(D) against them would report five findings that are not bugs.
              SPEC 3.2 does not currently distinguish the two -- REPORTED, not decided
              here (M2-T10).

   [Value]    nothing. docs/GLOSSARY.md: "only ever removes values it can name, without
              claiming anything about the values it leaves behind". A level that claims
              nothing about what remains has no support obligation, and inventing one
              for it would be this harness weakening a declaration into something it
              does not say. What [Value] owes is soundness, and test_random.ml owns that.

   [Checking] nothing, for the reason two sections up: the checking verdict is this
              oracle's own axiom.

   [Domain] implies bounds(Z) -- support over a subset implies support over the superset
   -- so a [Domain] instance is checked at [Domain] only.

   ---------------------------------------------------------------------------
   COST, AND WHY IT IS GATED SEPARATELY
   ---------------------------------------------------------------------------

   Per support search the work is a product of domain sizes, and it runs per variable,
   per value, per instance, per search node. It is brute force by construction and it is
   exactly the shape that reaches this machine's shared 15 GB ceiling. So:

     - it is behind BAGUETTE_CONSISTENCY, its own switch, not BAGUETTE_DEBUG
       (lib/core/debug.ml says why the two are separate),
     - every support search is bounded by [Debug.consistency_cap] tuples, and an
       instance whose scope exceeds it is SKIPPED and COUNTED in [oracle_skipped]. A
       skip is not a pass. A run that reports violations 0 and skips 300 has checked
       nothing and the counters say so out loud,
     - the scratch stores it builds are thrown away per tuple and never touch the live
       store, its trail, its reason arena or the proof. The oracle cannot perturb the
       search it is auditing, which also means a BAGUETTE_CONSISTENCY run answers the
       same and emits the same proof as one without it. *)

type violation = {
  vi_id : int;
  vi_name : string;
  vi_declared : Propagator.consistency;
  vi_level : string;  (** the obligation that failed: "domain" or "bounds" *)
  vi_var : Var.t;
  vi_var_name : string;
  vi_value : int;
  vi_scene : string;  (** the scope's domains as they stood, so the case is reproducible *)
}

let violation_to_string (v : violation) =
  Printf.sprintf
    "M2-T10: propagator #%d %s declares %s but is WEAKER than that: %s = %d survives at \
     the fixpoint with no support.\n\
    \  scene: %s\n\
    \  no assignment of the other variables in scope, over %s, satisfies the constraint \
     with %s = %d, so a %s-consistent propagator would have removed it."
    v.vi_id v.vi_name
    (Propagator.consistency_to_string v.vi_declared)
    v.vi_var_name v.vi_value v.vi_scene
    (if String.equal v.vi_level "bounds" then "their intervals" else "their domains")
    v.vi_var_name v.vi_value v.vi_level

exception Weaker_than_declared of violation

(* Without this the escaping exception prints as [Weaker_than_declared(_)] and every word
   of the message above is lost -- which is the whole value of it, since the reader is
   looking at a crash from a search they cannot replay. Registering the printer is how a
   payload-carrying exception stays legible when it reaches the top level. *)
let () =
  Printexc.register_printer (function
    | Weaker_than_declared v -> Some (violation_to_string v)
    | _ -> None)

(* Counters, so a run can say how much it actually audited. [reset_oracle_stats] is for
   tests that measure one scene; [propagate] never resets. *)
let oracle_nodes = ref 0
let oracle_checks = ref 0
let oracle_tuples = ref 0
let oracle_skipped = ref 0

(* Per propagator FAMILY, because the totals alone cannot tell "every declared level was
   met" from "no propagator carrying an obligation was ever reached". test_random.ml's
   header makes this point at length and it applies here with more force: the oracle is
   silent by construction on [Value] and [Checking], so a suite whose propagators were all
   [Value] would report a clean audit over zero checks. The two tables below are what let
   a reader tell the two apart -- one counts instances actually enumerated, the other
   counts instances passed over BECAUSE THEIR LEVEL OWES NOTHING, by name and by level. *)
let oracle_checked : (string, int) Hashtbl.t = Hashtbl.create 16
let oracle_unobliged : (string, int) Hashtbl.t = Hashtbl.create 16

let bump tbl key =
  Hashtbl.replace tbl key (1 + Option.value ~default:0 (Hashtbl.find_opt tbl key))

let histogram tbl = List.sort compare (Hashtbl.fold (fun k n acc -> (k, n) :: acc) tbl [])

let reset_oracle_stats () =
  oracle_nodes := 0;
  oracle_checks := 0;
  oracle_tuples := 0;
  oracle_skipped := 0;
  Hashtbl.reset oracle_checked;
  Hashtbl.reset oracle_unobliged

let oracle_stats () = (!oracle_nodes, !oracle_checks, !oracle_tuples, !oracle_skipped)
let oracle_checked_families () = histogram oracle_checked
let oracle_unobliged_families () = histogram oracle_unobliged

(* The candidate values a variable offers, under the relaxation the level asks for. *)
let oracle_values ~relaxed (d : Domain.t) =
  if relaxed then List.init (Domain.hi d - Domain.lo d + 1) (fun i -> Domain.lo d + i)
  else Domain.to_list d

(* Does the propagator accept this total assignment of its scope?

   Built on a SCRATCH store, not the live one, for three reasons that all matter. A hole
   cannot be reached by [Store.fix] (I-D3: domains only shrink, and the bounds relaxation
   above deliberately proposes values the live domain has removed). A [Conflict] on the
   live store would enter its reason arena and could be read back by conflict analysis.
   And a propagator that prunes on the way to failing would leave trail entries stamped
   with its id at a level the search does not know about. A fresh store costs an array
   copy per tuple and buys all three.

   [with_running] because [Store.conflict] stamps [t.current_prop], and a propagator that
   fails while nobody is marked as running would be attributed to [Store.no_prop]. *)
let oracle_accepts (inst : Propagator.instance) ~names ~base ~(scope : Var.t array)
    ~(tuple : int array) =
  let domains = Array.copy base in
  Array.iteri (fun k v -> domains.(Var.to_int v) <- Domain.singleton tuple.(k)) scope;
  let scratch = Store.create ~names ~domains in
  incr oracle_tuples;
  match
    Store.with_running scratch inst.Propagator.id (fun () -> inst.Propagator.run scratch)
  with
  | Propagator.Conflict _ -> false
  | Propagator.Fixpoint -> true

(* Is there an accepted tuple with [scope.(fixed_k)] held at [value]? Depth-first over
   the other positions, stopping at the first witness. *)
let oracle_supported inst ~names ~base ~scope ~choices ~fixed_k ~value =
  let n = Array.length scope in
  let tuple = Array.make n 0 in
  tuple.(fixed_k) <- value;
  let rec go k =
    if k = n then oracle_accepts inst ~names ~base ~scope ~tuple
    else if k = fixed_k then go (k + 1)
    else
      List.exists
        (fun v ->
          tuple.(k) <- v;
          go (k + 1))
        choices.(k)
  in
  go 0

let oracle_scene ~names ~base ~(scope : Var.t array) =
  String.concat ", "
    (Array.to_list
       (Array.map
          (fun v ->
            Printf.sprintf "%s in %s"
              names.(Var.to_int v)
              (Domain.to_string base.(Var.to_int v)))
          scope))

(* The obligation one instance carries at its declared level, or [None] for the levels
   that carry none. [relaxed] is the bounds(Z) reading; [every_value] is the difference
   between "all of the domain" and "just the two bounds". *)
let oracle_obligation (c : Propagator.consistency) =
  match c with
  | Propagator.Domain -> Some ("domain", false, true)
  | Propagator.Bounds -> Some ("bounds", true, false)
  | Propagator.Value | Propagator.Checking -> None

(* Check ONE instance against the store as it stands. Returns every violation found
   rather than the first, so a report names all of them; the raising wrapper below is
   what the gated hot path uses. *)
let check_instance_consistency (inst : Propagator.instance) (store : Store.t) :
    violation list =
  match oracle_obligation inst.Propagator.inst_consistency with
  | None ->
      bump oracle_unobliged
        (Printf.sprintf "%s (%s)" inst.Propagator.inst_name
           (Propagator.consistency_to_string inst.Propagator.inst_consistency));
      []
  | Some (level, relaxed, every_value) ->
      (* Dedup: a variable may appear twice in [inst_vars] (Ne's header names the case),
         and enumerating it twice would let the oracle pick two different values for one
         variable -- a "support" that is not an assignment at all. *)
      let scope = Array.of_list (List.sort_uniq Var.compare inst.Propagator.inst_vars) in
      let n = Array.length scope in
      if n = 0 then []
      else
        let n_vars = Store.n_vars store in
        let names = Array.init n_vars (fun i -> Store.name store (Var.of_int i)) in
        let base = Array.init n_vars (fun i -> Store.get store (Var.of_int i)) in
        let choices =
          Array.map (fun v -> oracle_values ~relaxed base.(Var.to_int v)) scope
        in
        (* The budget is the largest support search this instance would run: the product
           over all positions but the smallest. Overshooting the estimate is fine; what
           must not happen is discovering the cost after paying it. *)
        let sizes = Array.map List.length choices in
        let product =
          Array.fold_left
            (fun acc s -> if acc > Debug.consistency_cap then acc else acc * s)
            1 sizes
        in
        if product > Debug.consistency_cap then (
          incr oracle_skipped;
          [])
        else (
          incr oracle_checks;
          bump oracle_checked (Printf.sprintf "%s (%s)" inst.Propagator.inst_name level);
          let scene = oracle_scene ~names ~base ~scope in
          let out = ref [] in
          Array.iteri
            (fun k v ->
              let d = base.(Var.to_int v) in
              let probes =
                if every_value then Domain.to_list d
                else if Domain.is_fixed d then [ Domain.lo d ]
                else [ Domain.lo d; Domain.hi d ]
              in
              List.iter
                (fun value ->
                  if
                    not
                      (oracle_supported inst ~names ~base ~scope ~choices ~fixed_k:k
                         ~value)
                  then
                    out :=
                      {
                        vi_id = inst.Propagator.id;
                        vi_name = inst.Propagator.inst_name;
                        vi_declared = inst.Propagator.inst_consistency;
                        vi_level = level;
                        vi_var = v;
                        vi_var_name = names.(Var.to_int v);
                        vi_value = value;
                        vi_scene = scene;
                      }
                      :: !out)
                probes)
            scope;
          List.rev !out)

(* Every instance, against the store as it stands. The caller is responsible for calling
   this AT A FIXPOINT: mid-pass the answer is meaningless, because a propagator that has
   not been woken yet has not been given the chance the level promises. *)
let check_consistency (t : t) (store : Store.t) : violation list =
  incr oracle_nodes;
  let acc = ref [] in
  iter_instances t (fun inst -> acc := !acc @ check_instance_consistency inst store);
  !acc

(* The gated hot-path form: first violation raises, with the scene in the message. Same
   shape as [check_fixpoint] and for the same reason -- what it reports is something
   nobody would otherwise notice, so it must not be quiet and recoverable. *)
let check_consistency_exn (t : t) (store : Store.t) : unit =
  match check_consistency t store with
  | [] -> ()
  | v :: _ -> raise (Weaker_than_declared v)

(* M6-T18: THE INCREMENTAL SEED, and why it is the full seed with the no-op runs removed.

   Until M6-T18 [propagate] enqueued every instance, in id order, on every call, and then
   fed the FIFO with the watchers of what each run changed. D-0094 measured the seed at
   75-85 % of all runs, and nearly all of those runs change nothing: at a search node only
   the decision and its consequences are new, and a propagator that watches none of it is
   still at the fixpoint it reached at the parent.

   This engine walks the same seed -- one SLOT per instance, in id order, ahead of the
   FIFO -- and runs a slot only if its instance is DIRTY:

   (a) it watches a variable that a trail entry ABOVE THE LAST VALID FIXPOINT moved, with
       M2-T5's trigger mask applied ([seed_dirty]);
   (b) it is not known to be at its fixpoint at that fixpoint: not BORN at or before it
       (a learned constraint [add]ed since, or one born after a fixpoint a backjump has
       now gone back to); or
   (c) a run earlier in this call woke it before its slot came up. The full seed had it in
       the queue already, so the wake was deduplicated and it ran AT ITS SLOT; marking it
       dirty does exactly that. A wake for a slot already passed goes to the FIFO, as it
       did before.

   A clean slot is skipped. Skipping is exact, not approximate: a clean instance's watched
   domains are what they were at a joint fixpoint (nothing above it moved them, by (a) and
   (c)), it was at its fixpoint there (by (b) and I-P2 at that return), and its output is
   a function of its watched domains (D-0034; the audit is D-0098's table). So the full
   seed's run at that slot would have pruned nothing, written nothing and woken nothing,
   and every run that IS made happens in the same order, on the same domains, as before.
   The trail, the proof and the search are the old engine's, minus its no-op runs.

   Which fixpoint is "the last valid one" is the low-water mark's job. [fixpoints] holds
   the [(trail length, epoch)] of every [Fixpoint] return whose state is still a prefix of
   the store's trail. The store's domains are a function of the trail, so a recorded state
   is still the store's exactly when no pop has gone below its length -- and
   [Store.take_low_water] says how far the pops went since the last call. Drop the records
   above it; the top one left is a joint fixpoint of the current trail, and everything
   above it is what changed. No assumption about where [Search] pops to is needed: a pop
   to a non-fixpoint position just leaves a little more of the trail to scan.

   BAGUETTE_DEBUG checks the argument where it is relied on: every skipped slot is run
   ([check_skip]) and must prune nothing, and [check_fixpoint] still re-runs everything at
   the end. A starved instance is caught at the slot it was skipped at, before any later
   wake could cover it up. *)

(* M6-T22: the seed's min-heap of dirty ids ([t.heap]). *)
let heap_push t id =
  let h = t.heap in
  let rec up i =
    if i > 0 then
      let p = (i - 1) / 2 in
      if h.(p) > id then (
        h.(i) <- h.(p);
        up p)
      else h.(i) <- id
    else h.(i) <- id
  in
  up t.heap_len;
  t.heap_len <- t.heap_len + 1

let heap_pop t =
  let h = t.heap in
  let top = h.(0) in
  let len = t.heap_len - 1 in
  t.heap_len <- len;
  (if len > 0 then
     let x = h.(len) in
     let rec down i =
       let l = (2 * i) + 1 in
       if l >= len then h.(i) <- x
       else
         let c = if l + 1 < len && h.(l + 1) < h.(l) then l + 1 else l in
         if h.(c) < x then (
           h.(i) <- h.(c);
           down c)
         else h.(i) <- x
     in
     down 0);
  top

(* Mark [id] dirty for this call's seed: the flag and the heap together. *)
let mark_dirty t id =
  if not t.dirty.(id) then (
    t.dirty.(id) <- true;
    heap_push t id)

let seed_dirty t store ~since ~epoch =
  let n = t.count in
  if Debug.enabled then t.declined <- [];
  let mark change v id =
    if id >= 0 && id < n && wakes_on (trigger_of t id) change then
      (* An instance born after the fixpoint at [epoch] has never run on this
         state: [propagate] seeds it whatever it says, so its advisor is not
         asked -- and under BAGUETTE_DEBUG not checked, since a run of it is
         EXPECTED to prune (I-P7 is a contract between runs). *)
      if t.born.(id) > epoch || advises t store id v then mark_dirty t id
  in
  let mark_slot change v sl =
    let nd = t.dyn_len.(sl) in
    if nd > 0 then
      let ids = if Debug.enabled then Array.sub t.dyn_ids.(sl) 0 nd else t.dyn_ids.(sl) in
      for j = 0 to nd - 1 do
        mark change v ids.(j)
      done
  in
  for i = Store.trail_length store - 1 downto since do
    let e : Store.entry = Store.trail_entry store i in
    let x = Var.to_int e.var in
    if x < Array.length t.wake_static then (
      let stat = t.wake_static.(x) in
      (* E1 (D-0142): the slots this entry asks -- see "The wake index by direction". *)
      let sl = 3 * x and lo = lo_moved e and hi = hi_moved e in
      let nd =
        t.dyn_len.(sl)
        + (if lo then t.dyn_len.(sl + 1) else 0)
        + if hi then t.dyn_len.(sl + 2) else 0
      in
      if Debug.enabled then
        record_unasked t e ~lo ~hi ~self:(-1) ~skip:(fun id -> t.born.(id) > epoch);
      if stat <> [] || nd > 0 then (
        let change = Domain.classify ~old:e.old ~now:e.now in
        List.iter (mark change e.var) stat;
        (* M6-T22: the self-watching instances of the slots asked; order is immaterial
           here, this only marks. *)
        mark_slot change e.var sl;
        if lo then mark_slot change e.var (sl + 1);
        if hi then mark_slot change e.var (sl + 2)))
  done

(* M6-T18: under BAGUETTE_DEBUG, the run a skipped slot would have made under the old
   full seed, made after all, and required to do nothing. Same exception and same
   no-write property as [check_claim]; not counted. *)
let check_skip (inst : Propagator.instance) (store : Store.t) : unit =
  let before = Store.trail_length store in
  let fail what =
    raise
      (Not_at_fixpoint
         (Printf.sprintf
            "M6-T18: propagator #%d %s was skipped by the incremental seed as CLEAN -- \
             none of its watched variables moved since a joint fixpoint it was at -- but \
             run at its seed slot it %s. Either it reads something it does not watch \
             (D-0034: the watch is the declaration of what it reads; see D-0098's audit) \
             or the seed's low-water bookkeeping is wrong. Fix the watch, not this \
             check."
            inst.Propagator.id inst.Propagator.inst_name what))
  in
  match
    Store.with_running store inst.Propagator.id (fun () -> inst.Propagator.run store)
  with
  | Propagator.Conflict _ -> fail "reported a CONFLICT"
  | Propagator.Fixpoint ->
      if Store.trail_length store > before then
        let e : Store.entry = Store.trail_entry store before in
        fail
          (Printf.sprintf "pruned %s from %s to %s" (Store.name store e.var)
             (Domain.to_string e.old) (Domain.to_string e.now))

(* Run every propagator to a joint fixpoint (invariant I-P2): the seed slots in id order
   (only the dirty ones run, see above), then the FIFO, re-fed only by the watchers of
   variables a run actually changed. *)
let propagate ?stop ?(poll_runs = default_poll_runs) (t : t) (store : Store.t) : outcome =
  let n = n_instances t in
  if n = 0 then Fixpoint
  else
    (* M6-T22: [t]'s own, all false on entry; this call clears what it sets, on every
       exit (see [t.dirty]). *)
    let dirty = t.dirty in
    (* The epoch of the fixpoint the seed is relative to, or -1 when there is none and
       every slot is dirty. *)
    let since_epoch =
      match t.seen with
      | Some (s, h) when s == store && t.incremental -> (
          let lw = Store.take_low_water store h in
          let rec drop = function
            | (len, _) :: rest when len > lw -> drop rest
            | l -> l
          in
          t.fixpoints <- drop t.fixpoints;
          match t.fixpoints with
          | [] -> -1
          | (since, e) :: _ ->
              seed_dirty t store ~since ~epoch:e;
              (* Rule (b): every id with [born > e], read off [births] (M6-T22). *)
              List.iter (mark_dirty t) t.newborns;
              let rec young = function
                | (b, ids) :: rest when b > e ->
                    List.iter (mark_dirty t) ids;
                    young rest
                | _ -> ()
              in
              young t.births;
              if Debug.enabled then check_declined t store;
              e)
      | _ ->
          t.seen <-
            (if t.incremental then Some (store, Store.register_low_water store) else None);
          t.fixpoints <- [];
          -1
    in
    if since_epoch < 0 then (
      (* Every slot: an ascending array is already a min-heap. *)
      Array.fill dirty 0 n true;
      for id = 0 to n - 1 do
        t.heap.(id) <- id
      done;
      t.heap_len <- n);
    let in_queue = t.in_queue in
    let queue = Queue.create () in
    let enqueue id =
      if (not in_queue.(id)) && id >= 0 && id < n then (
        in_queue.(id) <- true;
        Queue.push id queue)
    in
    (* Seed slots below [cursor] have been passed; a wake for one at or above it is a
       wake the full seed's queue would have deduplicated (rule (c) above). *)
    let cursor = ref 0 in
    let wake id = if id >= !cursor && id < n then mark_dirty t id else enqueue id in
    let conflict = ref None in
    (* M6-T21: set by the poll at the end of a completed [Fixpoint] run. The poll also
       ENDS both loops itself -- the cursor to [n], the queue emptied -- rather than the
       loops testing [stopped] in their guards: the seed loop's guard is evaluated once
       per instance SLOT, run or skipped, which on a large learned database is billions
       of times in one run (3.5e9 skipped slots in D-0136's 600 s run), and one more test
       there measured +0.7 % instructions. Here the cost is per RUN, and only when the
       caller passed [?stop]. *)
    let stopped = ref false in
    let poll =
      match stop with
      | None -> fun () -> ()
      | Some stop ->
          (* A countdown left by a caller with a longer period is cut to this one's. *)
          let poll_runs = max 1 poll_runs in
          if t.poll_left > poll_runs then t.poll_left <- poll_runs;
          fun () ->
            t.poll_left <- t.poll_left - 1;
            if t.poll_left <= 0 then (
              t.poll_left <- poll_runs;
              if stop () then (
                stopped := true;
                (* M6-T22: the slots and the queue this abandons, cleared. *)
                for i = 0 to t.heap_len - 1 do
                  dirty.(t.heap.(i)) <- false
                done;
                t.heap_len <- 0;
                cursor := n;
                Queue.iter (fun id -> in_queue.(id) <- false) queue;
                Queue.clear queue))
    in
    let run_one id =
      let inst = t.instances.(id) in
      let before = Store.trail_length store in
      incr runs;
      t.ctr.c_runs <- t.ctr.c_runs + 1;
      (* The whole of M2-T7's threading, in one bracket: everything [inst] pushes while
         this call is in flight is stamped with [inst]'s own id, and nothing else can be.
         [check_attribution] then reads it back on both arms -- a propagator may push
         prunings and *then* conflict, so the conflict arm has new entries to check too,
         which is why the check is not simply folded into [watchers_of_new_entries]. *)
      match Store.run_as store inst.Propagator.id inst.Propagator.run store with
      | Propagator.Conflict c ->
          check_attribution t inst store ~since:before ~conflict:(Some c);
          t.ctr.c_contra <- t.ctr.c_contra + 1;
          bump_by_id t id ~eff:false;
          conflict := Some c
      | Propagator.Fixpoint ->
          check_attribution t inst store ~since:before ~conflict:None;
          let pruned = Store.trail_length store > before in
          if pruned then t.ctr.c_effectful <- t.ctr.c_effectful + 1;
          bump_by_id t id ~eff:pruned;
          if pruned && Debug.enabled && vetoes_self t id then check_claim inst store;
          (* M11-complexity-T14: a run that pushed nothing has no entry to walk, and the
             walk would return [] after building its closures; nine runs in ten on
             codes-cp's QR48 are such runs. [t.declined] is [[]] here either way: every
             walk and every seed is followed by [check_declined], which empties it. *)
          if pruned then
            List.iter wake (watchers_of_new_entries ~self:id t store ~since:before);
          if Debug.enabled then check_declined t store;
          (* M6-T21: AFTER the run and its wakes, so the run is whole whatever the poll
             says. Not on the [Conflict] arm: that call is leaving anyway. *)
          poll ()
    in
    (* The slots [!cursor .. upto - 1] are passed CLEAN: counted, and under
       BAGUETTE_DEBUG run by [check_skip], exactly as the slot-by-slot walk did. *)
    let pass_clean upto =
      t.ctr.c_skipped <- t.ctr.c_skipped + (upto - !cursor);
      if Debug.enabled then
        for q = !cursor to upto - 1 do
          check_skip t.instances.(q) store
        done
    in
    let loops () =
      (* M6-T22: the seed walks the dirty slots in id order off [t.heap] -- the same
         runs, in the same order, as the walk over every slot, which cost O(n) per call
         on a learned database of n. *)
      while Option.is_none !conflict && t.heap_len > 0 do
        let id = heap_pop t in
        pass_clean id;
        cursor := id + 1;
        dirty.(id) <- false;
        t.ctr.c_seeded <- t.ctr.c_seeded + 1;
        run_one id
      done;
      if Option.is_none !conflict then (
        pass_clean n;
        cursor := n);
      while Option.is_none !conflict && not (Queue.is_empty queue) do
        let id = Queue.pop queue in
        in_queue.(id) <- false;
        run_one id
      done
    in
    (* M6-T22: a [Conflict] leaves the seed slots past the cursor and the queue's
       members marked; an exception (a BAGUETTE_DEBUG check, an attribution failure)
       can leave anything. Both are cleared here, so the next call starts all false. *)
    (match loops () with
    | () ->
        for i = 0 to t.heap_len - 1 do
          dirty.(t.heap.(i)) <- false
        done;
        t.heap_len <- 0;
        Queue.iter (fun id -> in_queue.(id) <- false) queue
    | exception e ->
        Array.fill dirty 0 n false;
        t.heap_len <- 0;
        Array.fill in_queue 0 n false;
        raise e);
    (* Reset the low-water mark HERE, at the end of the call, and not only at its start:
       the next call must see the pops since this call RETURNED. Read only at the start,
       the mark would still stand at this call's starting length, below every fixpoint
       recorded at the end of it, and the next call would drop that record and fall back
       to the full seed -- conservative, so never wrong, but it threw away most of the
       gain on mario until it was measured (D-0098). [propagate] never pops, so this
       read loses nothing. *)
    (match t.seen with
    | Some (s, h) when s == store -> ignore (Store.take_low_water store h)
    | _ -> ());
    match !conflict with
    | Some c -> Conflict c
    | None when !stopped ->
        (* M6-T21: not a fixpoint, so neither I-P2 nor the M6-T18 record below. The next
           call (there is none in a solve: the search is ending) would reseed from the
           last recorded fixpoint, exactly as after a [Conflict]. *)
        raise Stopped
    | None ->
        (* I-P2, checked rather than asserted in a comment. Only on the no-failure
           return: I-P2 says nothing about a [Conflict], and re-running propagators
           against a store that has already failed would be meaningless. *)
        if Debug.enabled then check_fixpoint t store;
        (* M6-T18: record this state as a joint fixpoint. Every instance is at its
           fixpoint here (I-P2); one not known at the fixpoint the seed started from is
           born now. A record at the same length is the same state, so it is replaced. *)
        if t.incremental then (
          let e = t.epoch + 1 in
          t.epoch <- e;
          (* Every id with [born > since_epoch] is born at [e]: [newborns] and the head
             of [births] down to [since_epoch], merged into one entry (M6-T22). *)
          let rec take acc = function
            | (b, ids) :: rest when b > since_epoch -> take (List.rev_append ids acc) rest
            | rest -> (acc, rest)
          in
          let merged, rest = take t.newborns t.births in
          List.iter (fun id -> t.born.(id) <- e) merged;
          t.births <- (if merged = [] then rest else (e, merged) :: rest);
          t.newborns <- [];
          let len = Store.trail_length store in
          t.fixpoints <-
            (match t.fixpoints with
            | (l, _) :: rest when l = len -> (len, e) :: rest
            | l -> (len, e) :: l));
        (* M2-T10. Here and not in [Search]: "at a fixpoint" is a property this loop
           knows and its caller can only assume, and this is the same return that I-P2
           is checked on, for the same reason -- both are statements about the state the
           engine has just finished producing. [Search] calls [propagate] exactly once
           per node (see its [dfs]), so a per-fixpoint check IS a per-node check, and
           the node count [oracle_nodes] reports is the search's own.

           Not on the [Conflict] arm: a failed store is not a fixpoint, the domains are
           whatever the failing propagator left behind, and "every remaining value has a
           support" is not a claim any level makes about a scene with no solutions. *)
        if Debug.consistency_enabled then check_consistency_exn t store;
        Fixpoint
