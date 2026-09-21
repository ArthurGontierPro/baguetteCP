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
   by the propagator. *)

type outcome = Fixpoint | Conflict of Store.conflict

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
  (* var -> ids of the propagator instances that read it. Built once at [create] time
     from each instance's [inst_vars]; instances never change their variable set after
     that, so the table does not need to be rebuilt per call. *)
  watchers : (Var.t, int list) Hashtbl.t;
  (* id -> that instance's trigger mask, indexed by [Propagator.id] (not by position in
     [instances]) because that is what the watcher lists hold. Any id with no instance
     gets [wake_on_any]: an unknown instance is one whose reads are unknown, and the safe
     answer for an unknown reader is always "wake it". *)
  mutable triggers : trigger array;
}

let create ?(trigger = default_trigger) (instances : Propagator.instance list) : t =
  let watchers = Hashtbl.create 64 in
  List.iter
    (fun (inst : Propagator.instance) ->
      List.iter
        (fun v ->
          let cur = try Hashtbl.find watchers v with Not_found -> [] in
          if not (List.mem inst.Propagator.id cur) then
            Hashtbl.replace watchers v (inst.Propagator.id :: cur))
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
  { instances = Array.of_list instances; watchers; triggers }

let n_instances t = Array.length t.instances

(* ------------------------------------------------- registering a LEARNED constraint *)

(* The id the next [add] will demand, which is also the id [Propagator.pack] must be
   given. Exposed rather than left to the caller to compute from [n_instances], because
   the two are the same number only because [add] keeps them so, and a caller that
   derived it for itself would silently stop agreeing the day that stops being true. *)
let next_id t = Array.length t.instances

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

   Appending copies both arrays. That is O(n) per learned constraint and is the right
   trade for now: learning adds constraints at a rate bounded by conflicts, not by
   propagations, and an amortised-growth buffer here would be a second representation of
   "which instances exist" for no measured gain. Say so in M2-L4 if the retention policy
   makes it a hot path. *)
let add ?(trigger = default_trigger) (t : t) (inst : Propagator.instance) =
  let expected = next_id t in
  if inst.Propagator.id <> expected then
    invalid_arg
      (Printf.sprintf
         "Engine.add: instance %s was packed with id #%d, but this engine's next id \
          is           #%d. Engine.propagate indexes its instance array BY ID, so the \
          two must           agree; pack with Engine.next_id."
         inst.Propagator.inst_name inst.Propagator.id expected);
  t.instances <- Array.append t.instances [| inst |];
  List.iter
    (fun v ->
      let cur = try Hashtbl.find t.watchers v with Not_found -> [] in
      if not (List.mem inst.Propagator.id cur) then
        Hashtbl.replace t.watchers v (inst.Propagator.id :: cur))
    inst.Propagator.inst_vars;
  if Array.length t.triggers <= inst.Propagator.id then (
    let grown = Array.make (inst.Propagator.id + 1) wake_on_any in
    Array.blit t.triggers 0 grown 0 (Array.length t.triggers);
    t.triggers <- grown);
  t.triggers.(inst.Propagator.id) <- trigger inst

(* The variables an instance watches, or [None] if this engine has no such instance.

   The shape [Analysis.analyse] wants (M2-L2), and it is here rather than reconstructed
   by the caller because [t.instances] is indexed by id and only [add] keeps it so. A
   caller that built this from its own list of instances would stop agreeing with the
   engine the moment a learned constraint was registered. *)
let vars_of t id =
  if id >= 0 && id < Array.length t.instances then
    Some t.instances.(id).Propagator.inst_vars
  else None

(* M2-L6: the PB row instance [id] is, or [None] when it does not expose one. The same
   shape as [vars_of] and for the same reason -- lib/core/pb_analysis.ml is shown the
   engine through two narrow functions rather than being handed the instance array. *)
let row_of t store id =
  if id >= 0 && id < Array.length t.instances then
    t.instances.(id).Propagator.inst_row store
  else None

(* The builtin name instance [id] was packed under, for a diagnostic that has to say
   WHICH propagator family declined to expose a row. "<unknown>" rather than a raise: a
   fallback reason nobody can read is a counter with no diagnosis behind it, but it is
   still only a message. *)
let name_of t id =
  if id >= 0 && id < Array.length t.instances then t.instances.(id).Propagator.inst_name
  else "<unknown>"

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
let watchers_of_new_entries t store ~since =
  let acc = ref [] in
  for i = Store.trail_length store - 1 downto since do
    let e : Store.entry = Store.trail_entry store i in
    match Hashtbl.find_opt t.watchers e.var with
    | None -> ()
    | Some ids ->
        let change = Domain.classify ~old:e.old ~now:e.now in
        List.iter
          (fun id ->
            if wakes_on (trigger_of t id) change then (
              incr wakes;
              acc := id :: !acc)
            else incr masked_wakes)
          ids
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
   run the suite actually makes. The cost is one hashtable lookup and one short [List.mem]
   per NEW TRAIL ENTRY -- the same lookup [watchers_of_new_entries] makes on the same
   entries a moment later, and bounded by the number of prunings, not by the trail or the
   variable count.

   The watcher table is consulted rather than [inst.inst_vars] directly because it is
   built from exactly that list ([create] above) and is indexed, so membership is O(the
   watchers of one variable) instead of O(the instance's arity). The two agree by
   construction; if they ever did not, this check is what would say so. *)
let check_attribution (t : t) (inst : Propagator.instance) store ~since
    ~(conflict : Store.conflict option) =
  let id = inst.Propagator.id in
  let watches v =
    match Hashtbl.find_opt t.watchers v with None -> false | Some ids -> List.mem id ids
  in
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

exception Not_at_fixpoint of string

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
  Array.iter
    (fun (inst : Propagator.instance) ->
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
    t.instances

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
  Array.fold_left
    (fun acc inst -> acc @ check_instance_consistency inst store)
    [] t.instances

(* The gated hot-path form: first violation raises, with the scene in the message. Same
   shape as [check_fixpoint] and for the same reason -- what it reports is something
   nobody would otherwise notice, so it must not be quiet and recoverable. *)
let check_consistency_exn (t : t) (store : Store.t) : unit =
  match check_consistency t store with
  | [] -> ()
  | v :: _ -> raise (Weaker_than_declared v)

(* Run every propagator to a joint fixpoint (invariant I-P2): a FIFO queue seeded with
   every instance, so nothing is skipped on the first pass, and thereafter re-fed only
   by the watchers of variables a run actually changed. *)
let propagate (t : t) (store : Store.t) : outcome =
  let n = n_instances t in
  if n = 0 then Fixpoint
  else
    let in_queue = Array.make n false in
    let queue = Queue.create () in
    let enqueue id =
      if (not in_queue.(id)) && id >= 0 && id < n then (
        in_queue.(id) <- true;
        Queue.push id queue)
    in
    Array.iter
      (fun (inst : Propagator.instance) -> enqueue inst.Propagator.id)
      t.instances;
    let conflict = ref None in
    while Option.is_none !conflict && not (Queue.is_empty queue) do
      let id = Queue.pop queue in
      in_queue.(id) <- false;
      let inst = t.instances.(id) in
      let before = Store.trail_length store in
      incr runs;
      (* The whole of M2-T7's threading, in one bracket: everything [inst] pushes while
         this call is in flight is stamped with [inst]'s own id, and nothing else can be.
         [check_attribution] then reads it back on both arms -- a propagator may push
         prunings and *then* conflict, so the conflict arm has new entries to check too,
         which is why the check is not simply folded into [watchers_of_new_entries]. *)
      match
        Store.with_running store inst.Propagator.id (fun () -> inst.Propagator.run store)
      with
      | Propagator.Conflict c ->
          check_attribution t inst store ~since:before ~conflict:(Some c);
          conflict := Some c
      | Propagator.Fixpoint ->
          check_attribution t inst store ~since:before ~conflict:None;
          let woken = watchers_of_new_entries t store ~since:before in
          List.iter enqueue woken
    done;
    match !conflict with
    | Some c -> Conflict c
    | None ->
        (* I-P2, checked rather than asserted in a comment. Only on the no-failure
           return: I-P2 says nothing about a [Conflict], and re-running propagators
           against a store that has already failed would be meaningless. *)
        if Debug.enabled then check_fixpoint t store;
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
