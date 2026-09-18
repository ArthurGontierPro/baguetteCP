(* retention.ml: the learned-constraint database, its deletion, and the retention
   policy (M2-L4, absorbing M2-T4).

   Consistency level: none -- this is not a propagator. Governing records:
   docs/DECISIONS.md D-0045 (the `wipe_level` finding this row exists to resolve),
   D-0044 and its amendments (the learned object, and the fork that makes it
   proof-only), D-0024 (what `wipe_level` imitates); docs/INVARIANTS.md I-X2 and I-X3;
   docs/PROOF-FORMAT.md section 5.

   ===========================================================================
   1. WHO OWNS A LEARNED CONSTRAINT'S LIFETIME
   ===========================================================================

   This row's real question, and the one D-0045 said to settle BEFORE choosing between
   LBD and activity. The answer:

     **This database owns it, alone. A backjump cannot be a co-owner, and since M2-L4
     that is a property of the code rather than a property of the call sites.**

   The argument is three steps and each one is checkable:

   1. [Writer.wipe_level l] deletes exactly the set {id | tag(id) >= l}
      (lib/proof/writer.ml, and D-0024 is why it is that set and not "everything derived
      since"). It is the only bulk deleter in the tree.
   2. A learned id is tagged 0. [Learned.introduce] and [Pb_analysis.introduce] both emit
      inside [Justify.with_level ctx 0], which moves the writer's level FOR REAL, so the
      tag and the emitted proof agree (I-X3). M2-L1 measured the alternative: tagged at
      the conflict level, the backjump deletes it and the next citation is "Trying to
      access constraint with ID 3 that has already been deleted".
   3. Levels are non-negative ([Writer.set_level] rejects a negative), so a tag of 0 is
      reached by [wipe_level l] only at l = 0. **[Writer.wipe_level] now refuses l = 0**
      -- an [invalid_arg] naming this module. Before M2-L4 that was a fact about
      [Search]'s four call sites, all of which pass a decision level; a fifth call site
      passing 0 would have made the backjump a second owner silently. It is now a fact
      about the writer.

   So there is exactly one deleter of a learned id, and it is [retire] below. Everything
   else in this module routes through it -- eviction, the end-of-search sweep, and the
   test harness alike -- which is what makes "deleted exactly once" (I-X2) a property of
   one function with one membership test rather than of an argument about call order.

   ### The double-delete this actually prevents, which is NOT the backjump

   D-0045's addendum warns about the policy and the backjump both wanting a learned id
   gone. Step 3 above closes that off. The double-delete that would really have happened
   is nearer home and is worth naming, because it is the shape a reader will reintroduce:

   before this row, [Search.solve] retired learned ids from [stats.learned_rev], the list
   of every id ever introduced. A policy that evicts mid-search and leaves that list
   alone gives two deletions of one id from ONE owner -- the end-of-search sweep repeating
   what the eviction already did. [stats.learned_rev] is now an audit trail and nothing
   reads it to delete; the sweep is [retire_all], which deletes what this database still
   HOLDS. The distinction between "introduced" and "held" is the whole fix.

   And it matters that the checker catches it rather than only our audit: a second
   [Writer.forget] is a no-op, so [BAGUETTE_PROOF_AUDIT=1]'s live-set check cannot see a
   double delete at all (D-0045's closing paragraph). What sees it is `del id` on an
   already-deleted id, which 3.0.2 refuses -- and [test_retention.ml] performs that break
   rather than citing it.

   ===========================================================================
   2. THE POLICY, AND THE MEASUREMENT THAT CHOSE IT
   ===========================================================================

   The row asks for LBD-like or activity-based, justified by a measurement. Both were
   measured before either was written. The measurements are stated here with how they
   were taken, because a figure in this repository that says only what it is has twice
   turned out to be wrong.

   ### Activity is not a heuristic here; it is the constant zero

   An activity policy scores a learned constraint by how often it takes part in a later
   conflict. Taking part requires propagating. **No learned constraint in this solver
   propagates.** [Learned.instance] exists and builds a [Linear] instance, and nothing in
   lib/ calls it: D-0044's amendment bounds where a runtime instance CAN exist, and
   lib/core/learn.ml's header takes fork (ii), proof-only, in as many words. So every
   learned constraint has activity 0, for the whole search, always.

   Measured rather than read off the source, because "nothing calls it" is exactly the
   claim that goes stale: with the database instrumented to count citations
   ([cite] below), the 39-model suite records **0 citations of a learned id, on every
   model**. [n_cited] reports it and [test_retention.ml] asserts it, so the day a learned
   constraint does start propagating, the assertion fails and this paragraph is what
   changes.

   An activity policy over a constant is FIFO with a heuristic's name on it. [fifo] below
   is therefore the activity policy, spelled as what it actually is.

   ### LBD is available, and on today's suite it does not discriminate either

   LBD -- the number of distinct decision levels the minimised clause's literals sit at
   -- is computable at derivation time from the cut alone, needs no runtime
   participation, and is therefore the one of the two that carries information at all.
   [Learn.lbd] computes it, after minimisation (see its comment for why the order
   matters).

   Measured over all 39 models, 2026-09-18, by running the solver with `--stats` and
   reading the `stats: lbd` histogram ([Search.stats_lbd]):

   | LBD | learned clauses |
   |---|---|
   | 1 | 72 |
   | 2 | 16 |
   | >= 3 | **0** |

   -- 88 clauses in all, which is the same denominator lib/core/pb_analysis.ml's header
   carries for the conversion rate, arrived at independently here.

   and on `width_sat_depth`, the only model with a search deep enough to matter, **all 49
   learned clauses have LBD 1** and every one of them is a UNIT clause. The maximum LBD
   anywhere in the suite is 2.

   Two consequences, and the second is the one that shaped the code:

   - **Glucose's glue exemption is measured inert and is deliberately NOT implemented.**
     "Keep every clause with LBD <= 2 forever" retains 100% of what this suite learns.
     A parameter whose only measured value is "never fires" is a parameter that is
     exercised by nothing, which is this project's signature defect; so there is no
     [glue] argument here. If a later model produces LBD >= 3, adding it is one line and
     the histogram is how you will know.
   - **LBD is the ranking key; the CAP is the budget, and the cap is what fires.** With
     LBD tied everywhere on this suite, the tie-break -- age, oldest evicted first --
     does the work. That is stated rather than hidden: a reader who sees [lbd] evicting
     in age order on every shipped model should know it is the tie-break and not a bug.

   ### What retention costs, and what it was expected to buy -- the measurement REFUTED
   ### the expectation, and the default follows the measurement

   This is the part that changed after it was measured, and it is recorded that way round
   on purpose.

   The expectation, written before the numbers: a learned constraint costs nothing in
   search (nothing propagates it) and a `del` line to retire, so eviction cannot save
   proof bytes -- but every live constraint is one the checker's unit propagation walks on
   every subsequent `rup`, and this proof is almost all `rup` lines, so eviction should
   buy verification time.

   Measured on `width_sat_depth` (73 learned constraints, the only shipped model that
   learns enough for a cap to fire), 2026-09-18, by solving with `BAGUETTE_RETENTION=<p>`
   and then running the checker `scripts/checker.sh` resolves -- VeriPB 3.0.2 -- over the
   emitted proof, 15 runs, mean wall time; peak checker RSS from `/usr/bin/time -v`:

   | policy | evicted | .pbp bytes | `del` rules | check (mean) | checker peak RSS |
   |---|---|---|---|---|---|
   | `off` (keep-all) | 0 | **48145** | 124 | **14.67 ms** | 7432 kB |
   | `lbd:64` | 9 | 48226 | 133 | -- | -- |
   | `lbd:32` | 41 | 48514 | 165 | -- | -- |
   | `lbd:16` | 57 | **48658** | 181 | **16.16 ms** | 7336 kB |
   | `lbd:8` | 65 | 48730 | 189 | -- | -- |
   | `lbd:4` | 69 | 48766 | 193 | -- | -- |
   | `lbd:0` | 73 | **48793** | 196 | **16.12 ms** | 7384 kB |

   **The expected benefit is not there and the cost is.** Bytes rise monotonically with
   how aggressively the policy evicts, +1.1% at cap 16 and +1.3% at cap 0. Verification
   gets about **10% SLOWER**, not faster: the extra `del` rules cost the checker more than
   the smaller database saves it. Checker RSS does not move outside noise. Every policy
   on the axis is dominated by `keep-all`.

   **So [default] is [keep_all].** The machinery is built, named, swappable, exercised and
   measured; it is off because the measurement says off. Turning it on would be choosing
   a policy by citation, which is the one thing this row's text forbids.

   What would change that verdict, stated so the next session does not have to re-derive
   it: the benefit term is per-`rup` propagation over the live database and it grows with
   database size, while the cost term is `del` rules and grows with the number of
   evictions. At 73 constraints the cost term wins. Re-run the table above on a model
   whose learned database is an order of magnitude larger -- and if the crossover is
   found, `lbd:<cap>` is one environment variable away and nothing else has to change.

   A last note on the cap sweep, because it settles something the row worried about:
   **the proof verifies at every cap, including `lbd:0`, which deletes each learned
   constraint on the line after it is introduced.** Nothing in this proof depends on a
   learned constraint still being live -- consistent with the citation count of 0 above,
   and the reason eviction is safe here at all. It would NOT be safe in a solver whose
   later `rup` lines leaned on a learned unit to propagate, and that is a constraint on
   M2-L6's successors rather than a property of retention in general: deleting is free in
   a plain solver and is not free in a proof-logging one.

   ---------------------------------------------------------------------------
   M2-L12 RE-RAN THE SWEEP, BECAUSE THE CONDITION ABOVE WAS MET
   ---------------------------------------------------------------------------

   D-0051 said the verdict reverses "when a learned constraint is actually propagated",
   and the paragraph above says eviction "would NOT be safe in a solver whose later `rup`
   lines leaned on a learned unit to propagate". M2-L12 built exactly that solver: a unit
   learned clause is applied at every node and a wider one is a registered
   [Clause.Learned_clause] instance. So the table was re-run rather than inherited, on
   the same model, the same four columns, with the same method (2026-09-18).

   First, the OLD column reproduced EXACTLY -- `off` 48145 bytes / 124 `del`, `lbd:16`
   48658 / 181, `lbd:0` 48793 / 196, all VERIFIED -- which is what makes the new one
   worth reading. `BAGUETTE_PROPAGATE_LEARNED=off` is the build that produces it.

   With propagation ON, on `width_sat_depth` (73 learned constraints, 49 of them cited):

     | policy   | evicted | eviction refused | .pbp bytes | `del` | nodes | checker  |
     |----------|---------|------------------|------------|-------|-------|----------|
     | off      |       0 |                0 |      48145 |   124 |    99 | VERIFIED |
     | lbd:16   |      16 |             1397 |      48289 |   140 |    99 | VERIFIED |
     | fifo:8   |      20 |             1745 |      48325 |   144 |    99 | VERIFIED |
     | lbd:0    |      24 |             2125 |      48361 |   148 |    99 | VERIFIED |

   **The verdict is unchanged and the ARGUMENT for it is not.** D-0051's reason was
   "activity is the constant zero". That reason is now false: 49 of the 73 constraints
   have a consumer. The reason `keep_all` still wins is the new one:

     1. **The constraints with activity are exactly the ones eviction may not touch.**
        [reduce] below refuses to evict a cited constraint, so the achievable cap is
        bounded below by the number of live consumers: at `lbd:0`, which asks for an
        empty database, 24 of 73 go and 49 stay. Eviction cannot reduce the work the
        globals do, because the globals are what pins them.
     2. **What it CAN evict has no activity**, being the uncited remainder -- duplicates
        and M2-L6 PB rows with no runtime instance -- so evicting it saves no propagation
        and only adds `del` lines. Bytes and `del` rules still rise monotonically with
        eviction, exactly as before.
     3. **The tree is the same size at every cap** (99 nodes in all four rows), which is
        the direct measurement that eviction is buying nothing here.

   So: **`keep_all` stands, and D-0051's "what would reverse this" is now spent.** Do not
   cite it a third time as "retention does not help while nothing propagates a learned
   constraint" -- something does. Cite it as: retention does not help while the
   constraints that propagate are the ones a policy may not evict, and the ones it may
   evict do not propagate. What would reverse THAT is a database large enough for the
   uncited remainder to dominate, or a consumer cheap enough to be worth dropping -- and
   the sweep above is re-runnable with two environment variables.

   And the safety note above has to be read the other way round now. The proof still
   verifies at every cap, but no longer because nothing leans on a learned constraint:
   it verifies because [reduce] refuses to delete the ones that are leaned on. The
   citation guard is doing the work the citation count of 0 used to do for free.

   ### Determinism

   The gate requires two runs of one binary to be byte-identical, and a learned database
   iterated in hash order is the specific way learning breaks it (lib/core/learn.ml says
   so, and this is the module that inherits the obligation). So: [live] is a LIST, in
   introduction order; [gone] and [cited] are [Hashtbl]s that are only ever queried with
   [find_opt]/[mem] and never folded or iterated; and every policy below sorts on a key
   ending in [e_seq], which is unique, so no sort is left to compare equal elements.
*)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer

(* ------------------------------------------------------------------ entries *)

(* One learned constraint the database holds.

   [e_key] is the constraint's canonical rendering ([Learned.to_string], which sorts and
   merges in [Learned.make]), used for the duplicate MEASUREMENT below and for nothing
   else -- it is not part of any policy. [e_seq] is introduction order and is unique,
   which is what makes every sort here total. *)
type entry = {
  e_cid : Writer.cid;
  e_lbd : int;
  e_size : int; (* terms in the row; 1 is a unit clause *)
  e_seq : int;
  e_key : string;
  e_origin : string;
}

let entry_cid e = e.e_cid
let entry_lbd e = e.e_lbd
let entry_seq e = e.e_seq
let entry_origin e = e.e_origin

(* ----------------------------------------------------------------- policies *)

(* A policy is a function from the live database to the entries to evict. That is the
   whole of the swappable axis, and it is a function rather than a threshold for the
   reason D-0044 gives for the reduction rule and the stopping criterion: the interesting
   ones are not parameterisations of each other.

   The argument is the live set in INTRODUCTION order (oldest first), and the result must
   be a subset of it. [reduce] checks the subset property rather than trusting it, because
   a policy that returned an id the database does not hold would be a delete from a second
   owner -- the exact failure this module exists to prevent, arriving through the one door
   that is meant to be extensible. *)
type policy = { p_name : string; p_evict : entry list -> entry list }

let name p = p.p_name

(* Off. The behaviour before M2-L4: everything is retained until the search ends. Test
   (c)'s "policy off" side, and the control every measurement here is taken against. *)
let keep_all = { p_name = "keep-all"; p_evict = (fun _ -> []) }

(* Evict oldest-first down to [cap]. This IS the activity policy -- see the header: with
   every learned constraint's activity identically zero, an activity ranking is a tie
   across the whole database and the tie-break is all that is left. Spelling it [fifo]
   says what it does instead of what it was named after. *)
let fifo ~cap =
  {
    p_name = Printf.sprintf "fifo(cap=%d)" cap;
    p_evict =
      (fun live ->
        let n = List.length live in
        if n <= cap then []
        else
          List.filteri
            (fun i _ -> i < n - cap)
            (List.sort (fun a b -> compare a.e_seq b.e_seq) live));
  }

(* The policy. Rank by LBD descending -- a higher LBD is a worse constraint, Glucose's
   direction -- and break ties by age, oldest first. Evict down to [cap].

   No glue exemption: measured inert, see the header. The cap is the budget and the
   ranking decides who pays it. *)
let lbd ~cap =
  {
    p_name = Printf.sprintf "lbd(cap=%d)" cap;
    p_evict =
      (fun live ->
        let n = List.length live in
        if n <= cap then []
        else
          let worst_first =
            List.sort
              (fun a b ->
                match compare b.e_lbd a.e_lbd with 0 -> compare a.e_seq b.e_seq | c -> c)
              live
          in
          List.filteri (fun i _ -> i < n - cap) worst_first);
  }

(* The default is KEEP-ALL, and that is the measurement's verdict rather than a decision
   not to choose -- see the table in the header. Every cap measured costs proof bytes and
   costs verification time; none saves either. A policy turned on against its own
   measurement is a policy chosen by citation.

   [lbd ~cap:16] is what the default WOULD be if the crossover the header describes were
   ever found, and `BAGUETTE_RETENTION=lbd:16` is how to run it without changing a line.
   It is not dead code: test/unit/test_retention.ml runs it end to end through the
   checker, which is where the eviction path is exercised. *)
let default = keep_all

(* Every policy, at one cap. For a test that wants to run the axis rather than a point
   on it. *)
let policies ~cap = [ keep_all; fifo ~cap; lbd ~cap ]

(* ---------------------------------------------------------------- the database *)

exception Double_delete of string
exception Cited of string
exception Not_owned of string

let () =
  Printexc.register_printer (function
    | Double_delete r -> Some ("learned-constraint double delete (invariant I-X2)\n" ^ r)
    | Cited r -> Some ("a cited learned constraint was deleted (invariant I-X3)\n" ^ r)
    | Not_owned r -> Some ("retention: a policy named an id it does not hold\n" ^ r)
    | _ -> None)

type t = {
  policy : policy;
  mutable live_rev : entry list; (* newest first *)
  mutable next_seq : int;
  mutable n_added : int;
  mutable n_evicted : int;
  mutable n_swept : int;
  mutable n_duplicate : int;
  mutable n_cited : int;
  mutable n_pinned : int;
      (* M2-L12. Evictions the policy PROPOSED and [reduce] did NOT perform, because the
         constraint had a live consumer. Proposals and not distinct constraints: [reduce]
         runs once per conflict and an over-cap policy re-proposes the same pinned
         entries every time, so this number is much larger than the database. That is
         what makes it the right counter for "how hard is the policy pushing against the
         citations", which is the question the sweep in the header asks. See [reduce]. *)
  gone : (Writer.cid, entry) Hashtbl.t;
      (* Retired by this database: cid -> the entry it was. Lookup only, never iterated
         (determinism, header). It is what turns a second deletion into an exception
         instead of a silently accepted no-op. *)
  cited : (Writer.cid, string) Hashtbl.t;
      (* cid -> what cites it, for the live citation. Lookup only. See [cite]. *)
  keys : (string, Writer.cid) Hashtbl.t;
      (* Canonical row text -> the first id that stated it. Lookup only, and MEASUREMENT
         only: it feeds [n_duplicate] and no policy reads it. M1-T59 found duplicate
         `rup` lines harmless per-proof; a retention policy that evicts and lets the same
         clause be re-learned is how they stop being harmless, so the count is kept where
         a later row can see it. *)
}

let create ?(policy = default) () =
  {
    policy;
    live_rev = [];
    next_seq = 0;
    n_added = 0;
    n_evicted = 0;
    n_swept = 0;
    n_duplicate = 0;
    n_cited = 0;
    n_pinned = 0;
    gone = Hashtbl.create 64;
    cited = Hashtbl.create 16;
    keys = Hashtbl.create 64;
  }

let live t = List.rev_map (fun e -> e.e_cid) t.live_rev
let live_entries t = List.rev t.live_rev
let size t = List.length t.live_rev
let n_added t = t.n_added
let n_evicted t = t.n_evicted
let n_swept t = t.n_swept
let n_duplicate t = t.n_duplicate
let n_cited t = t.n_cited
let n_pinned t = t.n_pinned
let policy_name t = t.policy.p_name
let holds t cid = List.exists (fun e -> e.e_cid = cid) t.live_rev
let was_retired t cid = Hashtbl.mem t.gone cid

(* Register a learned constraint. The id must be one [Learned.introduce] or
   [Pb_analysis.introduce] just handed back, and registering it is what transfers I-X2's
   obligation from the caller to this database.

   Rejects an id this database has already seen, in either direction: a repeat while live
   would put one id in the list twice and [retire] would delete it twice, and a repeat
   after retirement is a caller reusing a dead id. Both are [Double_delete] because both
   end in one. *)
let add t ~cid ~(row : Learned.t) ~lbd ~origin =
  if holds t cid then
    raise
      (Double_delete
         (Printf.sprintf "retention: id %d is already held (origin %S)" cid origin));
  if Hashtbl.mem t.gone cid then
    raise
      (Double_delete
         (Printf.sprintf "retention: id %d was already retired and cannot be re-added" cid));
  let key = Learned.to_string row in
  (match Hashtbl.find_opt t.keys key with
  | Some _ -> t.n_duplicate <- t.n_duplicate + 1
  | None -> Hashtbl.replace t.keys key cid);
  let e =
    {
      e_cid = cid;
      e_lbd = lbd;
      e_size = List.length (Learned.lits row);
      e_seq = t.next_seq;
      e_key = key;
      e_origin = origin;
    }
  in
  t.next_seq <- t.next_seq + 1;
  t.n_added <- t.n_added + 1;
  t.live_rev <- e :: t.live_rev;
  e

(* --------------------------------------------------------------- I-X3: citations *)

(* Record that [cid] is referenced by something still live -- a trail entry whose reason
   is this learned constraint, which is what I-X3 is about. [by] is for the message.

   M2-L4 wrote this with NO caller in lib/, because no learned constraint propagated and
   so no trail entry could name one -- a guard written before the thing it guards, which
   is the only time a guard is written against a bug that does not already exist.
   **M2-L12 is that caller**: [Search.register_learned] cites a constraint the moment it
   gives it a consumer, a global unit or a [Clause.Learned_clause] instance. [n_cited]
   counts calls, so the population is a measurement this module reports rather than a
   claim its header makes; on `width_sat_depth` it is 49 of 73. *)
let cite t ~cid ~by =
  t.n_cited <- t.n_cited + 1;
  Hashtbl.replace t.cited cid by

let uncite t ~cid = Hashtbl.remove t.cited cid

(* Release EVERY citation at once, for [Search.solve]'s end-of-search sweep alone.

   M2-L12. The guard [cite] installs is about the search: a trace line written by a
   global unit or by a registered learned-clause instance is RUP only while its
   constraint is live, so retiring a cited constraint MID-SEARCH is the fault the guard
   catches. When [dfs] has returned there are no more nodes, nothing will propagate
   again, and the constraints have to come off the page (I-X2) -- so the citations are
   released first and [retire_all] then sweeps with its other two guards, the double
   delete and the not-owned, still on.

   This is NOT [~unchecked]: that skips all three and exists only so test_retention.ml
   can perform the deletion the guards refuse and watch the checker's answer. Releasing
   is a statement about lifetime and is made once, in one place. *)
let release_all t = Hashtbl.reset t.cited
let cited_by t cid = Hashtbl.find_opt t.cited cid

(* ----------------------------------------------------------------- deletion *)

(* THE deletion path. Every `del` of a learned id in this project goes through here.

   Order is load-bearing and is the same order [Justify.wipe_level] keeps for the memo
   and the claim index: check everything FIRST, then emit, then update the tables in the
   same call. A refused deletion must leave no `del` on the page -- a proof carrying half
   a rejected retirement is worse than one carrying none, because the checker would then
   be the thing that noticed.

   [~unchecked:true] skips the guards and is the break. It exists so that
   [test_retention.ml] can perform the deletion the guards refuse and show what the
   CHECKER says about it, which is the only way to know the guard is catching something
   the checker would otherwise have had to. It is not reachable from the CLI. *)
let retire ?(unchecked = false) t ctx ~why (ids : Writer.cid list) =
  if ids <> [] then (
    if not unchecked then
      List.iter
        (fun cid ->
          (match Hashtbl.find_opt t.gone cid with
          | Some e ->
              raise
                (Double_delete
                   (Printf.sprintf
                      "retention: id %d (%s) is being deleted a SECOND time, now for %S. \
                       The first deletion is the one that owns it; a second `del id` on \
                       it is refused by the checker, and BAGUETTE_PROOF_AUDIT cannot see \
                       it because a second forget is a no-op (D-0045)."
                      cid e.e_origin why))
          | None -> ());
          if not (holds t cid) then
            raise
              (Not_owned
                 (Printf.sprintf
                    "retention: id %d is not held by this database, so deleting it for \
                     %S would be a delete from a second owner (M2-L4)"
                    cid why));
          match Hashtbl.find_opt t.cited cid with
          | Some by ->
              raise
                (Cited
                   (Printf.sprintf
                      "retention: id %d is still cited by %s, so retiring it for %S \
                       violates I-X3. Caught here rather than left for the checker, \
                       which would have said \"Trying to access constraint with ID %d \
                       that has already been deleted\" at the next citation."
                      cid by why cid))
          | None -> ())
        ids;
    Writer.delete_many (Justify.writer ctx) ids;
    List.iter
      (fun cid ->
        (match List.find_opt (fun e -> e.e_cid = cid) t.live_rev with
        | Some e -> Hashtbl.replace t.gone cid e
        | None -> ());
        t.live_rev <- List.filter (fun e -> e.e_cid <> cid) t.live_rev)
      ids)

(* Apply the policy. Returns the ids evicted, in the order they were deleted.

   The subset check is not defensive decoration: [policy] is the extension point, so a
   policy is the one place where an id that this database does not hold could enter the
   deletion path. [retire]'s [Not_owned] is where it lands. *)
let reduce t ctx =
  let victims = t.policy.p_evict (live_entries t) in
  (* M2-L12: A CITED CONSTRAINT IS NOT ELIGIBLE FOR EVICTION, so the cap is SOFT.

     Before M2-L12 this filter would have been dead code -- nothing propagated a learned
     constraint, nothing cited one, and a policy's choice was always performable. Now a
     unit is applied at every node and a wider clause has a registered instance, and a
     trace line either writes is RUP only while the constraint is on the page. A policy
     that named one would be naming a deletion the search cannot survive.

     Filtering here rather than letting [retire]'s [Cited] guard fire is the difference
     between a POLICY DECISION and a FAULT, and the two must not be confused. [Cited] is
     for a caller deleting something it should have known was in use; that is a bug and
     it raises. A cap that cannot be met because everything under it is in use is not a
     bug, it is the measurement M2-L12 owes D-0051 -- so it is counted ([n_pinned]) and
     reported, and [BAGUETTE_RETENTION=lbd:0] stays runnable instead of aborting the
     solver.

     The consequence is stated rather than buried: with [propagate_learned] on, NO
     policy can evict a constraint with a consumer, so the achievable cap is bounded
     below by the number of live consumers. That is exactly what the sweep in D-0051's
     successor record has to be read against. *)
  let evictable, pinned =
    List.partition (fun e -> not (Hashtbl.mem t.cited e.e_cid)) victims
  in
  t.n_pinned <- t.n_pinned + List.length pinned;
  let ids = List.map (fun e -> e.e_cid) evictable in
  if ids = [] then []
  else (
    retire t ctx ~why:(Printf.sprintf "eviction by %s" t.policy.p_name) ids;
    t.n_evicted <- t.n_evicted + List.length ids;
    ids)

(* The end-of-search sweep: retire whatever is still held, once, on every path.

   This is the function that replaced "delete every id ever introduced". It deletes what
   the database HOLDS, so an id the policy already evicted is not in the list and is not
   deleted twice. *)
let retire_all t ctx =
  let ids = live t in
  if ids = [] then []
  else (
    retire t ctx ~why:"end of search" ids;
    t.n_swept <- t.n_swept + List.length ids;
    ids)

(* A one-line summary for [--stats] and for a test that wants the shape of a run. *)
let to_string t =
  Printf.sprintf
    "%s: %d added, %d evicted, %d swept, %d live, %d duplicate, %d cited, %d pinned"
    t.policy.p_name t.n_added t.n_evicted t.n_swept (size t) t.n_duplicate t.n_cited
    t.n_pinned
