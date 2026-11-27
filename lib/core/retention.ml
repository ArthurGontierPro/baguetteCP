(* retention.ml: the learned-constraint database. It holds the proof id of every learned
   constraint the search introduced, it is the only code that deletes one (writing the
   matching `del` line), and its retention POLICY decides which constraints to evict while
   the search runs (M2-L4, which absorbed M2-T4, learned-clause deletion with its `del`).

   Consistency level: none, this is not a propagator. The records it rests on are D-0045,
   which found that a learned constraint tagged at the decision level it was learned at is
   deleted by the very backjump that follows learning it (the `wipe_level` finding that
   section 1 resolves); D-0044 and its amendments, under which the learned object is a PB
   inequality with the clause as its degree-1 case (and the fork that makes a learned PB
   row proof-only); D-0024, under which VeriPB 3.0 has no command that wipes a level, so
   lib/proof/writer.ml keeps a level tag per id and [Writer.wipe_level] imitates the wipe
   with explicit deletions; the invariants I-X2 (every constraint id is deleted exactly
   once) and I-X3 (a reason deleted from the proof is referenced by no live trail entry)
   of docs/INVARIANTS.md; and docs/PROOF-FORMAT.md section 5, on backtracking and
   deletion.

   The default policy is [tiered] (three LBD tiers, Glucose's schedule), chosen by D-0226
   on measurement: once an eviction also takes the instance out of the engine, [tiered]
   verified 25 answers of the tuning set where [keep_all] verified 20, and the peak memory
   of a run that times out fell to 0.6 to 0.7 times [keep_all]'s. `BAGUETTE_RETENTION`
   selects another policy (`off` or `keep_all`, `fifo:N`, `lbd:N`, `tiered:PARAMS`); `off`
   gives back the proofs written before D-0226 byte for byte. Section 2 gives the
   measurements that led there in the order they were taken. The first three chose or
   kept [keep_all] as the default (D-0051, D-0139), and what they say about the default
   is history.

   ===========================================================================
   1. WHO OWNS A LEARNED CONSTRAINT'S LIFETIME
   ===========================================================================

     **This database owns it, alone. A backjump cannot be a co-owner, and since M2-L4
     that is a property of the code rather than a property of the call sites.**

   D-0045 asked for this to be settled BEFORE any choice between LBD and activity. The
   argument is three steps and each one is checkable:

   1. [Writer.wipe_level l] deletes exactly the set {id | tag(id) >= l}
      (lib/proof/writer.ml, and D-0024 is why it is that set and not "everything derived
      since"). It is the only bulk deleter in the tree.
   2. A learned id is tagged 0. [Learned.introduce] and [Pb_analysis.introduce] both emit
      inside [Justify.with_level ctx 0], which moves the writer's level FOR REAL, so the
      tag and the emitted proof agree (I-X3). M2-L1 (the learned-constraint type and its
      introduction) measured the alternative: tagged at the conflict level, the backjump
      deletes it and the next citation is "Trying to access constraint with ID 3 that has
      already been deleted".
   3. Levels are non-negative ([Writer.set_level] rejects a negative), so a tag of 0 is
      reached by [wipe_level l] only at l = 0, and **[Writer.wipe_level] refuses l = 0**
      with an [invalid_arg] naming this module. Before M2-L4 that was a fact about
      [Search]'s four call sites, all of which pass a decision level; a fifth call site
      passing 0 would have made the backjump a second owner silently. It is now a fact
      about the writer.

   So there is exactly one deleter of a learned id, and it is [retire] below. Everything
   else in this module routes through it (eviction, the end-of-search sweep, and the test
   harness alike), which is what makes "deleted exactly once" (I-X2) a property of one
   function with one membership test rather than of an argument about call order.

   **The RUNTIME side has the same owner (D-0226).** A learned constraint with a
   propagator is in two places: its id on the page, and its instance in the engine.
   [Engine.add] hands the gated instance the function that removes it
   ([Propagator.inst_attach]), [gate] keeps that function, and [reduce] calls it in the
   same step that turns the gate off and retires the id. The engine holds a gated instance
   on this database's behalf and for exactly as long as this database holds its id; no
   other caller can remove it (the function is reachable only from the gate), and the
   engine never removes anything on its own. Under [keep_all] there is no gate, so nothing
   is ever removed and the proof is the one written before D-0226. Before D-0226 only the
   id ended at an eviction: the engine kept the instance until the end of the run,
   switched off by [gate] but with every closure and byte of the propagator.

   ### The double-delete this prevents is not the backjump's

   D-0045's addendum warns about the policy and the backjump both wanting a learned id
   gone, and step 3 above closes that off. The double-delete that would really have
   happened is nearer home, and it is worth naming because it is the shape a reader will
   reintroduce.

   Before M2-L4, [Search.solve] retired learned ids from [stats.learned_rev], the list of
   every id ever introduced. A policy that evicts mid-search and leaves that list alone
   gives two deletions of one id from ONE owner: the end-of-search sweep repeating what
   the eviction already did. [stats.learned_rev] is now an audit trail and nothing reads
   it to delete; the sweep is [retire_all], which deletes what this database still HOLDS.
   The distinction between "introduced" and "held" is the whole fix.

   It matters that the checker catches this and not only our audit, because the audit
   cannot: a second [Writer.forget] is a no-op, so [BAGUETTE_PROOF_AUDIT=1]'s live-set
   check cannot see a double delete at all (D-0045's closing paragraph). What sees it is
   `del id` on an already-deleted id, which 3.0.2 refuses, and [test_retention.ml]
   performs that break rather than citing it.

   ===========================================================================
   2. THE POLICY, AND THE MEASUREMENTS THAT CHOSE IT
   ===========================================================================

   The default is [tiered] since D-0226. Four measurements led there. Each is stated
   below with how it was taken, because a figure in this repository that says only what
   it is has twice turned out to be wrong.

   (a) M2-L4, 2026-09-18, on a suite whose largest learned database held 73 constraints.
       LBD does not discriminate, and every eviction costs proof bytes and checker time
       while saving neither, so D-0051 made [keep_all] the default.
   (b) M2-L12, the same day, once learned constraints propagate (M2-L12 for the clause,
       M2-L13 for the PB row). The same verdict for a new reason: the constraints that
       propagate are cited, and a policy may not evict a cited constraint.
   (c) M10-search-strategy-T4 (D-0139), on models that learn 10^4 to 10^5 constraints.
       With a detachable consumer ([gate]) and three LBD tiers ([tiered]) a policy can
       act. On the codes models it removes most of the propagation cost at an equal
       search; on a Challenge subset it buys no answer, and the default stayed [keep_all]
       (D-0139 section 6). D-0202 then found [tiered] a wash on the codes set.
   (d) D-0221 measured [tiered] on the tuning set and on 42 former heap refusals: one
       verified answer more of 200, but 6 refusals of 42 against 2, because an evicted
       constraint kept its bytes ([gate] kept the instance's closures and the engine kept
       the instance). D-0226 made an eviction take the instance out of the engine,
       re-measured the question, and made [tiered] the default; [default]'s comment has
       the numbers and D-0226's record the table.

   The activity [tiered] ranks its middle tier by is use ([e_used], whether the gated
   instance propagated), and [fifo] below is the plain age policy.

   ### LBD, and why it did not discriminate on the first suite

   LBD, the number of distinct decision levels the minimised clause's literals sit at, is
   computable at derivation time from the cut alone and needs no runtime participation,
   which made it the one of the two candidates that carried information at all while no
   learned constraint propagated. [Learn.lbd] computes it, after minimisation (see its
   comment for why the order matters).

   Measured over all 39 models, 2026-09-18, by running the solver with `--stats` and
   reading the `stats: lbd` histogram ([Search.stats_lbd]):

   | LBD | learned clauses |
   |---|---|
   | 1 | 72 |
   | 2 | 16 |
   | >= 3 | **0** |

   That is 88 clauses in all, the same denominator lib/core/pb_analysis.ml's header
   carries for the conversion rate, arrived at independently here. On `width_sat_depth`,
   the only model with a search deep enough to matter, **all 49 learned clauses have LBD
   1** and every one of them is a UNIT clause. The maximum LBD anywhere in that suite was
   2.

   Two consequences, both still in the code:

   - **[lbd] has no glue exemption.** Glucose keeps every clause with LBD <= 2 forever;
     on that suite the exemption would have retained 100% of what was learned. A
     parameter whose only measured value is "never fires" is a parameter exercised by
     nothing, which is this project's signature defect, so [lbd] has no [glue] argument.
     [tiered]'s CORE tier is that exemption, added by D-0139 once models that produce
     LBD >= 3 were measured.
   - **LBD is the ranking key; the CAP is the budget, and the cap is what fires.** With
     LBD tied everywhere on that suite, the tie-break (age, oldest evicted first) does the
     work. That is stated rather than hidden: a reader who sees [lbd] evicting in age
     order on a small model should know it is the tie-break and not a bug.

   ### (a) On a small database, eviction costs bytes and buys nothing (D-0051)

   Every cap measured made the proof larger and its check about 10% slower and saved
   neither, so D-0051 made [keep_all] the default. That refuted the expectation written
   before the numbers, and the order is recorded on purpose. The expectation was: a
   learned constraint costs nothing in search (at the time nothing propagated it) and a
   `del` line to retire, so eviction cannot save proof bytes; but every live constraint
   is one the checker's unit propagation walks on every subsequent `rup`, and this proof
   is almost all `rup` lines, so eviction should buy verification time.

   Measured on `width_sat_depth` (73 learned constraints, the only shipped model that
   learns enough for a cap to fire), 2026-09-18, by solving with `BAGUETTE_RETENTION=<p>`
   and then running the checker `scripts/checker.sh` resolves (VeriPB 3.0.2) over the
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

   So [keep_all] became the default: the machinery was built, named, swappable, exercised
   and measured, and left off because the measurement said off. Turning it on then would
   have been choosing a policy by citation, which the text of M2-L4's row forbids.

   What would change that verdict, stated so the next session does not have to re-derive
   it: the benefit term is per-`rup` propagation over the live database and it grows with
   database size, while the cost term is `del` rules and grows with the number of
   evictions. At 73 constraints the cost term wins. Re-run the table above on a model
   whose learned database is an order of magnitude larger, and if the crossover is found,
   `lbd:<cap>` is one environment variable away and nothing else has to change.

   A last note on the cap sweep, because it settles something the row worried about:
   **the proof verifies at every cap, including `lbd:0`, which deletes each learned
   constraint on the line after it is introduced.** Nothing in this proof depended on a
   learned constraint still being live, consistent with no learned constraint being cited
   at the time, and that is why eviction was safe here at all. It would NOT be safe in a
   solver whose later `rup` lines leaned on a learned unit to propagate, and that is a
   constraint on the successors of M2-L6 (PB conflict analysis) rather than a property of
   retention in general: deleting is free in a plain solver and is not free in a
   proof-logging one.

   ### (b) Once learned constraints propagate, the same verdict for a new reason (M2-L12)

   With propagation on, eviction still only adds `del` lines, because the constraints that
   propagate are cited and [reduce] refuses to evict them, and the ones it may evict do
   not propagate.

   D-0051 had said the verdict reverses "when a learned constraint is actually
   propagated", and (a) says eviction "would NOT be safe in a solver whose later `rup`
   lines leaned on a learned unit to propagate". M2-L12 built exactly that solver: a unit
   learned clause is applied at every node and a wider one is a registered
   [Clause.Learned_clause] instance. So the table was re-run rather than inherited, on
   the same model, the same four columns, with the same method (2026-09-18).

   First, the OLD column reproduced EXACTLY (`off` 48145 bytes / 124 `del`, `lbd:16`
   48658 / 181, `lbd:0` 48793 / 196, all VERIFIED), which is what makes the new one worth
   reading. `BAGUETTE_PROPAGATE_LEARNED=off` is the build that produces it.

   With propagation ON, on `width_sat_depth` (73 learned constraints, 49 of them cited):

     | policy   | evicted | eviction refused | .pbp bytes | `del` | nodes | checker  |
     |----------|---------|------------------|------------|-------|-------|----------|
     | off      |       0 |                0 |      48145 |   124 |    99 | VERIFIED |
     | lbd:16   |      16 |             1397 |      48289 |   140 |    99 | VERIFIED |
     | fifo:8   |      20 |             1745 |      48325 |   144 |    99 | VERIFIED |
     | lbd:0    |      24 |             2125 |      48361 |   148 |    99 | VERIFIED |

   **The verdict is unchanged and the ARGUMENT for it is not.** D-0051's reason was
   "activity is the constant zero". That reason became false: 49 of the 73 constraints
   have a consumer. The reason `keep_all` still won is the new one:

     1. **The constraints with activity are exactly the ones eviction may not touch.**
        [reduce] below refuses to evict a cited constraint, so the achievable cap is
        bounded below by the number of live consumers: at `lbd:0`, which asks for an
        empty database, 24 of 73 go and 49 stay. Eviction cannot reduce the work the
        globals do, because the globals are what pins them.
     2. **What it CAN evict has no activity**, being the uncited remainder (duplicates
        and M2-L6 PB rows with no runtime instance), so evicting it saves no propagation
        and only adds `del` lines. Bytes and `del` rules still rise monotonically with
        eviction, exactly as before.
     3. **The tree is the same size at every cap** (99 nodes in all four rows), which is
        the direct measurement that eviction is buying nothing here.

   So `keep_all` stood, and D-0051's "what would reverse this" was spent. Do not cite it
   as "retention does not help while nothing propagates a learned constraint", because
   something does. Cite it as: retention does not help while the constraints that
   propagate are the ones a policy may not evict, and the ones it may evict do not
   propagate. What would reverse THAT is a database large enough for the uncited
   remainder to dominate, or a consumer cheap enough to be worth dropping, and the sweep
   above is re-runnable with two environment variables.

   The safety note of (a) reads the other way round since M2-L12. The proof still
   verifies at every cap, but no longer because nothing leans on a learned constraint: it
   verifies because [reduce] refuses to delete the ones that are leaned on. The citation
   guard does the work that the absence of citations used to do for free.

   ### (c) On databases of 10^4 to 10^5 constraints, a policy can act (D-0139)

   With a consumer that can be switched off ([gate]), three LBD tiers ([tiered]), and an
   eviction that may detach a cited constraint unless the proof still needs it
   ([locked_instances]), a policy evicts for real. (a) and (b) were taken on a suite where
   the largest learned base was 73 constraints; M10-search-strategy-T4 (D-0139) took the
   question to the coding-theory models and fifteen Challenge instances, 1 170 s each,
   and three things came out, in order:

     1. **Nothing above could evict anything.** Every learned clause and PB row is cited
        for the whole search (M2-L12/L13), so `lbd:2000` on QR48 evicted 0 of 11 684 and
        refused 46.9 million proposals, 27 % slower than `off` because it sorted the
        database on every conflict to propose them. The cap was not soft but absent.
     2. **The cost the user saw is in PROPAGATING the base, not in holding it.** The
        learning rate falls 2 to 135 times from the start of a run to its end; with
        BAGUETTE_PROPAGATE_LEARNED=off and every clause still held, QR48 runs the same
        nodes in a tenth of the time.
     3. **With a detachable consumer ([gate], below) and three LBD tiers ([tiered]), a
        policy can act**, and on the codes it removes most of that cost at an EQUAL
        search (QR72 with proof 554 -> 296 s, the same conflicts). On the Challenge
        subset it buys conflicts and no answer, a third of them clauses learned again
        after eviction, and costs `bacp-22` a 2.3 times slower optimum; the checker's time
        does not move at an equal search, so "a smaller database for the checker" buys
        nothing measurable here.

   D-0139 therefore kept [keep_all] as the default, as a recommendation to M10-T5 (the
   task that measured the defaults; restarts and an activity heuristic change what
   eviction loses) rather than as D-0051's measurement. [gate] is wired by the search
   since main 36c1312 (the two `Engine.add` sites in lib/core/search.ml, cherry-picked
   from `wave45-retention-hook`), so `lbd`, `fifo` and `tiered` all evict for real; under
   [keep_all] the gate is the identity and the proof is byte-identical to the one before
   it. D-0139 has the tables, the binaries each was measured on, the lock rule's break,
   and the two late configurations. Section (d) of the list above says how [tiered]
   became the default.

   ### Determinism

   Two runs of one binary must write byte-identical output (the commit gate checks it with
   scripts/check_determinism.sh), and a learned database iterated in hash order is the
   specific way learning breaks it (lib/core/learn.ml says so, and this is the module
   that inherits the obligation). So [live_rev] is a LIST, in introduction order; [gone],
   [cited], [index] and [keys] are [Hashtbl]s that are only ever queried with
   [find_opt]/[mem] and never folded or iterated; and every policy below sorts on a key
   ending in [e_seq], which is unique, so no sort is left to compare equal elements.
   D-0139 kept that: [index] and the table [locked_instances] builds are lookup only, and
   [tiered] ranks on a key ending in [e_seq] like the others.
*)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer

(* Engine ids, keyed by their own value: they are small non-negative ints, so the
   identity is a hash and [Int.equal] the comparison, with no [caml_hash] and no
   polymorphic compare per probe (one of the hash-table costs the file-by-file review of
   learning removed, D-0191). Lookup only, like every table here. *)
module Int_tbl = Hashtbl.Make (struct
  type t = int

  let equal = Int.equal
  let hash x = x land max_int
end)

(* ------------------------------------------------------------------ entries *)

(* One learned constraint the database holds.

   [e_seq] is introduction order and is unique, which is what makes every sort here
   total.

   The duplicate MEASUREMENT below ([keys], [n_duplicate]) is keyed on the row's HASH
   ([Learned.hash]), which holds one word per row. Until D-0226 it was keyed on the row's
   canonical text, held in every entry and in [keys] for the whole run, 27 bytes per
   literal kept only to be compared (D-0218 section 5, the heap inventory that found it).
   M11-complexity-T4 (D-0152, which took the per-conflict scans out of search, analysis
   and retention) had tried keying on the row itself and reverted it because the table
   then held every row. *)
type tier = Core | Mid | Local

let tier_to_string = function Core -> "core" | Mid -> "mid" | Local -> "local"

(* The runtime consumer of a learned constraint, when the search handed it to [gate]: the
   engine instance [g_inst] and the switch that turns it off. A [gate]d constraint is the
   only kind of CITED constraint a policy may evict; see [gate] and [reduce]. (D-0139.) *)
type gate = {
  g_inst : int;
  mutable g_dead : bool;
  mutable g_leave : unit -> unit;
      (* What takes the instance out of the engine that holds it, handed over by
         [Engine.add] through [Propagator.inst_attach]; [ignore] before that and after it
         has been called (M21-memory-T3, the memory fixes of D-0226). *)
}

type entry = {
  e_cid : Writer.cid;
  e_lbd : int;
  e_size : int; (* terms in the row; 1 is a unit clause *)
  e_seq : int;
  e_origin : string;
  mutable e_tier : tier;
      (* D-0139. Set from [e_lbd] at [add] under [tiered] ([Local] under every other
         policy, which never reads it) and moved only by [tiered]: a [Mid] entry that was
         not used between two of its checks is demoted to [Local]. *)
  mutable e_used : bool;
      (* D-0139. The gated instance propagated or conflicted since the last reduction
         that looked at this entry -- the activity this solver can observe without a
         hook in conflict analysis (lib/core/analysis.ml is not this module's). Set only
         by [gate]'s wrapper, so an ungated entry is never "used". *)
  mutable e_gate : gate option;
}

let entry_cid e = e.e_cid
let entry_lbd e = e.e_lbd
let entry_seq e = e.e_seq
let entry_origin e = e.e_origin
let entry_tier e = e.e_tier

(* ----------------------------------------------------------------- policies *)

(* A policy is a function from the live database to the entries to evict. That is the
   whole of the swappable axis, and it is a function rather than a threshold for the
   reason D-0044 gives for the reduction rule and the stopping criterion: the interesting
   ones are not parameterisations of each other.

   The argument is the live set in INTRODUCTION order (oldest first), and the result must
   be a subset of it. [reduce] checks the subset property rather than trusting it, because
   a policy that returned an id the database does not hold would be a delete from a second
   owner -- the exact failure this module exists to prevent, arriving through the one door
   that is meant to be extensible.

   The function comes in two halves, [due] and [evict], and the pair is something a
   policy CONSTRUCTS ([p_new]) per database (both since D-0139):

   - [due] answers from two counters whether [evict] has anything to do, so the common
     call to [reduce], which runs once per learned constraint, is O(1). Before D-0139
     [reduce] materialised the whole live list ([List.rev]) on every call, under
     [keep_all] too, to hand it to a function that returned [], which was O(n) per
     conflict for nothing at 35 000 held constraints. For [fifo] and [lbd], [due] is
     exactly their old "n <= cap then []" test, so what they evict is unchanged.
   - [p_new] gives each database its own schedule state. [tiered] carries a reduction
     count and the point at which it next reduces, and a policy VALUE is shared by every
     solve of a config, so the state cannot live in the value.
   - [p_detaches] says whether the policy may ever evict, i.e. whether [gate] has to wrap
     anything. [keep_all] says no, and [gate] then returns the instance unchanged: a
     [keep_all] build runs the very closure it ran before D-0139. *)
type evictor = {
  due : added:int -> live:int -> bool;
  evict : added:int -> entry list -> entry list;
}

(* ------------------------------------------------- three LBD tiers (M10-T4, D-0139)

   The scheme of Glucose (Audemard and Simon, IJCAI 2009) and of its three-tier successor
   (Oh, SAT 2015, COMiniSatPS; the scheme Kissat and CaDiCaL kept). Each learned
   constraint is in one tier, set from its LBD when it is added:

   - CORE: LBD <= [core]. A "glue" clause links few decision blocks and is kept for the
     whole search. Never proposed.
   - MID (Oh's tier 2): [core] < LBD <= [mid]. Kept while it is used. Every [mid_every]
     learned constraints, a mid entry not used since the previous such check is demoted
     to local, and every mid entry's use flag is cleared.
   - LOCAL: everything else, and the demoted. At a local reduction the half of the local
     tier ranked worst is proposed; the k-th reduction (k = 1, 2, ...) schedules the next
     one [first + k * inc] learned constraints later -- Glucose's schedule, first = 2000
     and inc = 300 in Glucose 2 and 3. Worst = unused before used, then higher LBD, then
     older; the use flags of the local tier are cleared after the ranking.

   "Used" is [e_used]: the gated instance propagated or conflicted since the entry's last
   check. Glucose bumps on participation in conflict ANALYSIS, which this module cannot
   observe without a hook in lib/core/analysis.ml; a propagation is the nearest signal
   the instance itself gives, and it is a superset (every clause that takes part in an
   analysis propagated or conflicted first). An ungated entry -- the build where the
   search does not call [gate] -- is never used after its first check, which is the
   honest reading: nothing observed it working.

   A NEW entry starts USED, CaDiCaL's rule (a learned clause is created with its `used`
   flag set): at the first check it meets it ranks with the used, whatever it did.
   Without that grace a reduction ranks a clause learned one conflict earlier -- which has
   had no chance to propagate -- with the unused, first in line; [reduce] runs right
   after [add], before the search has backtracked, so the clause just learned would be
   the likeliest victim of the reduction its own [add] triggered.

   The schedule counts LEARNED CONSTRAINTS, not conflicts: [reduce] sees one call per
   [add], and a conflict that also learns a PB row (M2-L6) adds two. D-0139 records the
   pb-learned share per instance.

   The LBD is the one computed at derivation ([Learn.lbd], after minimisation) and is not
   updated later. Glucose recomputes it when a clause takes part in an analysis; that is
   the same missing hook, recorded rather than approximated. A PB row carries the LBD of
   the conflict it came from (lib/core/search.ml says why); RoundingSat's per-row LBD
   (Elffers and Nordstrom, IJCAI 2018) would need levelled literals out of
   lib/core/pb_analysis.ml, and D-0139 has the count of PB rows that would be scored. *)
type tier_params = { core : int; mid : int; first : int; inc : int; mid_every : int }

let default_tier_params =
  { core = 2; mid = 6; first = 2000; inc = 300; mid_every = 10000 }

let tier_of_lbd prm lbd =
  if lbd <= prm.core then Core else if lbd <= prm.mid then Mid else Local

type policy = {
  p_name : string;
  p_new : unit -> evictor;
  p_detaches : bool;
  p_tiers : tier_params option;
}

let name p = p.p_name

(* Off: everything is retained until the search ends, the behaviour before M2-L4. It is
   the "policy off" side of test (c) in test/unit/test_retention.ml (.pbp bytes with the
   policy off and on), and the control every measurement here is taken against. *)
let keep_all =
  {
    p_name = "keep-all";
    p_new =
      (fun () ->
        { due = (fun ~added:_ ~live:_ -> false); evict = (fun ~added:_ _ -> []) });
    p_detaches = false;
    p_tiers = None;
  }

(* The orders [fifo] and [lbd] rank by, over ints with [Int.compare] (the polymorphic
   [compare] was called per comparison until M11-complexity-T4, D-0152, the fix for item
   R3 of D-0140's inventory of costs that grow with the run). [by_seq] is total because
   [e_seq] is unique. [reduce] hands [evict] the live list
   oldest first, i.e. already in [by_seq] order ([add] appends with the next [e_seq], and
   [retire] only filters), so [fifo] checks that in one pass and sorts only a list that
   is not; [List.sort] being stable and the order total, the sorted list is the list. *)
let by_seq a b = Int.compare a.e_seq b.e_seq

let rec sorted_by_seq = function
  | a :: (b :: _ as rest) -> a.e_seq < b.e_seq && sorted_by_seq rest
  | [ _ ] | [] -> true

(* Evict oldest-first down to [cap]. It stands in for the activity policy M2-L4 was asked
   for: when it was written no learned constraint propagated, so every activity was
   identically zero, an activity ranking was a tie across the whole database, and the
   tie-break (age) was all that was left. Spelling it [fifo] says what it does instead of
   what it was named after. Since M2-L12 learned constraints do propagate, and the policy
   that ranks on use is [tiered] (its middle tier, [e_used]). *)
let fifo ~cap =
  {
    p_name = Printf.sprintf "fifo(cap=%d)" cap;
    p_new =
      (fun () ->
        {
          due = (fun ~added:_ ~live -> live > cap);
          evict =
            (fun ~added:_ live ->
              let n = List.length live in
              if n <= cap then []
              else
                List.filteri
                  (fun i _ -> i < n - cap)
                  (if sorted_by_seq live then live else List.sort by_seq live));
        });
    p_detaches = true;
    p_tiers = None;
  }

(* The [k] first elements of [List.sort cmp l], in that order, for a TOTAL [cmp] (every
   comparator here ends in [by_seq]). For a small [k] it takes them in one pass each, the
   next being the least element above the last one taken, which a total order makes the
   same element the sort puts there; past [first_k_passes] it sorts.

   Why: [lbd] asks for the [n - cap] worst of a database that is over its cap by one or a
   few, once per learned constraint, and sorting all [n] for them was most of its cost
   once [locked_instances] stopped dominating (M16-file-review-T3, D-0191). *)
let first_k_passes = 8

let first_k cmp k l =
  if k <= 0 then []
  else if k > first_k_passes then List.filteri (fun i _ -> i < k) (List.sort cmp l)
  else
    let least_above prev =
      List.fold_left
        (fun best x ->
          match prev with
          | Some p when cmp x p <= 0 -> best
          | _ -> ( match best with Some b when cmp b x <= 0 -> best | _ -> Some x))
        None l
    in
    let rec take i prev acc =
      if i = k then List.rev acc
      else
        match least_above prev with
        | None -> List.rev acc
        | Some x -> take (i + 1) (Some x) (x :: acc)
    in
    take 0 None []

(* The policy. Rank by LBD descending -- a higher LBD is a worse constraint, Glucose's
   direction -- and break ties by age, oldest first. Evict down to [cap].

   No glue exemption: on the suite it was measured on, the exemption never fired (header,
   section 2); [tiered]'s core tier is the policy that has one. The cap is the budget and
   the ranking decides who pays it. *)
let lbd ~cap =
  {
    p_name = Printf.sprintf "lbd(cap=%d)" cap;
    p_new =
      (fun () ->
        {
          due = (fun ~added:_ ~live -> live > cap);
          evict =
            (fun ~added:_ live ->
              let n = List.length live in
              if n <= cap then []
              else
                first_k
                  (fun a b ->
                    match Int.compare b.e_lbd a.e_lbd with 0 -> by_seq a b | c -> c)
                  (n - cap) live);
        });
    p_detaches = true;
    p_tiers = None;
  }

(* The three-tier policy; see the comment above [tier_params]. *)
let tiered ?(params = default_tier_params) () =
  let prm = params in
  if
    prm.core < 0 || prm.mid < prm.core || prm.first < 1 || prm.inc < 0
    || prm.mid_every < 1
  then
    invalid_arg
      "Retention.tiered: need 0 <= core <= mid, first >= 1, inc >= 0, mid_every >= 1";
  {
    p_name =
      Printf.sprintf "tiered(core<=%d,mid<=%d,first=%d,inc=%d,mid_every=%d)" prm.core
        prm.mid prm.first prm.inc prm.mid_every;
    p_new =
      (fun () ->
        let k = ref 0 in
        let next_local = ref prm.first in
        let next_mid = ref prm.mid_every in
        {
          due = (fun ~added ~live:_ -> added >= !next_local || added >= !next_mid);
          evict =
            (fun ~added live ->
              if added >= !next_mid then (
                List.iter
                  (fun e ->
                    if e.e_tier = Mid then (
                      if not e.e_used then e.e_tier <- Local;
                      e.e_used <- false))
                  live;
                next_mid := added + prm.mid_every);
              if added < !next_local then []
              else
                let local = List.filter (fun e -> e.e_tier = Local) live in
                let worst_first =
                  List.sort
                    (fun a b ->
                      match Bool.compare a.e_used b.e_used with
                      | 0 -> (
                          match Int.compare b.e_lbd a.e_lbd with
                          | 0 -> by_seq a b
                          | c -> c)
                      | c -> c)
                    local
                in
                List.iter (fun e -> e.e_used <- false) local;
                incr k;
                next_local := added + prm.first + (!k * prm.inc);
                let half = List.length local / 2 in
                List.filteri (fun i _ -> i < half) worst_first);
        });
    p_detaches = true;
    p_tiers = Some prm;
  }

(* The default is [tiered] with D-0139's parameters ([default_tier_params]), chosen by
   D-0226, an [AUTONOME] decision. Once an eviction took the instance out of the engine
   (D-0226 fix 1), the review's rule held on both of D-0221's sets: verified answers 20 to
   25 on the tuning set and 1 to 1 on the 42 heap cases, heap-budget refusals 3 to 2 and 1
   to 1, the peak RSS of a run that times out 0.67 and 0.59 times [keep_all]'s.
   `BAGUETTE_RETENTION=off` (or [keep_all]) is the default before it, exactly.

   Before D-0226 the default was KEEP-ALL, on the measurement in the header's section 2
   (a): on a database of 73 constraints every cap measured cost proof bytes and
   verification time and saved neither, and a policy turned on against its own
   measurement would have been a policy chosen by citation. [lbd ~cap:16] was what the
   default would have been had the crossover the header describes been found, and
   `BAGUETTE_RETENTION=lbd:16` runs it without changing a line;
   test/unit/test_retention.ml runs it end to end through the checker, which is where the
   [lbd] eviction path is exercised. D-0139 then re-measured the question on the codes set
   and a Challenge subset, with [tiered], and left the decision to M10-T5. *)
let default = tiered ()

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
  ev : evictor; (* [policy.p_new ()], this database's own schedule state *)
  mutable live_rev : entry list; (* newest first *)
  mutable n_live : int; (* [List.length live_rev], kept so [size] and [due] are O(1) *)
  index : (Writer.cid, entry) Hashtbl.t;
      (* cid -> its entry, for the ids in [live_rev] exactly. Lookup only, never iterated
         (determinism, header). Before D-0139 [holds] walked [live_rev], which made [add]
         O(n) and a search O(n^2) in learned constraints. *)
  mutable store : Store.t option;
      (* D-0139. The store the gated instances run on, handed over by [gate]; [reduce]
         reads its trail to find the LOCKED entries. [None] until something is gated. *)
  mutable last_conflict : int;
      (* D-0139. Engine id of the most recent gated instance whose run returned
         [Conflict], or -1. See [locked_instances] for why it is protected. *)
  mutable n_detached : int;
  mutable n_locked : int;
  mutable n_reductions : int;
  mutable next_seq : int;
  mutable n_added : int;
  mutable n_evicted : int;
  mutable n_swept : int;
  mutable n_duplicate : int;
  mutable n_cited : int;
  mutable n_pinned : int;
      (* Evictions the policy PROPOSED and [reduce] did NOT perform, because the
         constraint had a live consumer (M2-L12). Proposals and not distinct constraints:
         [reduce] runs once per learned constraint and an over-cap policy re-proposes the
         same pinned entries every time, so this number is much larger than the
         database. That is what makes it the right counter for "how hard is the policy
         pushing against the citations", which is the question the header's sweep (b)
         asks. See [reduce]. *)
  gone : (Writer.cid, entry) Hashtbl.t;
      (* Retired by this database: cid -> the entry it was. Lookup only, never iterated
         (determinism, header). It is what turns a second deletion into an exception
         instead of a silently accepted no-op. *)
  cited : (Writer.cid, string Lazy.t) Hashtbl.t;
      (* cid -> what cites it, for the live citation. Lookup only. See [cite]. The text
         is LAZY (D-0152, item S2 of D-0140's inventory): it names every literal of the
         citing instance and is read only by the [Cited] message and [cited_by], so it is
         rendered when one of them asks, from the same values, and never otherwise. *)
  keys : (int, Writer.cid) Hashtbl.t;
      (* The row's hash ([Learned.hash], D-0226; its canonical TEXT until then) -> the
         first id that stated it. Lookup only, and MEASUREMENT only: it feeds
         [n_duplicate] and no policy reads it. M1-T59, which found two proofs emitting a
         byte-identical `rup` twice, judged duplicate lines harmless within one proof; a
         retention policy that evicts and lets the same clause be re-learned is how they
         stop being harmless, so the count is kept where a later row can see it. *)
}

let create ?(policy = default) () =
  {
    policy;
    ev = policy.p_new ();
    live_rev = [];
    n_live = 0;
    index = Hashtbl.create 64;
    store = None;
    last_conflict = -1;
    n_detached = 0;
    n_locked = 0;
    n_reductions = 0;
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
let size t = t.n_live
let n_added t = t.n_added
let n_evicted t = t.n_evicted
let n_swept t = t.n_swept
let n_duplicate t = t.n_duplicate
let n_cited t = t.n_cited
let n_pinned t = t.n_pinned
let n_detached t = t.n_detached
let n_locked t = t.n_locked
let n_reductions t = t.n_reductions
let entry_of t cid = Hashtbl.find_opt t.index cid
let policy_name t = t.policy.p_name
let holds t cid = Hashtbl.mem t.index cid
let was_retired t cid = Hashtbl.mem t.gone cid

(* A PROGRESS TRACE, measurement only (D-0139). Every [!trace_every] constraints added,
   one stderr line with what the database holds and the process CPU time, so that a run's
   learning RATE can be read at its start and at its end -- the per-node slowdown the
   codes models show as the base grows is a slope, and a single end-of-run total cannot
   show a slope. 0 (the default) prints nothing; bin/main.ml sets it from
   BAGUETTE_RETENTION_TRACE. stderr only, so the determinism gate and the stdout-identity
   lane never see it. *)
let trace_every = ref 0

(* Under BAGUETTE_RETENTION_TRACE_HEAP=1, each trace line also carries the live words of
   the heap after a full major collection, which is how D-0226 measured what an eviction
   frees. A full collection per trace line: measurement only, never a default. *)
let trace_heap = ref (Sys.getenv_opt "BAGUETTE_RETENTION_TRACE_HEAP" = Some "1")

let trace t =
  if !trace_every > 0 && t.n_added mod !trace_every = 0 then
    Printf.eprintf "retention-trace: added=%d live=%d evicted=%d pinned=%d cpu=%.2f%s\n%!"
      t.n_added t.n_live t.n_evicted t.n_pinned (Sys.time ())
      (if !trace_heap then (
         Gc.full_major ();
         Printf.sprintf " live_words=%d" (Gc.stat ()).Gc.live_words)
       else "")

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
  let key = Learned.hash row in
  (match Hashtbl.find_opt t.keys key with
  | Some _ -> t.n_duplicate <- t.n_duplicate + 1
  | None -> Hashtbl.replace t.keys key cid);
  let e =
    {
      e_cid = cid;
      e_lbd = lbd;
      e_size = List.length (Learned.lits row);
      e_seq = t.next_seq;
      e_origin = origin;
      e_tier =
        (match t.policy.p_tiers with Some prm -> tier_of_lbd prm lbd | None -> Local);
      e_used = t.policy.p_tiers <> None (* the grace above [tier_params] *);
      e_gate = None;
    }
  in
  t.next_seq <- t.next_seq + 1;
  t.n_added <- t.n_added + 1;
  t.live_rev <- e :: t.live_rev;
  t.n_live <- t.n_live + 1;
  Hashtbl.replace t.index cid e;
  trace t;
  e

(* --------------------------------------------------------------- I-X3: citations *)

(* Record that [cid] is referenced by something still live -- a trail entry whose reason
   is this learned constraint, which is what I-X3 is about. [by] is for the message.

   The search cites a constraint the moment it gives it a consumer:
   [Search.register_learned] for a global unit or a [Clause.Learned_clause] instance,
   [Search.register_learned_pb] for a learned PB row's instance. [n_cited] counts calls,
   so the population is a measurement this module reports rather than a claim its header
   makes; on `width_sat_depth` it is 49 of 73.

   M2-L4 wrote this guard with NO caller in lib/, because no learned constraint
   propagated and so no trail entry could name one: a guard written before the thing it
   guards, which is the only time a guard is written against a bug that does not already
   exist. M2-L12 added the first caller. *)
let cite_lazy t ~cid ~(by : unit -> string) =
  t.n_cited <- t.n_cited + 1;
  Hashtbl.replace t.cited cid (Lazy.from_fun by)

let cite t ~cid ~by = cite_lazy t ~cid ~by:(fun () -> by)
let uncite t ~cid = Hashtbl.remove t.cited cid

(* Release EVERY citation at once, for [Search.solve]'s end-of-search sweep alone.

   The guard [cite] installs is about the search (M2-L12): a trace line written by a
   global unit or by a registered learned-clause instance is RUP only while its
   constraint is live, so retiring a cited constraint MID-SEARCH is the fault the guard
   catches. When the search has returned there are no more nodes, nothing will propagate
   again, and the constraints have to come off the page (I-X2) -- so the citations are
   released first and [retire_all] then sweeps with its other two guards, the double
   delete and the not-owned, still on.

   This is NOT [~unchecked]: that skips all three and exists only so test_retention.ml
   can perform the deletion the guards refuse and watch the checker's answer. Releasing
   is a statement about lifetime and is made once, in one place. *)
let release_all t = Hashtbl.reset t.cited
let cited_by t cid = Option.map Lazy.force (Hashtbl.find_opt t.cited cid)

(* ------------------------------------------- a consumer that CAN be detached (D-0139)

   [gate] is what lets a policy evict a constraint that has a consumer. The search hands
   the instance over before [Engine.add]; what comes back is the same instance behind a
   switch:

   - while the switch is on it runs and advises exactly as before, and records whether a
     run propagated (the trail grew) or conflicted -- [e_used], the activity [tiered]
     ranks on -- and, for a conflict, which instance it was ([last_conflict]);
   - once [reduce] turns it off, [run] is [Fixpoint] without calling the propagator and
     [advise] is [false], so the engine never queues it again. Both are what a
     propagator over a constraint that is no longer in the model may say: deleting a
     learned constraint is sound, it is redundant by construction.

   WHEN a gated constraint may be evicted is the proof's question, and the answer is
   [locked_instances] below. Since D-0226 the eviction also takes the instance out of the
   engine ([g_leave], handed over by [Engine.add] through [Propagator.inst_attach]): its
   slot, its wake entries and, with them, every closure over the propagator become
   garbage. Until then the engine kept the switched-off instance for the rest of the run,
   with all its bytes (D-0221 section 5).

   Under [keep_all] ([p_detaches = false]) the instance is returned UNCHANGED, so a
   [keep_all] build runs the very closures it ran before this function existed.

   Why it is needed: since M2-L12 every learned clause of two or more literals is a
   registered [Clause.Learned_clause] instance and every learned PB row a [Pb] instance,
   and both are [cite]d for the whole search, so [reduce] refuses to evict them. Without
   a gate, on the codes models and the Challenge subset D-0139 measured, `lbd:N` and
   `fifo:N` evict NOTHING and only count refusals ([n_pinned]): the cap is soft to the
   point of being absent. *)
let gate t store ~cid (inst : Propagator.instance) : Propagator.instance =
  if not t.policy.p_detaches then inst
  else
    match Hashtbl.find_opt t.index cid with
    | None ->
        raise
          (Not_owned
             (Printf.sprintf
                "retention: [gate] was handed instance #%d for id %d, which this \
                 database does not hold; register the constraint with [add] first"
                inst.Propagator.id cid))
    | Some e ->
        let g = { g_inst = inst.Propagator.id; g_dead = false; g_leave = ignore } in
        e.e_gate <- Some g;
        t.store <- Some store;
        let inner_run = inst.Propagator.run
        and inner_advise = inst.Propagator.inst_advise in
        let run s =
          if g.g_dead then Propagator.Fixpoint
          else
            let before = Store.trail_length s in
            match inner_run s with
            | Propagator.Conflict _ as r ->
                e.e_used <- true;
                t.last_conflict <- g.g_inst;
                r
            | Propagator.Fixpoint as r ->
                if Store.trail_length s <> before then e.e_used <- true;
                r
        in
        {
          inst with
          Propagator.run;
          inst_advise = (fun s v -> (not g.g_dead) && inner_advise s v);
          inst_attach = (fun leave -> g.g_leave <- leave);
        }

(* The engine ids whose constraint the proof may still need, at the moment of a
   reduction. Two kinds, and the argument for each is the whole of why eviction of a
   gated constraint is sound in THIS proof system:

   1. THE PROPAGATOR OF A TRAIL ENTRY STILL ON THE TRAIL (Glucose's "locked" clause,
      generalised from the reason of the current assignment to every entry). lib/core/
      trace.ml is LAZY: a branch writes its trace lines when it fails, by walking the
      trail, and a line for an entry propagated by a learned instance is `rup` against
      that learned constraint. So the constraint must be on the page for as long as the
      entry can still be traced, which is for as long as it is on the trail. A backjump
      pops it and [Writer.wipe_level] deletes any line it got; after that nothing can
      write a line citing the constraint through that entry.
   2. THE MOST RECENT GATED CONFLICT ([last_conflict]). [reduce] is called from inside
      conflict handling, after the learned clause is on the page and BEFORE the PB path
      (lib/core/search.ml's [pb_at_conflict]) resolves the conflicting instance's row. If
      that instance is gated it is the last gated one to have returned [Conflict] (the
      engine stops at the first conflict), so protecting it is exact; when the conflict
      came from elsewhere, protecting a stale id costs one entry one reduction.

   Every other reference to a learned id is a line already written (its validity does
   not depend on its premises staying -- VeriPB's database keeps derived constraints) or
   a level-0 unit, which [tiered] never proposes (LBD 1) and which is cited without a
   gate, so no policy can evict it. Under [BAGUETTE_PROOF_AUDIT] and the checker, every
   proof the D-0139 hook build emitted over the 173 test models verified, under five
   schedules down to a reduction per learned constraint. Half 1 is load-bearing: without
   it `colour_unsat` is rejected ("Trying to access constraint with ID 175 that has
   already been deleted"). Half 2 reddens no model in the suite and is kept on the
   argument above; the unit lanes in test/unit/test_retention.ml pin both.

   The function is ASKED ONLY ABOUT [wanted], the gates of this reduction's victims, and
   answers with the subset of them that is locked: an id is locked iff it is
   [last_conflict] or the instance of an entry on the trail. It walks the trail testing
   each entry's instance against the few wanted ids, and stops once all of them are found
   locked. Before M16-file-review-T3 (D-0191) it put the instance of EVERY trail entry
   into a polymorphic table, one [caml_hash] and a growing table per entry, once per
   reduction: under `lbd:500` that was 20 % of 2017_opd_small_bibd_08_28_14's samples.
   For the ids [reduce] asks about the answer is the one the full table gave. *)
let locked_instances t (wanted : int list) =
  let want = Int_tbl.create 8 and locked = Int_tbl.create 8 in
  List.iter (fun id -> Int_tbl.replace want id ()) wanted;
  let lock id = if Int_tbl.mem want id then Int_tbl.replace locked id () in
  if t.last_conflict >= 0 then lock t.last_conflict;
  (match t.store with
  | None -> ()
  | Some s ->
      let n = Store.trail_length s in
      let i = ref 0 in
      while !i < n && Int_tbl.length locked < Int_tbl.length want do
        lock (Store.trail_entry s !i).Store.prop;
        incr i
      done);
  locked

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
   the checker would otherwise have had to. It is not reachable from the CLI.

   ONE pass over [live_rev] per call, not one per id. Looking each id up with [holds],
   [List.find_opt] and [List.filter] over the whole database, as this did until M6-T21
   (D-0136, the --time-limit overshoot traced to this sweep), is O(k n) for k ids out of
   n held, and the end-of-search sweep has k = n: at 12 071 learned clauses that was 4.3 s
   of a 120 s `--time-limit` stop, at 34 381 the bulk of a 46 s overshoot past 600 s. The
   one-pass version kept the guards, their order and their messages, the entry recorded
   in [gone] (the newest one holding the id, which is what [find_opt] over a newest-first
   list returned) and what is left in [live_rev]. *)
let retire ?(unchecked = false) t ctx ~why (ids : Writer.cid list) =
  if ids <> [] then (
    let wanted = Hashtbl.create 64 in
    List.iter (fun cid -> Hashtbl.replace wanted cid ()) ids;
    (* cid -> the newest held entry for it, for the ids of this call only. *)
    let held = Hashtbl.create 64 in
    List.iter
      (fun e ->
        if Hashtbl.mem wanted e.e_cid && not (Hashtbl.mem held e.e_cid) then
          Hashtbl.add held e.e_cid e)
      t.live_rev;
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
          if not (Hashtbl.mem held cid) then
            raise
              (Not_owned
                 (Printf.sprintf
                    "retention: id %d is not held by this database, so deleting it for \
                     %S would be a delete from a second owner (M2-L4)"
                    cid why));
          match cited_by t cid with
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
    Hashtbl.iter (fun cid e -> Hashtbl.replace t.gone cid e) held;
    t.live_rev <- List.filter (fun e -> not (Hashtbl.mem wanted e.e_cid)) t.live_rev;
    (* [index] and [n_live] follow [live_rev] (D-0139). [held] is exactly the set of ids
       in [ids] that [live_rev] held (and [add] refuses a repeat), so it is what left. *)
    Hashtbl.iter (fun cid _ -> Hashtbl.remove t.index cid) held;
    t.n_live <- t.n_live - Hashtbl.length held)

(* Apply the policy. Returns the ids evicted, in the order they were deleted.

   The subset check is not defensive decoration: [policy] is the extension point, so a
   policy is the one place where an id that this database does not hold could enter the
   deletion path. [retire]'s [Not_owned] is where it lands.

   Cost. The call is O(1) unless the policy is [due], which is what keeps the
   once-per-learned-constraint call off the profile (see [evictor], D-0139). When it is
   due it is O(n) in the live database (the [List.rev], the policy's pass, the
   partition), plus [locked_instances]' one trail walk (D-0191). Over a run that is O(n)
   per learned constraint, and n is the cap plus what is PINNED: a database whose pinned
   constraints keep growing past the cap (cited consumers without a gate) makes the run
   quadratic in them. Under `lbd:500` no lane instance ends with more than 526 live
   constraints (the end sweep's count), so there n stays near the cap. *)
let reduce t ctx =
  if not (t.ev.due ~added:t.n_added ~live:t.n_live) then []
  else
    let victims = t.ev.evict ~added:t.n_added (List.rev t.live_rev) in
    t.n_reductions <- t.n_reductions + 1;
    (* A CITED CONSTRAINT IS NOT ELIGIBLE FOR EVICTION, so the cap is SOFT (M2-L12).

       A learned unit is applied at every node and a wider learned clause has a
       registered instance, and a trace line either writes is RUP only while the
       constraint is on the page. A policy that named one would be naming a deletion the
       search cannot survive. (Before M2-L12 nothing propagated a learned constraint,
       nothing cited one, and this filter would have been dead code.)

       Filtering here rather than letting [retire]'s [Cited] guard fire is the difference
       between a POLICY DECISION and a FAULT, and the two must not be confused. [Cited] is
       for a caller deleting something it should have known was in use; that is a bug and
       it raises. A cap that cannot be met because everything under it is in use is not a
       bug, it is the measurement M2-L12 owes D-0051 -- so it is counted ([n_pinned]) and
       reported, and [BAGUETTE_RETENTION=lbd:0] stays runnable instead of aborting the
       solver.

       The consequence is stated rather than buried: with [propagate_learned] on, NO
       policy can evict a constraint with a consumer, so the achievable cap is bounded
       below by the number of live consumers. That is exactly what the header's sweep (b)
       has to be read against.

       D-0139 makes ONE exception, and it is the whole of what makes retention real with
       propagation on: a cited constraint whose only consumer is a [gate]d instance is
       eligible unless [locked_instances] names that instance. Evicting it turns the gate
       off and releases the citation BEFORE [retire], so [retire]'s [Cited] guard still
       means exactly what it meant. A cited constraint with no gate -- a global unit, or
       any consumer of a search that does not call [gate] -- is pinned as before. *)
    let locked =
      if List.exists (fun e -> e.e_gate <> None && Hashtbl.mem t.cited e.e_cid) victims
      then
        Some
          (locked_instances t
             (List.filter_map (fun e -> Option.map (fun g -> g.g_inst) e.e_gate) victims))
      else None
    in
    let evictable, pinned =
      List.partition
        (fun e ->
          if not (Hashtbl.mem t.cited e.e_cid) then true
          else
            match (e.e_gate, locked) with
            | Some g, Some l ->
                if Int_tbl.mem l g.g_inst then (
                  t.n_locked <- t.n_locked + 1;
                  false)
                else true
            | _ -> false)
        victims
    in
    t.n_pinned <- t.n_pinned + List.length pinned;
    let ids = List.map (fun e -> e.e_cid) evictable in
    if ids = [] then []
    else (
      List.iter
        (fun e ->
          match e.e_gate with
          | Some g when Hashtbl.mem t.cited e.e_cid ->
              g.g_dead <- true;
              (* D-0226: and out of the engine, which held the instance and so every
                 byte of the propagator until this record. *)
              let leave = g.g_leave in
              g.g_leave <- ignore;
              leave ();
              Hashtbl.remove t.cited e.e_cid;
              t.n_detached <- t.n_detached + 1
          | _ -> ())
        evictable;
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
    "%s: %d added, %d evicted, %d swept, %d live, %d duplicate, %d cited, %d pinned%s"
    t.policy.p_name t.n_added t.n_evicted t.n_swept (size t) t.n_duplicate t.n_cited
    t.n_pinned
    (* Only for [tiered] (D-0139), so the keep-all, fifo and lbd lines are the ones the
       differential lane of M11-T2 recorded (it runs real instances at a fixed node
       budget and compares this line as text; the first draft appended it for every
       detaching policy and reddened all 84 fifo/lbd runs on this counter alone). *)
    (if t.policy.p_tiers <> None then
       Printf.sprintf ", %d reductions, %d detached, %d locked" t.n_reductions
         t.n_detached t.n_locked
     else "")
