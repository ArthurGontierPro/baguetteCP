(* search.ml: depth-first search with every decision and backtrack reflected in the
   proof (M1-T10, Part 2). Read the module header below in full before calling
   [solve] -- the proof-logging strategy it implements is a specific, deliberate
   answer to "how a decision made mid-search can ever be cited by a checker that never
   sees it as an axiom", not an incidental detail.

   ---------------------------------------------------------------------------
   The hard question, and why the answer here is neither of the two the task poses
   ---------------------------------------------------------------------------

   docs/SPEC.md 3.4: first-fail variable selection, min-value branching, depth-first,
   restarts disabled. That part is unsurprising. The proof-logging strategy is not.

   A decision is not implied by the model, so it cannot enter the proof as a bare fact:
   neither [rup] nor [pol] can derive an unentailed literal (docs/DECISIONS.md D-0009
   demonstrates this directly against veripb -- a bare literal in a [pol] is the
   trivial axiom [lit >= 0], and [rup] requires a genuine logical consequence), and
   [a] (assumed-checked) is forbidden outside debugging (docs/PROOF-FORMAT.md section
   2). [red] (redundance) does not apply either: it justifies adding a constraint that
   preserves *satisfiability* under a witness substitution, which is not available for
   an arbitrary domain split (a solution with x=3 cannot be "witnessed" into one with
   x>=5; it may simply not exist).

   The task offers two standard resolutions:
     (a) every derived constraint carries the negated decision literals, so it is
         globally valid rather than valid-under-assumption;
     (b) nothing is logged inside a branch; the branch's refutation is derived only
         when it closes.

   This module used to implement (b) for the branching case, and that was the defect
   docs/DECISIONS.md D-0018 is about. The nogood over the active decisions was emitted
   as a [rup] and veripb rejected it; D-0012, D-0014 and D-0017 concluded from that that
   the nogood was *unreachable* and needed new machinery. It is not, and it does not.
   A [rup] check negates its target -- asserting each decision as a unit -- and then unit
   propagates over the database one single constraint at a time. With nothing logged
   inside the branch, the database held only the model rows, so the checker was being
   asked to re-derive a multi-row bounds fixpoint in one step. That is the one thing PB
   unit propagation cannot do, and it never had to: the solver already performed that
   fixpoint and can simply write down each step.

   So what is implemented now is (a) applied *per pruning* rather than per conflict, in
   the form D-0018 takes from the Glasgow Constraint Solver. Every pruning gets one line
   (lib/core/trace.ml):

       rup 1 <the order literal the pruning established>
             1 ~<a bound fact the propagator read> ... >= 1 ;

   which is globally valid and mentions **no decision at all** -- it says "these bounds
   imply that bound", a consequence of one model row. The decisions appear in exactly one
   line, the nogood, unchanged in form from what this module always emitted; it is RUP
   now because the checker has a trace to propagate along. We keep the lazy variant: the
   trace is written when a branch actually fails, by walking the trail, not at every
   pruning on every successful path. [Trace]'s header says why that is sound here and
   what would break it.

   **A conflict with no decision active** is unchanged: it renders the propagator's own
   [Explanation.t] -- D-0013's weaken-out-the-other-variables, divide, add -- as a [pol]
   chain. That is the derivation M1-T12 made [Explanation.t] able to express, and D-0018
   keeps it: where a pruning is not plain RUP over its row, the [pol] is what the trace
   line falls back on (D-0018 point 2). No such fallback was needed for any [int_lin_le]
   pruning in this checkout; see the M1-T13 hand-back report for what was run.

   ---------------------------------------------------------------------------
   How a decision and a backtrack become proof steps
   ---------------------------------------------------------------------------

   Branching splits on a single order-encoding literal [l = x_ge_(k+1)] for the chosen
   variable [x] at the chosen value [k] (docs/SPEC.md 3.4's default, [spec_order] below,
   is first-fail with [k = lo]: try [x = lo] -- i.e. [~l] -- before [x > lo] -- i.e.
   [l]). Which variable, which [k] and which side first are the *only* things the order
   decides, and none of them reaches anything below this paragraph: one literal, one
   level, one trace, one nogood, whatever the order says. Both branches run inside their own
   [Store] decision level (docs/DECISIONS.md D-0008), tagged in the proof with
   [Writer.set_level] to match: *every* decision opens a level and *every* backtrack
   wipes one, which is the sense in which "every branching decision and every
   backtrack MUST be reflected in the proof" (docs/SPEC.md 3.4) holds here. Since
   D-0018 each individual pruning inside a branch is rendered too, tagged with the
   level of the trail entry that produced it, so one [w] retires exactly the lines
   whose prunings the matching [Store.backtrack] undid.

   Ordering is load-bearing and has its own [Debug.check] below: the nogood is emitted
   **before** the level it mentions is wiped. D-0018 point 4 exists because reversing
   these two is the bug someone rediscovers; gcs/solve.cc:296-297 has the same two lines
   in the same order.

   When both branches of a decision fail, their two nogoods --
     "~l" branch:  (negated ancestor decisions) \/ l
     "l"  branch:  (negated ancestor decisions) \/ ~l
   -- resolve on [l] (itself a [rup], found trivially by unit propagation against the
   two clauses, both still live in the database at that point) into the ancestor-only
   nogood, i.e. the failure is propagated exactly one level up, mirroring chronological
   backtracking. The two child nogoods are then retired with a single [w] at the level
   they were tagged with (D-0008: one wipe per backtrack, not one deletion per
   reason), and the combined nogood survives, tagged one level up. Recursing this to
   the root produces, when the whole search space is exhausted, the empty clause --
   an unconditional contradiction -- which is exactly the id [conclusion UNSAT] cites
   (invariant I-S2: the proof independently establishes it, not merely the solver's
   own "I looked everywhere" bookkeeping). *)

module Lit = Baguette_proof.Lit
module Writer = Baguette_proof.Writer
module Encoding = Baguette_proof.Encoding

type assignment = (Var.t * int) list
type outcome = Sat of assignment | Unsat

(* Raised if the independently-checked solution (invariant I-S1) fails the caller's
   own [check] -- a propagator soundness bug (I-P1), never a normal outcome. [solve]
   must not paper over this by pretending UNSAT or silently retrying. *)
exception Unsound_solution of assignment

(* One node's outcome, before it has been reported to its own caller: a solution, or a
   nogood -- the clause already asserted into the proof (its [Writer.cid] is still
   live) together with the literals it states, so the caller can drop its own most
   recent decision literal and re-derive the next nogood up. *)
(* M2-L3: the literals are PAIRED WITH THE DECISION LEVEL each one negates, and the
   pairing is the whole of what makes a backjump decidable locally. A frame owning level
   [lvl] skips its sibling exactly when no pair in the nogood carries [lvl]: the clause is
   then already false under the decisions ABOVE [lvl], so it refutes the sibling too.
   Recomputing the level from the literal is not available -- semantic minimisation merges
   two thresholds on one variable and keeps the DEEPER one's level, which is precisely the
   information that would be lost. See lib/core/learn.ml. *)
type nogood = (Lit.t * int) list
type node = NSat of assignment | NFail of nogood * Writer.cid

(* ------------------------------------------------------------ M1-T36: node counting *)

(* The search-tree node count, kept by the search itself rather than read back out of
   the proof it wrote.

   WHAT A NODE IS HERE. One node is one child dispatched by [branch], plus the root.
   [branch] explores a decision's two sides through [explore_le]/[explore_ge], and each
   of those is one visit to one node of the tree: propagation runs there, and the visit
   ends in a solution, a failure or a further decision. Counting at the dispatch rather
   than inside [dfs] is deliberate and it is what makes the count TOTAL -- the
   [Store.Conflict] arms of [explore_le]/[explore_ge] never reach [dfs], so a counter
   living in [dfs] would silently miss a node that was visited and failed.

   WHAT IT IS NOT. [bench/run_bench.sh] reported `lvl` -- the number of level markers in
   the emitted .pbp -- as a stand-in for this, and labelled it a proxy. It is a
   different number, and not by a constant factor:

     * a level marker is written per child explored AND once more when a branch steps
       back down to emit its combined nogood ([Writer.set_level] is the only thing that
       writes one), so an internal node whose two children both fail contributes THREE
       markers and TWO nodes, while one whose first child is satisfiable contributes ONE
       marker and (down that path) one node. The ratio is a property of the tree's
       shape, so it cannot be divided out;
     * a marker is a property of the PROOF. It moves when the proof's shape changes with
       the tree standing still, which is precisely the confusion D-0026's claim -- the
       same search tree costs no more -- cannot be tested through;
     * there is no marker at all without --proof, so the proxy is not even defined for
       a run that emits no proof.

   [decisions] counts decisions taken: one per [branch] call, which is one per internal
   node. [max_depth] is the deepest decision stack reached -- the depth of the TREE, not
   the deepest level marker in the proof.

   THE ARITHMETIC IS CHECKED, because a number nothing reads is decoration and this
   project has shipped one (M1-T48). Branching is binary and every decision push lands
   (I-D2, and [check_decision_landed] asserts it), so:

       nodes =  2 * decisions + 1     when the tree was exhausted (Unsat)
       nodes <= 2 * decisions + 1     when it was not (Sat: the search stops at the
                                      first solution, so right siblings go unvisited)

   [solve] asserts exactly that under [Debug.check], and test/unit/test_engine.ml
   asserts it outside [Debug.check] on searches whose trees it knows. An off-by-one
   anywhere in the accounting, or a count taken at the wrong event, breaks the equality
   on every complete search. *)
(* ------------------------------------------------------------------------- M1-T66

   What a bridge rested on, as data rather than as bytes in the proof.

   M1-T55 put the settle step on the page; M1-T66 is the row that asked how anyone would
   know if it stopped being there. The answer, measured twice (M1-T45 and the
   orchestrator, 2026-09-17), was: nothing would, except one byte-level assertion in
   test/unit/test_engine.ml that greps the proof text for the line. Disable [bridges]
   outright and 34/34 models still pass and every checker still accepts, because the
   settle is re-derivable from the page without it -- see the paragraph headed "why its
   absence is invisible, and what this record does about it" above [bridges].

   So the bridge is recorded here as a *derivation* instead: which decision it bridged,
   from which literal onto which bound, which holes the push walked over, and -- the part
   that matters for I-S4 and for M2-L3 -- which line on the page states each of those
   holes, at which level. A test can then assert that the step was derived, and assert it
   in the vocabulary of the derivation rather than in the vocabulary of the emitted text,
   which is what M1-T66 asked for. [br_unnamed] is the honest remainder: holes the push
   walked over that no line this solver wrote states, so the bridge rests on the model's
   own rows for them (I-X10).

   [Trace.record_citation] is called for every hole in [br_cited], so a decision settle
   now enters the same I-S4 audit as a propagator settle. Before M1-T66 it did not enter
   it at all: [Trace.emit] skips level-start entries, so a decision push gets no trace
   line and therefore recorded no citation, and the one kind of settle whose line is
   written at the *deepest* open level -- the one furthest from the holes it cites -- was
   the one kind the audit could not see. *)
type bridge = {
  br_var : string;
  br_assumed : Lit.t; (* the literal the branch assumed *)
  br_settled : Lit.t; (* the bound the trail actually recorded *)
  br_ancestors : Lit.t list;
  br_holes : int list; (* the values the push settled over, ascending *)
  br_cited : (int * Writer.cid * int) list; (* hole, its line, that line's level *)
  br_unnamed : int list; (* holes no line of ours states *)
  br_cid : Writer.cid;
  br_level : int;
}

(* Keeping every bridge of a long search would be a leak in a process that shares 15 GB
   with other sessions, and no caller needs more than the first few: a test names the
   scene it built. So the list is capped and [n_bridges] carries the true total, which is
   the number a measurement wants. *)
let bridge_cap = 256

(* M2-L4: buckets for [stats.lbd_hist]. Index [lbd_buckets - 1] is the overflow bucket,
   so an LBD of 16 or more is counted as 16 rather than growing the array -- the
   distribution's shape is what the policy is chosen from, and its tail is one bucket. *)
let lbd_buckets = 17

(* ------------------------------------------------------ M2-L12 step 1: a GLOBAL unit

   A learned clause of ONE literal, as a permanent bound tightening.

   D-0052's step 1, and the reason it comes first is now a measurement rather than an
   estimate: over the 39 models of test/models/, instrumented at the point the clause is
   built ([stats.width_hist]), **72 of 88 learned clauses have exactly one literal**, 5
   have two, 8 have three and 3 have four. The provisional figure D-0052 refused to build
   on -- "roughly 70, +/-5, parsed out of proof text" -- is confirmed at 72 by a counter
   that cannot mistake an [Ne] hole line for a learned clause.

   A unit 1UIP clause has backjump level 0. It is not a constraint that needs a
   propagator, a watch list, a survey or two-open logic: it is a bound that holds
   everywhere in the search tree from the moment it is derived. So it is applied
   directly, with [Store.set_lo] / [Store.set_hi], and the only machinery it needs is the
   justification every pruning needs.

   WHERE IT IS APPLIED, and why that is not "level 0" in the literal sense. The store's
   trail records changes at the level in force; it cannot write a change BELOW the
   current level, and the clause is derived deep in the tree. So [apply_globals] re-runs
   the list at the top of every [dfs] node instead, before [Engine.propagate]. The effect
   is the one a level-0 tightening would have -- the bound holds at every node from here
   on -- and the cost is one walk of a deduplicated list per node plus, at each node
   where it actually moves a bound, exactly the trail entry and trace line that pruning
   would have cost anyway. It is emphatically NOT mutable propagator state: the list only
   grows, it is never undone, and nothing in it depends on the current branch.

   THE JUSTIFICATION IS THE CLAUSE ITSELF, [Explanation.Clause [g_lit]], which renders as
   `rup g_lit >= 1`. That is reverse unit propagation in one step against the learned
   constraint [Learn.introduce] put on the page -- negating the target falsifies that
   constraint outright. Which is exactly why [register_learned] below calls
   [Retention.cite]: the line is RUP only while the constraint is LIVE (D-0052's "new
   obligation", D-0051's "what would reverse this"). *)
type global = {
  g_lit : Lit.t; (* the unit literal, as it appears in the learned clause *)
  g_cid : Writer.cid; (* the learned constraint the [rup] rests on *)
  g_var : Var.t;
  g_pos : bool; (* true: the literal is [x >= g_k]; false: [x <= g_k - 1] *)
  g_k : int;
  g_decl_lo : int;
  g_decl_hi : int;
  g_fact : Reason.fact; (* D-0043: what applying it concludes *)
  g_expl : Explanation.t;
      (* Built ONCE per global and shared, because lib/core/justify.ml memoises on
         physical identity: one `rup` per decision level per unit, cited again
         afterwards, exactly as lib/core/prop/clause.ml shares its own. *)
}

type stats = {
  mutable nodes : int;
  mutable decisions : int;
  mutable max_depth : int;
  mutable n_bridges : int;
  mutable bridges_rev : bridge list;
  (* ------------------------------------------------------------------ M2-L3 *)
  mutable skipped : int;
      (* Siblings NOT explored because the branch's nogood was already false without
         this level's decision. The M1-T36 identity is stated over it below; a backjump
         that reported no skip would be a backjump that did not happen. *)
  mutable n_learned : int; (* 1UIP clauses put on the page *)
  mutable n_converts : int;
      (* ...of which [Learned.to_linear_row] would accept, i.e. of which could have been
         a runtime instance had this row taken D-0044 fork (i). MEASURED, not used: see
         lib/core/learn.ml's header for why the fork went the other way, and M2-L4 for
         who needs the number. *)
  mutable learned_rev : Writer.cid list;
      (* Every id [Learn.introduce] and [Pb_analysis.introduce] handed back, newest
         first. AN AUDIT TRAIL, NOT A DELETION LIST -- M2-L4 took that job away from it,
         and the distinction is the whole of lib/core/retention.ml's section 1. Deleting
         from this list is deleting every id ever introduced, which double-deletes
         anything the retention policy already evicted; [db] holds what is still live and
         is what [solve] sweeps. Kept because "how many distinct ids did this search
         introduce" is what test (a)'s exactly-once audit counts against. *)
  mutable db : Retention.t;
      (* M2-L4: the learned-constraint database and the SOLE owner of a learned id's
         lifetime. Replaced at [solve] entry with one built from [config.retention];
         [stats_create] gives it the default so that a [stats] used without a [solve] --
         which several tests do -- is still well formed. *)
  mutable lbd_hist : int array;
      (* M2-L4. Index i counts learned CLAUSES whose LBD is i, with index [lbd_buckets-1]
         the overflow bucket. A histogram rather than a list because the retention policy
         is chosen from the DISTRIBUTION and this is O(1) memory on a search of any
         depth. Clause path only: the PB path's rows have no LBD of their own -- see
         [Retention]'s header for what they are scored on instead. *)
  mutable width_hist : int array;
  (* M2-L12 step 0. Index i counts learned CLAUSES of exactly i literals, with index
     [lbd_buckets-1] the overflow bucket -- the same bucketing as [lbd_hist] because
     the two are read side by side and a clause cannot have more literals than it has
     levels plus one anyway.

     This exists because D-0052 marked the figure its own sequencing rests on --
     "roughly 70 of 88 learned clauses are unit" -- as PROVISIONAL, +/-5, having
     extracted it by parsing level-0 `rup` lines out of proof TEXT, which also catches
     [Ne] hole lines and every other level-0 `rup`. A counter incremented where the
     clause is built cannot catch anything else: it counts exactly the clauses
     [Learn.at_conflict] returned and [Learn.introduce] put on the page. Width 1 is
     the population step 1 acts on -- a unit clause has backjump level 0 and is a
     permanent global bound tightening. *)
  (* ------------------------------------------------------------------ M2-L12 *)
  mutable globals_rev : global list;
      (* Learned units, newest first, DEDUPLICATED by literal. Replaced at [solve] entry
         for the reason [db] is. Deduplication matters here and not for the clause
         instances below: one model (width_sat_depth) derives 49 of the suite's 72 units,
         many of them the same bound twice, and this list is walked at every node. *)
  mutable n_global_prunes : int;
      (* Times applying a global actually MOVED a bound. This is the counter that says
         whether step 1 did anything: a learned unit that never prunes is a learned unit
         the search had already re-derived for itself. *)
  mutable n_global_conflicts : int; (* ...and times it refuted the node outright *)
  mutable n_global_declined : int;
      (* Units this search could not apply -- a [Lit.Eq] literal (the direct encoding has
         no bound to move; D-0019 point 3 and D-0052 both say do not reach for
         [Store.remove_with_facts]) or a name the encoding does not declare. Counted
         rather than silently skipped, because "step 1 captured the unit population" is a
         claim this number can refute. *)
  mutable n_clause_instances : int;
      (* M2-L12 step 2: multi-literal learned clauses registered with the engine as
         [Clause.Learned_clause] instances. *)
  mutable n_clause_declined : int;
  (* ...and those [Clause.of_lits] refused, for the same two reasons as
     [n_global_declined]. *)
  (* ------------------------------------------------------------------ M2-L13 *)
  mutable n_pb_instances : int;
      (* Learned PB ROWS registered with the engine as [Pb.Learned_pb] instances --
         D-0054's solving-side object. Distinct from [n_clause_instances], which counts
         the degree-1 case arriving by the M2-L3 clause path; a conflict can contribute
         to both, because both objects are learned from it. *)
  mutable n_pb_inst_declined : int;
      (* ...and the rows [Pb.of_terms] refused: a [Lit.Eq] literal, or a name the
         encoding does not declare. Same two reasons as [n_global_declined], counted
         rather than silently skipped for the same reason. *)
  mutable pb_inst_ids_rev : int list;
      (* The engine instance ids of those, newest first. A LIST and not a [Hashtbl]:
         nothing here may iterate a hash table (the determinism gate), and the list is
         one entry per learned row. Read by [count_learned_activity] to tell a pruning
         made by a learned PB row from one made by a learned clause. *)
  mutable clause_inst_ids_rev : int list; (* ...and the M2-L12 clause instances' *)
  mutable n_pb_prunes : int;
      (* Bounds actually MOVED by a learned PB instance. This is the counter M2-L13
         turns on and the one M2-L12 reported as 0 for the clause path: an instance with
         no prunings is a propagator that exists and does nothing, which is the result
         D-0054 reinterpreted. Counted off the TRAIL (whose entries carry the pushing
         instance's id, M2-T7) rather than by the propagator, which has no stats. *)
  mutable n_pb_inst_conflicts : int; (* ...and conflicts one reported outright *)
  mutable n_clause_prunes : int; (* the same two, for the M2-L12 clause instances *)
  mutable n_clause_inst_conflicts : int;
  mutable first_learned_id : int;
      (* [Engine.next_id] at [solve] entry: every instance id at or above it was
         registered mid-search by this row or by M2-L12, and every id below it is a model
         row's. The engine only ever appends ([Engine.add]), which is what makes the
         range test sound; [Search]'s own comment on why the engine cannot be reset
         between solves is the other half of that. *)
  mutable i_s4_supports : int; (* hole lines the learned clauses' derivations rest on *)
  mutable i_s4_crossings : int; (* ...of which sit above level 0 -- data, not a fault *)
  mutable i_s4_broken_rev : string list; (* ...of which were already retired: faults *)
  mutable n_min_dropped : int;
  (* Literals semantic minimisation removed from a nogood. A reduction that never
     fires is a reduction whose break lane cannot redden, which is why it is counted
     rather than assumed to be doing something. *)
  (* ------------------------------------------------------------------ M2-L6 *)
  mutable n_pb_attempts : int;
      (* Conflicts PB analysis was asked about. The denominator of the fallback rate, and
         NOT [n_learned]: a conflict at no decision level is never analysed at all. *)
  mutable n_pb_learned : int; (* ...of which produced a PB row that went on the page *)
  mutable n_pb_fallback : int;
      (* ...of which handed the conflict back to the M2-L3 clause path. This is the
         counter docs/ROADMAP.md M2-L6 test (b) exists for: the clause path is permanent
         (D-0044), so a build that ALWAYS fell back would look green in every other
         measure the suite has. It cannot look green in this one. *)
  mutable n_pb_steps : int; (* pivots eliminated, over all successful analyses *)
  mutable n_pb_converts : int;
      (* ...of which [Learned.to_linear_row] accepts. Measured against the clause path's
         [n_converts], which is the comparison lib/core/pb_analysis.ml's "why the PB row
         can propagate where the clause cannot" makes and does not assume.

         NOT "of which could be a runtime instance", which is what this comment said
         until M2-L4 measured it. The EMPTY CONTRADICTION converts -- to a zero-term
         [Linear] that propagates nothing -- and is counted here. Suite-wide on
         2026-09-18: 36 conversions of 38 learned rows, of which **10 are the empty
         contradiction** (backjump_lineq_unsat 3, near_limit_unsat 3, offset_unsat 4), so
         26 could actually propagate. Read this beside [n_pb_nondegenerate], which is the
         counter that can tell them apart, and see bin/main.ml's block above `pb-nondeg`.
         The counter is left as it is on purpose: test_ladder.ml's degenerate control pins
         that it CANNOT make the distinction, which is the property M2-L11 established. *)
  mutable n_pb_stronger : int;
  (* ...of which convert where the SAME conflict's clause does not. This is test (a)
     as a counter: the number of times this row did something M2-L3 could not -- with
     [n_pb_converts]'s caveat above inherited in full, because it is the same predicate.
     Suite-wide 36, of which the same 10 are vacuous. *)
  (* ------------------------------------------------------------------ M2-L11 *)
  mutable n_pb_nondegenerate : int;
      (* Learned PB rows that are NOT the empty contradiction, i.e. that still carry at
         least one literal. This is docs/ROADMAP.md M2-L11 test (b) and it is the number
         the whole row turns on. A counter that cannot tell a contradiction from an
         inequality cannot report an improvement, so this one exists to be quoted BESIDE
         [n_pb_stronger] and never instead of it.

         AND IT IMMEDIATELY CORRECTED THE RECORD. M2-L6 reported "pb-stronger 36 of 36,
         and every one of those 36 is the degenerate case". That is not what the suite
         says: re-measured 2026-09-18 over the same 38 models, 26 of those 36 carry
         literals. The degenerate ones are the int_lin_eq family -- backjump_lineq_unsat
         (3), near_limit_unsat (3), offset_unsat (4) -- where the two halves of an
         equality add to 0 >= k in ONE elimination, which is exactly the family M2-L6's
         own test (a) inspected. width_sat_depth alone contributes 24 non-degenerate rows,
         of the shape `+2 a_ge_1 ... +2 a_ge_99 >= 98`. So the generalisation ran from one
         family to the suite, and it stood because nothing counted. *)
  mutable n_pb_lifted : int;
      (* Analyses in which at least one elimination resolved against the model row PLUS a
         ladder chain (lib/core/ladder.ml) rather than the model row alone. 0 means this
         build is behaviourally M2-L6: the lift is a RETRY after the bare row fails, so a
         build in which it never fires derives exactly what M2-L6 derived. That is what
         makes this counter the one that says whether M2-L11 is doing anything. *)
  mutable n_pb_rungs : int;
      (* ...and how many ladder rows those analyses cited in total. Separate from
         [n_pb_lifted] because one analysis can climb many rungs, and a build that lifts
         often but one rung at a time is a different thing from one that lifts rarely and
         far. *)
  mutable pb_rows_rev : Pb_analysis.t list;
      (* The PB rows learned, newest first, capped. Kept so a test can run the ORACLE on
         what a real solve actually derived -- test (e) -- instead of on a scene built to
         make the oracle pass. Capped for the reason [bridges_rev] is. *)
  mutable pb_fallback_rev : string list;
  (* Why, newest first, capped. A rate with no breakdown behind it cannot be acted
     on, and the breakdown is what says whether the traffic is [No_row] (expected,
     D-0044) or [Not_conflicting] (a finding about the reduction). *)
  (* ------------------------------------------------------------------ M2-L15 *)
  mutable n_level_compared : int;
      (* Conflicts at which BOTH a decision closure and a PB row were obtained, so the
         two level sets could be put side by side. The denominator of everything below,
         and it is neither [n_learned] nor [n_pb_learned]: a conflict that falls back has
         no PB set, and one under no decision has no closure. *)
  mutable n_level_same : int; (* ...and the two sets were equal *)
  mutable n_level_narrower : int;
      (* ...and the PB row's set is a STRICT SUBSET of the closure's. THIS IS THE TRAP,
         and it is the only one of the four arms that is dangerous: a narrower set filters
         MORE literals out of the branch nogood, so it licenses a HIGHER jump than the
         closure justifies, and the clause that comes out is not entailed. Every one of
         these is a conflict at which [config.backjump_on_pb] would emit an unprovable
         nogood. See [pb_level_verdict]. *)
  mutable n_level_wider : int;
      (* ...and the closure's is a strict subset of the PB row's. Harmless as a backjump
         -- it skips less -- and interesting as data: it means the row's literals were
         falsified at levels the conflict does not actually rest on, which is what
         "the levels a derived row names are not a dependency set" looks like from the
         other side. *)
  mutable n_level_incomparable : int;
      (* ...and neither contains the other. Counted apart because "differ" would let a
         reader assume the disagreement is one-directional, and it is not. *)
  mutable n_level_assert_deeper : int;
      (* Conflicts at which the PB row's own [asserting_level] -- the SAT solver's
         backjump level, Le Berre et al.'s subject -- is strictly below the LOWEST level
         the closure names, i.e. the row would resume beneath EVERY decision the conflict
         actually rests on. That is the maximal over-jump and it is the figure the CDCL
         instinct deserves to have put next to it.

         Compared against the lowest and not the deepest ON PURPOSE. Against the deepest
         it is near-vacuous: [assertive_slack]'s postcondition already guarantees the row
         asserts at [conflict_level - 1], and the closure's deepest level is the conflict
         level, so the comparison would read 103 of 103 over the suite and mean only that
         the criterion did its job. Measured that way first; the number was 103 of 103,
         and a counter that cannot come out false is decoration. *)
  mutable n_level_pb_empty : int;
      (* Conflicts at which the learned PB row names NO level at all -- the empty
         contradiction [0 >= k] (see [n_pb_nondegenerate]), whose [levels] is [[]].

         Split out of [n_level_narrower] because it is the same arm with a different
         meaning and the worst case in it: filtering the branch nogood by the empty set
         leaves the EMPTY CLAUSE, i.e. a claim that the model is unconditionally
         unsatisfiable, emitted at a node where it is not. Folding it in with php's
         genuine partial subsets would let a reader think the dangerous arm is uniform,
         and it is not. *)
  mutable level_diffs_rev : string list;
      (* The disagreements, newest first, capped: one line each, closure set against PB
         set. Capped for the reason [pb_fallback_rev] is. *)
}

let stats_create () =
  {
    nodes = 0;
    decisions = 0;
    max_depth = 0;
    n_bridges = 0;
    bridges_rev = [];
    skipped = 0;
    n_learned = 0;
    lbd_hist = Array.make lbd_buckets 0;
    width_hist = Array.make lbd_buckets 0;
    n_converts = 0;
    learned_rev = [];
    db = Retention.create ();
    globals_rev = [];
    n_global_prunes = 0;
    n_global_conflicts = 0;
    n_global_declined = 0;
    n_clause_instances = 0;
    n_clause_declined = 0;
    n_pb_instances = 0;
    n_pb_inst_declined = 0;
    pb_inst_ids_rev = [];
    clause_inst_ids_rev = [];
    n_pb_prunes = 0;
    n_pb_inst_conflicts = 0;
    n_clause_prunes = 0;
    n_clause_inst_conflicts = 0;
    first_learned_id = max_int;
    i_s4_supports = 0;
    i_s4_crossings = 0;
    i_s4_broken_rev = [];
    n_min_dropped = 0;
    n_pb_attempts = 0;
    n_pb_learned = 0;
    n_pb_fallback = 0;
    n_pb_steps = 0;
    n_pb_converts = 0;
    n_pb_stronger = 0;
    n_pb_nondegenerate = 0;
    n_pb_lifted = 0;
    n_pb_rungs = 0;
    pb_rows_rev = [];
    pb_fallback_rev = [];
    n_level_compared = 0;
    n_level_same = 0;
    n_level_narrower = 0;
    n_level_wider = 0;
    n_level_incomparable = 0;
    n_level_assert_deeper = 0;
    n_level_pb_empty = 0;
    level_diffs_rev = [];
  }

let stats_learned s = List.rev s.learned_rev
let stats_db s = s.db

(* M2-L4: the LBD histogram as [(lbd, count)], ascending, empty buckets dropped. The
   last bucket is the overflow one, so a pair [(16, n)] means "16 or more". *)
let stats_lbd s =
  Array.to_list (Array.mapi (fun i n -> (i, n)) s.lbd_hist)
  |> List.filter (fun (_, n) -> n > 0)

(* M2-L12 step 0: the learned-CLAUSE WIDTH histogram as [(width, count)], ascending,
   empty buckets dropped, last bucket overflow. Same shape as [stats_lbd]. *)
let stats_width s =
  Array.to_list (Array.mapi (fun i n -> (i, n)) s.width_hist)
  |> List.filter (fun (_, n) -> n > 0)

(* M2-L12: the learned units in force, oldest first, as their literals. A test reads this
   to name the bound it expects to have moved. *)
let stats_globals s = List.rev_map (fun g -> g.g_lit) s.globals_rev

(* ------------------------------------------------------------------ M2-L6 counters *)

(* The same cap and the same reason as [bridge_cap]: keeping every reason of a long
   search would be a leak in a process that shares 15 GB, and no caller needs more than
   the first few. The RATE is computed from [n_pb_fallback], which is uncapped. *)
let pb_reason_cap = 64
let stats_pb_fallbacks s = List.rev s.pb_fallback_rev
let stats_pb_rows s = List.rev s.pb_rows_rev

(* M2-L15: the disagreements, oldest first. Same shape and same cap as
   [stats_pb_fallbacks], and read for the same reason -- a rate with no breakdown behind
   it cannot be acted on. *)
let stats_level_diffs s = List.rev s.level_diffs_rev

(* The fraction of analysed conflicts that fell back to the clause path, in [0., 1.].
   [0.] when nothing was analysed -- which is honestly "no fallbacks happened", and a
   caller that needs to tell that apart from "none of the many attempts fell back" has
   [n_pb_attempts] to look at. *)
let stats_pb_fallback_rate s =
  if s.n_pb_attempts = 0 then 0.
  else float_of_int s.n_pb_fallback /. float_of_int s.n_pb_attempts

let stats_i_s4_broken s = List.rev s.i_s4_broken_rev

(* The bridges this search derived, oldest first, up to [bridge_cap] of them. *)
let stats_bridges s = List.rev s.bridges_rev

let record_bridge s b =
  s.n_bridges <- s.n_bridges + 1;
  if s.n_bridges <= bridge_cap then s.bridges_rev <- b :: s.bridges_rev

(* Does this pair of counts satisfy the identity above? [exhausted] is whether the
   search closed its whole tree. Public because [solve] checks it only under
   BAGUETTE_DEBUG and the tests must be able to check it always. *)
(* M2-L3 widens the identity by exactly one term rather than weakening it. Branching is
   still binary and every push still lands; what changed is that a backjump dispatches
   ONE child at an internal node instead of two, and [skipped] counts each time it did.
   With learning off [skipped] is 0 and this is M1-T36's equation unaltered. A version
   that merely relaxed the equality to an inequality would have stopped catching the
   off-by-one it exists for, on every search. *)
let stats_expected_nodes s = (2 * s.decisions) + 1 - s.skipped

let stats_consistent s ~exhausted =
  if exhausted then s.nodes = stats_expected_nodes s
  else s.nodes <= stats_expected_nodes s

(* ------------------------------------------------------- the branching order (M2-T11)

   Which variable is branched on, at which value, and which side first. docs/SPEC.md 3.4
   fixes that -- first-fail, indomain_min -- and [spec_order] is it; it is the default of
   [solve] and the only order anything outside the tests uses. [random_order] exists
   because M1's whole nogood story (D-0018, D-0021) is a claim about *whatever* tree the
   search happens to build: the branch's own trace is what its refutation rests on, so a
   different tree is a different proof, and a fuzzer that only ever drives one tree shape
   tests one shape of that claim. It is a test facility and nothing more.

   What an order may vary is the *choice*. It may not vary the logging discipline around
   it, and it cannot: everything below this point -- one level per decision, the trace
   before the nogood, the nogood before the wipe (D-0018 point 4) -- is written once and
   is the same code for every order. If making some order verify seems to need a change
   to the emission, that is the emission relying on the fixed order, which is a finding
   and not a patch. *)

(* Every unfixed variable, in declaration order; empty exactly when everything is fixed.

   An order chooses from this array and can choose nothing else, which is what keeps
   completeness (I-S2) a property of this module rather than of the strategy it is handed:
   [dfs] reports a solution exactly when the array is empty, so a strategy decides the
   *shape* of the tree and never which leaves it has. *)
let unfixed store =
  let n = Store.n_vars store in
  let acc = ref [] in
  for i = n - 1 downto 0 do
    let v = Var.of_int i in
    if Domain.size (Store.get store v) > 1 then acc := v :: !acc
  done;
  Array.of_list !acc

(* One decision. [d_split] is read as: the low branch is [x <= d_split], the high branch
   is [x >= d_split + 1], and the single order literal [x_ge_(d_split+1)] is the one thing
   the two branches disagree about -- so the two child nogoods still resolve on exactly
   one literal, as they always did. [d_split] must lie in [lo, hi), which makes both
   pushes strictly narrowing, which is what [check_decision_landed] asserts.

   docs/SPEC.md 3.4's indomain_min is [d_split = lo] with the low side first (that branch
   then fixes [x = lo], which is what [Search] has always emitted); indomain_max would be
   [d_split = hi - 1] with the high side first. *)
type decision = { d_var : Var.t; d_split : int; d_high_first : bool }

(* An order is asked for a decision given the store and the non-empty array of unfixed
   variables. *)
type order = Store.t -> Var.t array -> decision

(* First-fail (docs/SPEC.md 3.4): the unfixed variable (domain size > 1) with the
   smallest domain, ties broken by declaration order (the store's variable index). *)
let first_fail store cands =
  let best = ref cands.(0) in
  let bsize = ref (Domain.size (Store.get store cands.(0))) in
  for i = 1 to Array.length cands - 1 do
    let size = Domain.size (Store.get store cands.(i)) in
    if size < !bsize then (
      best := cands.(i);
      bsize := size)
  done;
  !best

(* Input order (docs/SPEC.md 3.4): the FIRST unfixed variable in the order the caller
   handed them over. [unfixed] builds its array by ascending store index, and
   `lib/flatzinc/compile.ml` builds the store in `Model.vars` order, so at the top level
   that is declaration order; inside a [phase] below it is the order the annotation's
   array wrote, which is the order `int_search(vs, input_order, ...)` actually means. *)
let input_order _store cands = cands.(0)

(* docs/SPEC.md 3.4, and the default of [solve]: first-fail, min-value branching. This is
   the normative default -- what a model with NO search annotation gets, and what
   [sequence] below falls back to for the variables an annotation did not mention. *)
let spec_order store cands =
  let v = first_fail store cands in
  { d_var = v; d_split = Domain.lo (Store.get store v); d_high_first = false }

(* ------------------------------------------------------- M7-T2: annotated search

   A FlatZinc `int_search`/`bool_search` annotation is two independent choices -- which
   variable, then how to split it -- over a NAMED SUBSET of the variables, and
   `seq_search` is a list of those consulted in order. So the order is factored the same
   way: a [var_select] picks from candidates, a [val_select] turns the pick into a
   decision, and a [phase] pairs them with the subset they govern.

   Splitting the value choice out is what makes obligation (a) of M7-T2 testable at all:
   [indomain_min] and [indomain_max] produce DIFFERENT decisions on the same variable, and
   a test can assert on the decision rather than on the answer.

   These constructors live in `core` and not in `flatzinc` because [order] is core's type
   and the dependency runs one way (CLAUDE.md, "Where things are"). `compile.ml` supplies
   the subsets; it does not get to define what an order is. *)

type var_select = Store.t -> Var.t array -> Var.t
type val_select = Store.t -> Var.t -> decision

(* [d_split] must lie in [lo, hi) ([type decision]); both of these are in range because a
   candidate is by construction unfixed, so [hi > lo].

   indomain_min splits at [lo] and takes the LOW side first -- that branch fixes [x = lo].
   indomain_max splits at [hi - 1] and takes the HIGH side first -- that branch fixes
   [x = hi]. Neither is "the other one reversed": the split point moves too, because
   trying the largest value first is only one decision if the branch that assumes it
   fixes the variable. *)
let indomain_min store v =
  { d_var = v; d_split = Domain.lo (Store.get store v); d_high_first = false }

let indomain_max store v =
  { d_var = v; d_split = Domain.hi (Store.get store v) - 1; d_high_first = true }

(* One `int_search(...)` annotation. [p_vars] is the annotation's array, IN THE ORDER IT
   WAS WRITTEN, which is what [input_order] reads; it may name a variable twice and may
   omit variables entirely, and neither is this type's problem. *)
type phase = { p_vars : Var.t array; p_var : var_select; p_val : val_select }

(* `seq_search`: consult each phase in turn, and take the first whose subset still holds
   an unfixed variable. That IS the composition rule -- a later annotation is reached only
   once every variable of every earlier one is fixed -- and it is M7-T2 obligation (b).

   [fallback] is what happens when no phase has an unfixed variable left but the search
   still needs a decision, which is the ordinary case: a FlatZinc annotation is not
   obliged to mention every variable, and the solver must still be able to branch on the
   ones it did not. [Search] would otherwise have no decision to make and the model would
   be answered wrong, so the fallback is not optional and not a default -- it is stated.
   `compile.ml` passes [spec_order], and docs/SPEC.md 3.4 needs to say so. *)
let sequence ?(fallback = spec_order) (phases : phase list) : order =
 fun store cands ->
  let live = Hashtbl.create (2 * Array.length cands) in
  Array.iter (fun v -> Hashtbl.replace live (Var.to_int v) ()) cands;
  let rec go = function
    | [] -> fallback store cands
    | ph :: rest -> (
        let sub =
          Array.of_seq
            (Seq.filter
               (fun v -> Hashtbl.mem live (Var.to_int v))
               (Array.to_seq ph.p_vars))
        in
        match Array.length sub with
        | 0 -> go rest
        | _ -> ph.p_val store (ph.p_var store sub))
  in
  go phases

(* A branching order driven by [r], for the fuzzer (test/unit/test_random.ml). Every
   draw comes from [r], so one seed reproduces one whole tree. Three draws per decision
   -- the variable, the split, and which side goes first -- and NO rejection of any
   split in [lo, hi), which is the only shape constraint [branch] imposes.

   ---------------------------------------------------------------------------
   M1-T45: the hole guard this function used to carry, and why it is gone
   ---------------------------------------------------------------------------

   This function used to refuse to split at a [k] unless both [k] and [k + 1] were in
   the domain, retrying up to eight times and falling back to [lo]. The refusal was
   about the proof and not about the search: [Domain.settle] walks a bound over a hole,
   so a decision at a hole puts a bound on the trail strictly STRONGER than the
   [x_ge_(k+1)] its nogood negates, and the checker cannot replay the difference unless
   the difference is written down.

   Three things settled that, in this order, and the last one is the one that matters:

     1. The guard shipped DISABLED. It read [if true || (Domain.mem d k && Domain.mem d
        (k + 1))], which short-circuits, so the membership test, the retry recursion and
        the [tries] counter were all dead and every draw was taken whatever the domain
        looked like -- an unfinished-debugging edit no compiler warning catches. It was
        restored rather than deleted, deliberately, because "the guard is load-bearing"
        was a claim nobody had tested.
     2. Then it was measured. With it disabled, and with [random_order] further biased
        to prefer a holey variable AND a hole split within it, 2051 splits out of 495723
        over 108000 solver runs landed where it refused, and NOT ONE was rejected by
        veripb. So it was conservative, not measured-necessary. The guard was also never
        total: the fallback after eight misses could itself land at a hole.
     3. M1-T55 then wrote the missing step down. [bridges] below states, per settled
        decision and conditioned on that decision's ancestors, the implication from the
        literal the branch assumed to the bound the settle established. That is exactly
        what a hole split was missing, and it had to be written anyway: [spec_order] --
        the normative order, the CLI's only one -- splits at [d_split = lo] and
        [explore_ge] pushes [set_lo v (lo + 1)], which lands on a hole whenever [lo + 1]
        is one. So the normative default ALREADY makes the decision this guard refused,
        has no guard of its own and never did, and M1-T55 closed that by emitting the
        bridge rather than by adding one.

   Point 3 is the argument, and M1-T45's bar was the right way round: taking these
   shapes back needed an instance showing what the guard catches. There is none.
   [test_hole_split_sweep] in test/unit/test_engine.ml forces EVERY split shape the
   guard used to refuse -- a hole below the split, a hole above it, and holes on both
   sides at once -- over every interior hole pattern of a width-5 domain, at the root
   and one level down so the ancestor conjunct of [bridges] is under test too, and runs
   the real checker over each resulting proof. Every one verifies. What the guard bought
   was 0.4% fewer tree shapes for the fuzzer and one asymmetry with the normative order;
   what it cost was a class of decision the default makes and the fuzzer could not.

   If a hole split is ever rejected under this function, that is now a finding about
   [bridges] or about a propagator, which is what a fuzzer is for -- it is not a finding
   about this function. *)
let random_order r store cands =
  let v = cands.(Random.State.full_int r (Array.length cands)) in
  let d = Store.get store v in
  let lo = Domain.lo d and hi = Domain.hi d in
  {
    d_var = v;
    d_split = lo + Random.State.full_int r (hi - lo);
    d_high_first = Random.State.bool r;
  }

let extract_assignment store : assignment =
  List.init (Store.n_vars store) (fun i ->
      let v = Var.of_int i in
      (v, Domain.lo (Store.get store v)))

(* ------------------------------------------------------- M2-L3: learning, as a config

   What the search is allowed to do with a conflict, as a value rather than as an
   environment variable, because two of the three fields exist ONLY so that a test can
   perform a break and watch the checker reject it. A knob a test cannot set is a knob
   whose break lane does not exist, and this project has shipped one (M1-T45).

   [learn]      off is M1's search exactly: the nogood is the whole decision stack, no
                cut is taken, no clause is put on the page and [stats.skipped] stays 0.
                It is what test (c) measures against, and what a caller that wants the
                hand-derived tree of M1-T36's accounting tests asks for.
   [policy]     [Learn.Strongest] is the semantic minimisation. [Learn.Weakest] is this
                row's test (a2) break: it keeps the threshold the other one drops, so the
                nogood claims strictly more than the cut supports, and the checker
                rejects it. It is wrong on purpose and is not reachable from the CLI.
   [break_i_s4] retires the conflict level BEFORE the learned clause is derived instead
                of after, which is this row's test (b) break -- D-0018 point 4 and I-S4
                read backwards. The [rup] is then checked against a database that no
                longer holds the trace lines it rests on. Also not CLI-reachable.

   M2-L6 adds three, and the first is the one a reader should look at twice.

   [pb]         PB conflict analysis (lib/core/pb_analysis.ml). On, and ADDITIVE: when it
                succeeds, the derived inequality goes on the page ALONGSIDE the M2-L3
                clause, not instead of it. That is not hedging. The clause is what the
                search's nogood and backjump rest on -- through [Learn.levels], which come
                from the decision closure and not from either learned object, which M2-L15
                re-asked after M2-L13 and MEASURED rather than left as a preference; see
                [pb_level_verdict] -- and M2-L3 owns a body of assertions about it that
                this row has no business disturbing. What the PB row adds is a strictly stronger constraint on the
                page, under D-0044's same fork (ii): proof-only until M2-L4's retention
                policy decides which learned objects earn a runtime instance. Off is the
                state every M2-L3 measurement was taken in, so a comparison against those
                numbers has a switch to set.
   [reduction]  which [Reduce.t] brings the pivot's coefficient to 1. [round_to_one]
                dominates [division] (D-0044), and [division] is here so a test can show
                the difference on a real conflict rather than on a hand-built row.
   [pb_criterion] the slack-based stopping rule. See lib/core/pb_analysis.ml on why an
                assertive constraint is not a sufficient stop condition for PB.

   M2-L11 adds one, and it is a BREAK KNOB in the same sense [break_i_s4] is -- except
   that turning it off is not wrong, it is M2-L6.

   [pb_ladder]  whether a reason row that does not PB-propagate its pivot may be
                strengthened by the order encoding's ladder rows (lib/core/ladder.ml)
                before the reduction is tried again. ON. Off is exactly the M2-L6 build:
                the lift is a RETRY after the bare row fails, so with it off every
                conflict takes the derivation M2-L6 took and the counters land on M2-L6's
                numbers. That is what makes it the break lane for this row -- a test can
                assert that the fixture's learned rows DISAPPEAR when the ladder is
                withheld, which is the only way to show the chain is load-bearing rather
                than decorative.
   [break_ladder_mult] writes one ladder row at the WRONG multiplier on the [pol] while
                still claiming the right conclusion, which is this row's proof-level
                break. Wrong on purpose, sound but not the claimed row, and not
                CLI-reachable. See [Ladder.derive]'s [~break]. *)
(* ------------------------------------------------------- M5-T1: BRANCH AND BOUND

   The objective, and the incumbent, as data. Read this before [record_improving] and
   before [optimise]; the whole of M5-T1's proof argument is here rather than spread
   over the three of them.

   THE SHAPE, IN ONE SENTENCE. A branch-and-bound bound is *exactly* an M2-L12 global
   unit -- a permanent, decision-free bound tightening applied at the top of every node
   -- whose supporting constraint happens to come from `soli` rather than from
   [Learn.introduce]. Everything below reuses [type global], [global_of] and
   [apply_globals] unchanged. No new [Explanation] constructor was needed and none was
   added: the justification is [Explanation.clause [the bound literal]], which is what a
   learned unit already uses, and it renders as one `rup`.

   WHY THAT IS SOUND, measured against veripb 3.0.2 rather than argued. `soli <lits>`
   logs an improving solution AND yields the id of the strictly-improving constraint the
   checker builds for itself from the objective it read out of the .opb -- we never
   assert that constraint, so we cannot assert it wrongly. On an objective variable
   [obj] with declared domain [lo, hi], the .opb objective is the order encoding's own
   sum, so the constraint the checker adds for an incumbent of value [v] is
   "obj <= v - 1", and the single order literal ~obj_ge_v is RUP against it:

       @s1 soli ... y_ge_1 y_ge_2 y_ge_3 y_ge_4 ~y_ge_5 ;
           -> ConstraintId 11: 1 ~y_ge_1 1 ~y_ge_2 1 ~y_ge_3 1 ~y_ge_4 1 ~y_ge_5 >= 2
       @b1 rup +1 ~y_ge_4 >= 1 ;                                          ACCEPTED

   The `rup` needs the LADDER to get there -- negating it asserts y_ge_4, the ladder
   rows @c5..@c7 propagate y_ge_3, y_ge_2, y_ge_1, and the improving constraint is then
   falsified outright. That is one unit-propagation sweep over rows that are already in
   the .opb, which is the reason this needs no `pol` and no new machinery.

   `obju` IS NOT USED, AND THAT IS THE POINT. docs/PROOF-FORMAT.md line 136 files the
   trap against M5: `obju ... ;` is refused with *"Proofgoal #1 could not be autoproven.
   Please add an explicit subproof for proofgoal #1."* (re-measured on 3.0.2, 2026-09-21,
   not quoted from the note). It is refused because an objective UPDATE changes the
   function being minimised and owes a proof that the change is sound. Branch and bound
   does not change the objective -- it tightens a BOUND on a fixed objective -- so the
   rule it needs is `soli`, which owes no such goal. The trap is avoided by not being in
   its way, and [test_proof.ml]'s [obju_needs_a_subproof] keeps the measurement honest by
   performing it.

   WHAT THE CONCLUSION RESTS ON, and why it is not decorative. `conclusion BOUNDS <lo>`
   is CHECKED: 3.0.2 refuses a claim no database constraint syntactically implies, with
   *"Constraint not syntactically implied by any constraint in the database."*, and
   refuses a cited id that implies a weaker bound than claimed, with *"Expected
   constraint is not syntactically implied by the constraint at the hint."* Both were
   performed. So the lower bound is load-bearing, and there are exactly two ways this
   search can produce one:

     (1) THE TREE IS EXHAUSTED under the last improving constraint. The root refutation's
         contradiction implies every bound, and it is what [Writer.Bounds]'s [lower_id]
         cites. This is the ordinary case and the one the `pol`/`rup` machinery pays for.
     (2) THE INCUMBENT SITS ON THE OBJECTIVE'S DECLARED FLOOR (or ceiling, maximising).
         Then "obj <= v - 1" is already unsatisfiable as written -- the checker builds
         `1 ~y_ge_1 1 ~y_ge_2 1 ~y_ge_3 >= 4` over three terms -- so the improving
         constraint IS the contradiction and is cited directly. There is no literal
         ~obj_ge_lo in the encoding to make a global out of, which is the mechanical
         reason this case is separate rather than a shortcut.

   Note which literal each direction needs. Minimising, the bound is [obj <= v - 1],
   which the order encoding writes as [Lit.le obj (v - 1)] = ~obj_ge_v. Maximising, the
   .opb objective is NEGATED (docs: "An objective is minimised; FlatZinc maximisation is
   negated by the caller"), the checker's objective value is -v, and the bound is
   [obj >= v + 1] = obj_ge_(v+1). The numbers reported in `conclusion BOUNDS` are in the
   CHECKER's units -- negated under maximisation -- and [optimise] is where that is
   applied, once. *)
type direction = Minimise | Maximise

type objective = {
  o_var : Var.t;
  o_name : string; (* the encoding's name for it: the literals are built from this *)
  o_dir : direction;
  o_decl_lo : int; (* DECLARED, not current: the floor case above is about this one *)
  o_decl_hi : int;
}

(* The running state of a branch-and-bound search. Mutable and shared by reference
   through [config], because it is the one thing in a solve that genuinely is mutable
   search state: [stats] may not hold it (passing a [stats] must change no byte of the
   emitted proof, and this changes every byte) and [trace] is about prunings. *)
type bnb = {
  b_obj : objective;
  b_check : assignment -> bool;
      (* I-S1, per improving solution and not merely per run. An optimisation search
         prints several solutions and every one of them is a solution printed, so every
         one of them is re-checked independently. *)
  b_on_solution : assignment -> unit;
      (* SPEC 2.2: each improving solution is printed as it is found, terminated by
         `----------`. It is a callback and not a list because the FlatZinc convention
         is a running report, not a summary -- a user who kills a long optimisation has
         still been told the best answer found so far. *)
  mutable b_best : (assignment * int) option;
      (* the incumbent and its value IN MODEL UNITS (the objective variable's own
         value), never the checker's negated units *)
  mutable b_soli_ids : Writer.cid list; (* every id `soli` handed back, for I-X2 *)
  mutable b_floor : Writer.cid option;
      (* Case (2) above: the improving constraint that is itself the contradiction.
         [Some] means the search is over and this is what the conclusion cites. *)
}

type config = {
  learn : bool;
  policy : Learn.policy;
  break_i_s4 : bool;
  pb : bool;
  reduction : Reduce.t;
  pb_criterion : Pb_analysis.criterion;
  pb_ladder : bool;
  break_ladder_mult : bool;
  break_pb_degree : bool;
      (* M2-L13's break. Registers the learned PB row's runtime instance with a degree
         ONE HIGHER than the row that is on the page, so the propagator enforces a
         constraint the proof does not state and its prunings are no longer RUP against
         it. The point is that a wrong slack rule is NOT visible in the answer -- an
         over-strong propagator still returns UNSAT on an unsatisfiable model -- so the
         only oracle for it is the checker, and this is what puts the checker in front of
         one. test/unit/test_pb.ml runs it and asserts the REJECTION's wording. *)
  retention : Retention.policy;
      (* M2-L4. [Retention.keep_all] is the pre-M2-L4 behaviour and test (c)'s "policy
         off" side; [Retention.default] is the policy and the measurement that chose it
         is in lib/core/retention.ml's header. Swappable for the same reason [reduction]
         and [pb_criterion] are (D-0044): the interesting alternatives are not
         parameterisations of one another. *)
  backjump_on_pb : bool;
      (* M2-L15's BREAK, and the thing this row exists to refuse. OFF.

         On, the branch nogood is filtered by the level set the LEARNED PB ROW names
         ([Pb_analysis.levels]) instead of by the decision closure's
         ([Learn.levels]). That is the rule a reader arrives with -- M2-L13 gave the PB
         row a propagator, so surely the row can drive the backjump too -- and it is
         unsound for a reason that has nothing to do with propagation: the nogood is a
         clause over DECISIONS, and the row's levels are not a statement about which
         decisions the conflict rests on. [stats.n_level_narrower] counts the conflicts
         at which the two disagree in the dangerous direction, and on every one of those
         this knob emits a clause the checker cannot re-derive.

         Wrong on purpose and NOT CLI-reachable, exactly as [break_i_s4],
         [break_ladder_mult] and [break_pb_degree] are. test/unit/test_pb.ml runs it and
         asserts the rejection's wording. *)
  bnb : bnb option;
      (* M5-T1. [None] is a satisfaction search and is every pre-M5 caller's behaviour
         unchanged: [dfs] returns [NSat] at the first solution exactly as it always did.
         [Some] turns the same tree into a branch-and-bound search -- see [type bnb]
         above and [record_improving] below.

         It lives on [config] rather than being threaded as an argument because that is
         what [config] is: the record that says how this solve behaves. It is NOT one of
         the swappable components D-0044 is about, and it is not a break lane; it is the
         one field here that carries mutable state, which [type bnb] justifies. *)
  propagate_learned : bool;
      (* M2-L12. Whether a learned clause gets a runtime consumer: a unit becomes a
         global bound tightening applied at every node, a wider one becomes a
         [Clause.Learned_clause] instance registered with the engine. ON.

         OFF is exactly the pre-M2-L12 build -- every learned constraint proof-only,
         which is D-0044 fork (ii) as lib/core/learn.ml's header took it -- and it is
         here for the same reason [pb_ladder] is: an improvement that cannot be switched
         off is an improvement nobody can measure. It is also what makes test (a)'s break
         possible, which is the obligation "assert the bound moves, and that it does NOT
         without step 1" states in one sentence.

         Turning it off does not make the proof different in kind, only smaller: the
         learned constraints still go on the page, nothing cites them, and
         [Retention]'s citation guard has nothing to guard. *)
}

let default_config =
  {
    learn = true;
    policy = Learn.Strongest;
    break_i_s4 = false;
    pb = true;
    pb_ladder = true;
    break_ladder_mult = false;
    break_pb_degree = false;
    reduction = Reduce.round_to_one;
    pb_criterion = Pb_analysis.assertive_slack;
    retention = Retention.default;
    backjump_on_pb = false;
    propagate_learned = true;
    bnb = None;
  }

let no_learning = { default_config with learn = false; pb = false }

(* Retention off: every learned constraint is held until the search ends, which is what
   this solver did before M2-L4. The control side of test (c). *)
let no_retention = { default_config with retention = Retention.keep_all }
let no_pb = { default_config with pb = false }

(* M2-L12 test (a)'s control side: learning on, every learned constraint proof-only. The
   build lib/core/learn.ml's header describes, in which the backjump "would re-reach the
   same fixpoint, re-take the same decision and re-derive the same conflict". *)
let no_propagate_learned = { default_config with propagate_learned = false }

(* ------------------------------------------------------------------- nogoods

   The decision stack as a nogood: one literal per decision, negated, paired with the
   level that decision was taken at. [decisions] is most-recent first and each branch
   opens exactly one level, so the i-th entry sits at [top - i]. *)
let levelled_nogood decisions ~top : nogood =
  List.mapi (fun i l -> (Lit.negate l, top - i)) decisions

(* The level a nogood is FILED at: the deepest decision level it names, or 0.

   docs/ROADMAP.md M2-L3: "attach the clause at the backjump level, not the level being
   retired". That is this function, and it is the whole resolution of the tension the row
   names. The nogood is consumed by the frame owning its deepest level -- every frame
   between there and the conflict skips its sibling and passes the nogood up untouched --
   so it must survive their wipes and die with that frame's. [Writer.fresh] tags an id at
   the writer's CURRENT level, which is the conflict's, so emitting it where it is derived
   is exactly what gets it deleted on the way out (D-0045's addendum). [Justify.with_level]
   is M2-L1's entry point for moving the level for real, in both formats, and it is the
   entry point this row was told to check for and did find. *)
let filed_at (ng : nogood) = List.fold_left (fun a (_, l) -> Stdlib.max a l) 0 ng

(* Emit a branch nogood at the level it is filed at. The writer is left where it was:
   [branch] owns the level marker either side of this and D-0018 point 4 depends on it. *)
let emit_nogood ctx (ng : nogood) : Writer.cid =
  Justify.with_level ctx (filed_at ng) (fun () ->
      Justify.emit ctx (Explanation.clause (List.map fst ng)))

let mentions_level (ng : nogood) lvl = List.exists (fun (_, l) -> l = lvl) ng

(* [Learn.minimise_with], with what it removed recorded. See [stats.n_min_dropped]. *)
let minimise stats policy (xs : nogood) : nogood =
  let out = Learn.minimise_with policy xs in
  stats.n_min_dropped <- stats.n_min_dropped + (List.length xs - List.length out);
  out

(* Resolve two sibling nogoods on the decision they disagree about, then minimise.

   Dropping every pair at [lvl] from the union IS the resolution step: the two clauses
   carry [l] and [~l] there and nothing else at that level, so the resolvent is the rest
   of both. It is [rup] for the checker because both parents are still live -- which is
   why the wipe comes after (D-0018 point 4). Deduplicated by literal, then ordered by
   descending level, so the result is a function of the two clauses and not of the order
   they were built in (test (f)). *)
let combine_nogoods stats policy (a : nogood) (b : nogood) ~lvl : nogood =
  let joined = List.filter (fun (_, l) -> l <> lvl) (a @ b) in
  let deduped =
    List.fold_left
      (fun acc (l, i) ->
        if List.exists (fun (m, _) -> Lit.equal m l) acc then acc else acc @ [ (l, i) ])
      [] joined
  in
  minimise stats policy
    (List.stable_sort (fun (_, i) (_, j) -> Stdlib.compare j i) deduped)

(* ------------------------------------------------------------------------------ dfs *)

(* [decisions] is the stack of literals actually forced true so far by branching,
   most-recent decision first -- so [List.map Lit.negate decisions] is, at every
   point, exactly the nogood clause that would state "not all of these hold". *)
(* D-0018 point 4, made loud. The nogood cites decisions that live at [lvl]; the [w]
   that retires them must come *after* it, and the writer must already have stepped down
   to the parent level, or the nogood is filed at a level its own [w] is about to wipe.
   Under the audit the id is checked to be live as well, which catches the same mistake
   made one call earlier. *)
let wipe_after_nogood ctx ~lvl ~nogood =
  Debug.check
    "D-0018.4: the nogood is emitted, at the parent level, before the branch's level is \
     wiped" (fun () ->
      Writer.current_level ctx.Justify.writer < lvl
      &&
      let w = ctx.Justify.writer in
      (not (Writer.auditing w)) || Writer.is_live w nogood);
  Justify.wipe_level ctx lvl

(* Does this derivation rest on a clausal reason?

   docs/DECISIONS.md D-0013 closed the no-decision case with "the propagator's own
   derivation *is* the contradiction", and for [int_lin_le] it is: a row whose slack has
   gone negative weakens every other variable out, divides, and adds down to a numeric
   [0 >= k], which veripb reads as a contradiction directly. That sentence was written
   when [int_lin_le] was the only propagator there was, and it is false for a clausal
   reason. A [Clause] says "not all of these variables take these values at once"
   (D-0019): a perfectly good constraint, and not a contradiction -- veripb says so in
   as many words, at the [conclusion] line rather than at the rule, which is what makes
   the mistake hard to read off the output.

   The rejection is worded "The constraint with ID <n> is not contradicting, as specified
   by the hint" (veripb 3.0.2, the checker of record). Measured, not guessed.
   lib/core/prop/ne.ml's header and test/unit/test_random.ml carry the same wording, and
   that test matches on it so that this failure is DIAGNOSED rather than merely caught:
   a lane that only knows "the checker said no" reports a known bug as a brand-new one.

   It reaches the root arm two ways, and this predicate is deliberately structural so
   that it catches both: the propagator's conflict explanation can BE a [Clause]
   ([int_ne] conflicting with every variable fixed), or a [Combine] can have folded one
   into its arithmetic as a cited summand ([int_lin_le] citing the trail entry that last
   moved a bound, where the entry is a disequality's -- D-0019's last consequence). The
   second is sound as a [pol] step, which is why nothing louder happens at the rule
   itself: a [pol] derives whatever it derives, here something valid that simply is not
   what the row's own slack argument claimed, because a clause over several variables
   does not cancel this row's coefficient for the one variable the way a chain-sum over
   that variable's declared range does (lib/core/prop/linear.ml's header states that
   contract).

   Either way the honest close is the one D-0018 already uses everywhere else: write the
   trace, then state the contradiction as a [rup] the checker verifies for itself. *)
(* Is this derivation's row stated in the DIRECT encoding's currency -- a counting
   argument over x_eq_v -- rather than in the order encoding's ladder currency? (M4-T2.)

   The two vocabularies are not interchangeable and a [pol] that adds a row from one to a
   row from the other derives something valid that is neither side's claim
   (lib/core/prop/linear.ml's header states the contract its division depends on; D-0010
   and lib/core/ladder.ml state the other). Nothing in an [Explanation.t] says which row
   a sub-derivation concludes -- that is D-0064's "nothing in the tree tells my own
   sub-derivation from someone else's cited one" -- but the LINES it names do say it, and
   [Encoding.is_direct_row] is the lookup. A derivation that names a channelling half or
   an at-least-one line is a counting row; one that names only .opb model rows and ladder
   rungs is not.

   The pairwise disequality rows [Encoding.add_all_different] posts are clauses over
   ORDER literals and are deliberately not counted (see [is_direct_row]'s own comment):
   [Ne] cites them without leaving the ladder. *)
let rec is_counting_row encoding (e : Explanation.t) =
  match Explanation.force e with
  | Explanation.Model_row id -> Encoding.is_direct_row encoding id
  | Explanation.Clause lits -> List.exists (fun (l : Lit.t) -> Lit.is_direct l.Lit.v) lits
  | Explanation.Linear (terms, _) ->
      List.exists (fun (_, (l : Lit.t)) -> Lit.is_direct l.Lit.v) terms
  | Explanation.Decision _ -> false
  | Explanation.Cut (a, b, _, _) ->
      is_counting_row encoding a || is_counting_row encoding b
  | Explanation.Combine (summands, _) ->
      List.exists
        (function
          | Explanation.Term (_, e) -> is_counting_row encoding e
          | Explanation.Weaken lits ->
              List.exists (fun (_, (l : Lit.t)) -> Lit.is_direct l.Lit.v) lits
          | Explanation.Defining (_, (l : Lit.t)) -> Lit.is_direct l.Lit.v)
        summands
  | Explanation.Deferred _ -> false (* [force] returns a non-deferred head *)

(* Does this [Combine] mix the two currencies at its own top level? (M4-T2, and the fix
   for the defect D-0064 bounded and left open at this line.)

   D-0064's rule was structural in the wrong place: it read the PRESENCE of a [Defining]
   (or, before it, of a [Clause]) and routed on that. What it was standing in for is the
   question above -- and the case that proves it is the one D-0064 wrote down and could
   not fix: an [int_lin_le] conflict that folds in an [all_different] entry with NO moved
   bound has no [Defining] and no [Clause] anywhere, so the old rule called it closing,
   `conclusion UNSAT` cited a row that is not contradicting, and 3.0.2 would have said
   so. No shipped model reached it, which is why it shipped.

   Asked directly the question is decidable from the ids: a top-level [Combine] that adds
   an ORDER-currency model row (its own .opb row -- what [Linear], [Lin_eq], [Ne] and
   every M1 propagator build from) to a DIRECT-currency counting row cited as a [Term] is
   a sound [pol] that does not close, and D-0022's route is the right one.

   TOP LEVEL ONLY, the same boundary and the same reason as [Explanation.top_weaken_owners]
   and as D-0064's: the question is only well posed about the row this conflict itself
   claims is contradictory. Inside [pair_amo] an order-currency .opb disequality row and a
   direct-currency channelling half are added together on purpose -- that is what the
   division is for -- so a recursive reading would answer "mixed" about every correct Hall
   derivation there is.

   Erring [true] is erring safe: it costs the citation, never the refutation. *)
let mixes_currencies encoding (summands : Explanation.summand list) =
  let order_model_row = function
    | Explanation.Term (_, e) -> (
        match Explanation.force e with
        | Explanation.Model_row id -> not (Encoding.is_direct_row encoding id)
        | _ -> false)
    | _ -> false
  in
  let counting_term = function
    | Explanation.Term (_, e) -> is_counting_row encoding e
    | _ -> false
  in
  List.exists order_model_row summands && List.exists counting_term summands

(* Does this derivation ask the claim index for an id at its own top level? See the
   root-conflict arm in [dfs], which is the only caller and states why it matters. *)
let top_defining (e : Explanation.t) =
  match Explanation.force e with
  | Explanation.Combine (summands, _) ->
      List.exists (function Explanation.Defining _ -> true | _ -> false) summands
  | _ -> false

let rests_on_a_clause encoding (e : Explanation.t) =
  let rec go ~cited (e : Explanation.t) =
    match Explanation.force e with
    | Explanation.Clause _ -> true
    | Explanation.Decision _ | Explanation.Model_row _ | Explanation.Linear _ -> false
    | Explanation.Cut (a, b, _, _) -> go ~cited:true a || go ~cited:true b
    | Explanation.Combine (summands, _) ->
        ((not cited) && mixes_currencies encoding summands)
        || List.exists
             (function
               | Explanation.Term (_, e) -> go ~cited:true e
               | Explanation.Weaken _ -> false
               (* M4-T7 / D-0009, and [cited] exists for this case alone.

                  A [Defining] cancels a bound literal out of THE ROW ITS OWN [Combine] IS
                  BUILDING, citing a UNIT line ([Justify.defining_lit], which states the
                  literal outright if nothing has). At the top level that row is the one this
                  conflict claims is contradictory, the cancellation is exact -- the term goes
                  and the degree stays -- and the [pol] really does close, which is the whole
                  difference from a [Clause] summand: a clause may be any width and its
                  cancellation is not.

                  Beneath a [Term] it is a different row: one ANOTHER propagator instance
                  built, folded in here at this combine's own coefficient. A Hall row is a
                  counting argument over the direct encoding, not the per-variable
                  declared-range chain [Linear]'s division needs (D-0010,
                  lib/core/prop/linear.ml's header), so the citing combine is a sound [pol]
                  that does not close and D-0022's route is the right one --
                  test/models/alldiff_hall_trace_unsat.fzn is exactly that conflict. This is
                  the same top-level-only boundary, drawn for the same reason, as
                  [Explanation.top_weaken_owners]: nothing in the tree tells "my own
                  sub-derivation" from "someone else's cited one", so the question is only
                  well posed where the derivation is its own. Erring [true] is erring safe --
                  it costs the citation, never the refutation. *)
               (* M4-T7 / D-0009. A [Defining] cancels a bound literal out of the row its
                  own [Combine] is building, citing a UNIT line ([Justify.defining_lit],
                  which states the literal outright if nothing has): the term goes, the
                  degree stays, and the [pol] closes. D-0064 had to answer [cited] here,
                  because the presence of a [Defining] was the only thing standing between
                  a cited counting row and a conclusion that cites it. [mixes_currencies]
                  above now asks that question directly, so this arm can say what is
                  actually true about a [Defining], which is that it never makes a
                  derivation clausal. *)
               | Explanation.Defining _ -> false)
             summands
    | Explanation.Deferred _ -> false (* [force] returns a non-deferred head *)
  in
  go ~cited:false e

(* A root conflict whose derivation rests on a clause, closed the D-0018 way.

   Three lines, in this order, and the order is the same one the under-a-decision arm
   uses for the same reason (D-0018 point 4 and [Trace]'s header):

   1. the branch's trace -- here the *root's* trace, every level-0 pruning. D-0021: a
      [rup] check starts from nothing and does not inherit the solver's root fixpoint,
      so the bounds this conflict rests on have to be on the page before anything can
      unit propagate to them. This is exactly the measurement D-0021 records for
      `offset`, arrived at from the other end.
   2. the conflict's own reason line, when the propagator recorded facts for it
      (D-0018 point 3).
   3. the propagator's own derivation, which is emitted even though it is not the
      contradiction: it is still a valid consequence, and it leaves the empty clause one
      unit propagation away rather than a search away.

   Then the contradiction itself, as the empty clause. That is not a new rule or a new
   shape -- it is [rup >= 1 ;], the nogood over an empty decision stack, i.e. what the
   decision arm below emits with [decisions = []] substituted in. Citing *it* rather
   than the derivation is the whole fix: what [conclusion UNSAT] names is now a line
   veripb has checked to be a contradiction, not one this module asserted was. *)
let close_root_conflict ctx trace store (c : Store.conflict) =
  let e = c.Store.c_why in
  Trace.emit ctx trace store;
  let _ : Writer.cid option = Trace.conflict_line ctx trace c in
  match Explanation.force e with
  | Explanation.Clause [] ->
      (* Already the empty clause -- a disequality every one of whose variables the
         model declares fixed (D-0019). Emitting it twice would be silly. *)
      Justify.emit ctx e
  | _ ->
      let _ : Writer.cid = Justify.emit ctx e in
      Justify.emit ctx (Explanation.clause [])

(* ------------------------------------------------- a decision that settled at a hole

   M1-T55, and the other half of the sentence in [random_order]'s header above.

   [spec_order] splits at [d_split = lo] and [explore_ge] pushes [set_lo v (lo + 1)].
   [Domain.settle] re-establishes I-D2 by walking a bound over a hole, so when [lo + 1]
   is a hole the trail entry records [x >= m] for the next value [m] actually in the
   domain, while the literal that branch assumed -- and the one its nogood negates -- is
   [x_ge_(lo+1)]. The nogood therefore claims to have refuted [x >= lo + 1] on the
   strength of having explored only [x >= m].

   That claim is *true*. The values [lo + 1 .. m - 1] are excluded by constraints (I-P1),
   and where a propagator needed an ancestor decision to exclude them the nogood is
   conditioned on exactly those decisions. What is not automatic is that veripb can
   *find* it. A [rup] check asserts the decisions and unit propagates one constraint at a
   time; a pure hole removal moves no bound, so lib/core/trace.ml's [claims] writes no
   line for it (that function says so itself, and M1-T56 is the same sentence from the
   other end). The exclusion is on the page only as whatever the punching constraint's
   own rows happen to unit propagate.

   For every propagator M1 has, that is enough -- which is why M2-T11 measured 2051 hole
   splits out of 495723 over 108000 runs with **not one veripb rejection**. A hole is
   punched only by a disequality (lib/core/prop/ne.ml, [int_lin_ne]); its .opb encoding
   is a bounded number of rows over that constraint's own literals; and PB unit
   propagation over one such row reproduces exactly the bounds reasoning the propagator
   did, given the other terms' bounds -- which are on the page either as a trace line or
   as a decision the nogood itself asserts. So the proof has been resting on a property
   of *the encoding of the current propagator set*, stated nowhere and checked by
   nothing. M4's [all_different] prunes from a Hall set, whose reason is not one row, and
   that property ends there.

   Two routes were open (docs/ROADMAP.md M1-T55). Guarding [spec_order] the way
   [random_order] was then guarded was rejected: the split would no longer be at [lo],
   which is docs/SPEC.md 3.4's indomain_min, so it is a normative change that moves every
   model's proof to pay for a defect that has never been observed -- and that guard was
   not total anyway, its fallback after eight misses being [lo] itself, which is where it
   refused to land. (M1-T45 has since removed it outright; the argument above is what
   made that possible, and [random_order]'s header records the evidence.) Making the
   decision's trail entry land exactly on the literal its nogood negates was rejected
   because **it cannot be done**: the low side lands exactly iff [k] is in the domain and
   the high side iff [k + 1] is, so demanding both is demanding that old guard's
   condition, and a complementary literal pair at a hole boundary always leaves one side
   settling. Choosing the literal from the settled bound
   instead only moves the gap to the other side, where it is worse: the two children's
   nogoods then no longer resolve on one literal.

   So the missing step is written down instead. [bridges] emits, for each decision on the
   path whose push settled past a hole, one line

       rup 1 <the bound the trail recorded> 1 ~<the bound the decision assumed>
              1 ~<each ancestor decision> >= 1 ;

   read as a clause: "under these decisions, [x >= lo + 1] implies [x >= m]". It is
   globally valid -- every ancestor it rests on is negated into it, which is form (a) of
   this module's header -- and it is exactly the one fact the nogood's own check has been
   deriving implicitly all along. It is emitted lazily, after [Trace.emit] and before the
   nogood, because D-0021: a [rup] does not inherit the solver's root fixpoint, so the
   trace the exclusion propagates along has to be on the page first.

   What that buys is the point. The implicit dependency becomes a line veripb checks at
   the decision that made it, naming the variable and both bounds, so when it stops
   holding the proof is rejected *there* rather than at a nogood several inferences away
   -- or, worse, accepted because some other route through the branch happened to close.
   It also retires M1-T45, and M1-T45 has now taken it up: with the bridge on the page a
   hole split is harmless, so [random_order] no longer refuses one and the 0.4% of tree
   shapes it used to give up are back. [test_hole_split_sweep] is the evidence.

   It changes no tree. No order, no split, no domain and no decision literal is touched;
   a run that never splits at a hole emits byte-for-byte the proof it emitted before, and
   [solve]'s "the default is byte-for-byte the tree this module has always built" still
   holds -- for the tree *and*, on every model in test/models/ but the one added for this
   task, for the bytes. *)

(* The decision pushes of the open levels, oldest first, each with the trail index it
   sits at: each is the first trail entry of its own level, which is what
   [check_decision_landed] and [Store.is_level_start] assert from their two sides. A level
   that has been opened but whose push has not landed (the [Store.Conflict] arms of
   [explore_le]/[explore_ge]) contributes no entry, which is what makes the walk below
   line up on the ancestors and drop the literal that never made it onto the trail.

   The index is carried because [Store.remover] is asked "which entry took [v] out of
   this variable's domain *before* this point", and the point is a trail position. It is
   the same ~before [Trace.settle_facts] passes for a propagator's settle; M1-T66 asks it
   for a decision's. *)
let decision_entries store =
  let n = Store.trail_length store in
  let acc = ref [] in
  for i = n - 1 downto 0 do
    if Store.is_level_start store i then acc := (i, Store.trail_entry store i) :: !acc
  done;
  !acc

(* Did this push land somewhere strictly stronger than its literal names, and if so on
   what? [Some cond] is the bound the trail actually recorded; [None] means the push
   landed exactly and there is nothing to bridge, which is the overwhelmingly common
   case -- and, before M1-T45, the only one [random_order] would produce.

   The literal's polarity says which side the branch took: [x_ge_b] is the high side, so
   the low bound moved and lands exactly on [b]; [~x_ge_b] is [x <= b - 1], so the high
   bound moved and lands exactly on [b - 1].

   M1-T66 adds the second half of the answer: *which holes* the push walked over to get
   there. They are the run of holes of the pre-push domain between the literal's own
   bound and the one the trail recorded, and they are what the bridge's [rup] silently
   depends on -- [Trace.holes_below]/[holes_above] are the same two functions
   [Trace.lines] uses for a propagator's settle, asked here for a decision's. Their run
   can reach past the literal's bound (it stops at the first value the domain still
   holds, which may be below it), so it is trimmed to the values the push actually
   crossed rather than trusted wholesale. *)
let settled_bound encoding (e : Store.entry) name (l : Lit.t) =
  let b = Lit.value l.Lit.v in
  if l.Lit.positive then
    let m = Domain.lo e.Store.now in
    if m <= b then None
    else
      let holes = List.filter (fun v -> v >= b) (Trace.holes_below e.Store.old m) in
      Some (Encoding.ge encoding name m, holes)
  else
    let h = Domain.hi e.Store.now in
    if h >= b - 1 then None
    else
      let holes = List.filter (fun v -> v <= b - 1) (Trace.holes_above e.Store.old h) in
      Some (Encoding.le encoding name h, holes)

(* Does this entry plausibly belong to this decision literal? The walk pairs two lists
   that are built independently -- the open levels' pushes from [Store], the assumed
   literals from [dfs]'s own recursion -- and a pairing that has slipped would write a
   line about the wrong variable, which is the kind of mistake that verifies anyway
   (a true clause about some other variable is still a true clause). So it is checked
   rather than assumed, and a mismatch stops the walk instead of guessing. *)
let aligned store (e : Store.entry) (l : Lit.t) =
  Lit.is_order l.Lit.v
  && String.equal (Store.name store e.Store.var) (Lit.owner l.Lit.v)
  &&
  if l.Lit.positive then Domain.lo e.Store.now > Domain.lo e.Store.old
  else Domain.hi e.Store.now < Domain.hi e.Store.old

(* ------------------------------------------------------------------------- M1-T66

   Why its absence is invisible, and what this record does about it.

   The bridge says "under these decisions, [x >= b] implies [x >= m]". When veripb checks
   the nogood it asserts every decision and unit-propagates, and it reaches [x >= m] on
   its own by two independent routes, either of which suffices:

     1. the hole's own trace line. Since M1-T56 an interior hole gets a line of its own,
        the clause [x <= v-1 \/ x >= v+1], and [Trace.emit] has already put every such
        line on the page by the time [bridges] runs (D-0021 fixes that order). Asserting
        [x >= b] falsifies [x <= b-1], so the hole line at [v = b] unit-propagates
        [x >= b+1], and a run of holes chains;
     2. failing that, the disequality's own [.opb] rows. I-X10: [Ne] is the only thing in
        M1 that punches a hole, and [int_lin_ne]'s two big-M rows unit-propagate the
        exclusion once the bounds on the line's own tail are assumed.

   Route 2 is in the model file and can never be retired, so within M1's constraint
   vocabulary there is no scene in which removing this function makes a checker reject.
   That is not an argument for removing it -- it is an argument that M1 cannot *observe*
   it, which is a different statement and a weaker one. M2-L3's learned clauses cite
   across levels, which is exactly the case I-S4's level argument does not cover, and the
   settle step is what those citations need to be able to name.

   So what this function now leaves behind is the derivation, as data: [record_bridge]
   files a [bridge] on [stats], and [Trace.record_citation] files one I-S4 edge per hole
   whose line the page names. Both are checkable without reading a byte of the proof, and
   the second puts the decision settle inside the invariant audit it was previously
   outside of. [test/unit/test_matrix.ml]'s [bridge_derivation] is the test that reads
   them. *)
let bridges (ctx : Justify.ctx) trace stats store (decisions : Lit.t list) =
  let rec go entries rev_decisions ancestors =
    match (entries, rev_decisions) with
    | [], _ | _, [] -> ()
    | (i, (e : Store.entry)) :: es, (l : Lit.t) :: ls ->
        if not (aligned store e l) then
          Debug.check
            "M1-T55: the open levels' pushes and the assumed decision literals line up"
            (fun () -> false)
        else
          let name = Store.name store e.Store.var in
          (match settled_bound ctx.Justify.encoding e name l with
          | None -> ()
          | Some (cond, holes) -> (
              match
                Trace.claim_of_cond ~what:"the bound a decision settled onto" ~name cond
              with
              | None ->
                  (* The settled bound is the declared one, so the claim is vacuous and
                     no literal exists to state it -- nothing to bridge. *)
                  ()
              | Some claim ->
                  (* A push that landed strictly stronger than its literal landed there
                     because [Domain.settle] walked it over something. If that run is
                     empty the two halves of this module disagree about what a settle is,
                     and the bridge below would be a line with nothing under it. *)
                  Debug.check
                    (Printf.sprintf
                       "M1-T66: %s settled onto %s, so the push crossed at least \
                        one                         hole"
                       (Lit.to_string l) (Lit.to_string claim))
                    (fun () -> holes <> []);
                  let lits = claim :: Lit.negate l :: List.map Lit.negate ancestors in
                  let origin =
                    Printf.sprintf "M1-T55: %s settled onto %s" (Lit.to_string l)
                      (Lit.to_string claim)
                  in
                  let cid = Justify.emit_rup_clause ctx ~origin lits in
                  let level = Writer.current_level ctx.Justify.writer in
                  let cited, unnamed =
                    List.fold_left
                      (fun (cited, unnamed) v ->
                        match Store.remover store ~before:i ~var:e.Store.var v with
                        | None -> (cited, v :: unnamed)
                        | Some rem -> (
                            match Trace.hole_line_of trace rem v with
                            | None -> (cited, v :: unnamed)
                            | Some w ->
                                Trace.record_citation trace ctx.Justify.writer ~citing:cid
                                  ~citing_level:level ~cited:w.Trace.w_cid
                                  ~cited_level:w.Trace.w_level ~hole:v;
                                ((v, w.Trace.w_cid, w.Trace.w_level) :: cited, unnamed)))
                      ([], []) holes
                  in
                  record_bridge stats
                    {
                      br_var = name;
                      br_assumed = l;
                      br_settled = claim;
                      br_ancestors = ancestors;
                      br_holes = holes;
                      br_cited = List.rev cited;
                      br_unnamed = List.rev unnamed;
                      br_cid = cid;
                      br_level = level;
                    }));
          go es ls (l :: ancestors)
  in
  go (decision_entries store) (List.rev decisions) []

(* M2-L3: take the cut, discharge I-S4, put the learned clause on the page, and report
   the decision levels the conflict actually rests on.

   [None] means "learn nothing here", and every route to it is a route the search already
   handled before this row existed: learning off, an [Analysis] error, a criterion whose
   postcondition did not hold, or a cut that materialises no literal. The caller then
   builds the nogood over the whole decision stack, which is M1's behaviour unchanged. A
   failure to learn is never a failure to solve.

   The ORDER of the three steps here is the invariant, not an implementation detail. The
   trace lines and the conflict line are already on the page (the caller emitted them);
   the learned clause's [rup] is checked against them; and nothing has been wiped yet. The
   [break_i_s4] arm retires the conflict level first, which is the same three steps in the
   wrong order and is exactly what test (b) asserts the checker rejects. *)
(* M2-L13 / D-0054: give the learned PB ROW a runtime consumer.

   This is the row's whole point, so it is worth saying what it is NOT. It is not a
   conversion: nothing here asks [Learned.to_linear_row] whether the row can be read back
   as an integer linear row over the declared box. That predicate was a PROOF-side test
   standing in for a solving-side one (D-0050 named it "the right predicate used as the
   wrong gate"; D-0054 named why), and M2-L13 took it out of this path entirely --
   [Learned.to_linear] and [Learned.instance] are gone, and [to_linear_row] survives only
   as [n_pb_converts], which bin/main.ml already labels MEASURED ONLY.

   What replaces it is [Pb.of_terms], which instantiates the row AS A PB CONSTRAINT over
   the order literals it already names, and declines only on a literal that has no bound
   to move ([Lit.Eq]) or a name the encoding does not declare. Those are the two refusals
   [Clause.of_lits] and [global_of] already make, for the same reasons.

   AND TELL RETENTION IT HAS ONE, exactly as M2-L12's [register_learned] does: a trace
   line from a registered instance is RUP only while the learned constraint is on the
   page, so [Retention.cite] must refuse eviction of this id. The cap is SOFT since
   M2-L12, so a cited constraint is refused eviction and the refusal is counted; this row
   creates more citations and nothing else about that mechanism changes.

   THE EMPTY CONTRADICTION IS REGISTERED TOO, deliberately. A row with no terms and a
   positive degree is the constraint `0 >= b`, i.e. FALSE, derived by [pol] from model
   rows alone and stated at level 0 -- so if it is on the page at all the model is
   unsatisfiable, and a propagator for it conflicting at the next node is the correct
   reading of the object rather than a degenerate case to special-case away. Suppressing
   it would be deciding, on this side, that the proof-side derivation is not to be
   believed. [Search.n_pb_nondegenerate] is how many rows are not this. *)
let register_learned_pb engine store ctx stats ~bump ~cid ~(row : Learned.t) =
  let decl = Learned.decl_of_encoding ctx.Justify.encoding in
  let id = Engine.next_id engine in
  match Learned.pb_instance ~id ~row_id:cid ~bump store ~decl row with
  | None -> stats.n_pb_inst_declined <- stats.n_pb_inst_declined + 1
  | Some inst ->
      Engine.add engine inst;
      stats.n_pb_instances <- stats.n_pb_instances + 1;
      stats.pb_inst_ids_rev <- id :: stats.pb_inst_ids_rev;
      Retention.cite stats.db ~cid
        ~by:
          (Printf.sprintf "learned_pb instance #%d, %s (M2-L13)" id
             (Learned.to_string row))

(* ---------------------------------------------------------------------------
   M2-L15: THE BACKJUMP LEVEL, and why the decision closure is RIGHT and not merely safe
   ---------------------------------------------------------------------------

   lib/core/pb_analysis.ml's closing note handed this on by name: M2-L13 gave the learned
   PB row a runtime propagator, so the sentence "that would change the calculation" had
   stopped being hypothetical and the calculation was owed a redo. Here is the redo.

   FIRST, WHAT THE BACKJUMP IS HERE, because the CDCL word is misleading. This solver does
   not undo to a level and resume. [branch] is a recursive DFS, and the backjump is the
   arm below that says [NFail (ng1, cid1) when not (mentions_level ng1 lvl)]: the sibling
   of a decision is skipped exactly when the branch nogood does not name that decision's
   level. So THE BACKJUMP IS A FILTER ON THE NOGOOD, and the level set that filter uses is
   what [learn_at_conflict] returns.

   SECOND, WHAT THE NOGOOD IS. It is a CLAUSE OVER DECISION LITERALS, emitted as a `rup`
   and re-derived by the checker. Dropping level [j] from it is not a heuristic choice
   about where to resume; it is ASSERTING that the conflict follows from the remaining
   decisions alone. A wrong drop is not a slower search, it is a clause that is not
   entailed -- and [emit_nogood] puts it on the page, where veripb refuses it.

   THIRD, THE CURRENCY MISMATCH, which is the answer. The closure's level set answers "on
   which decisions does this conflict rest?" -- [Analysis.decision_closure] resolves every
   non-root node away at every level, so what is left is decisions, declared bounds and
   factless prunings, and [Analysis.decision_levels] says at the point it is read why that
   makes it a dependency set. [Pb_analysis.levels] answers "at which levels did this row's
   literals become falsified?", and [Pb_analysis.asserting_level] answers a third question
   again -- "how far down does this row still propagate?" -- which is the one Le Berre et
   al. (arXiv 2107.13085) show carries NO backjump guarantee over PB. None of the three is
   a rewording of another. Only the first is in the currency the nogood is stated in.

   So the decision closure is not the safe choice among candidates. It is the only
   candidate: the other two do not answer the question being asked.

   WHAT M2-L13 DID CHANGE, and it is the part worth keeping. A learned PB instance's
   pruning is an ordinary trail entry carrying reason facts ([Pb.reason_clause]), so
   [Analysis.analyse ~scope:Everywhere] resolves straight through it and the closure it
   returns already accounts for the row's antecedents -- at whatever levels those sit. The
   calculation WAS redone by M2-L13, by the closure walk, without a line of code. What did
   not change, and could not, is which set drives the filter.

   [pb_level_verdict] is that argument as a MEASUREMENT rather than as this comment. It
   puts the two sets side by side at every conflict where both exist and classifies the
   disagreement, because "they never differ" and "they differ and the PB set is narrower"
   are the two outcomes with opposite meanings and nothing here could previously tell them
   apart. [config.backjump_on_pb] is the break that takes the narrower set, and the
   checker is what says no. *)

(* [closure] and [pb] are both descending, deduplicated, level 0 dropped -- see
   [Analysis.decision_levels] and [Pb_analysis.row_levels], which agree on the shape
   deliberately so that this comparison needs no normalisation. *)
let pb_level_verdict stats ~(closure : int list) ~(pb : int list) ~asserting_level =
  let subset a b = List.for_all (fun x -> List.mem x b) a in
  stats.n_level_compared <- stats.n_level_compared + 1;
  let show ls =
    if ls = [] then "{}" else "{" ^ String.concat "," (List.map string_of_int ls) ^ "}"
  in
  if pb = [] then stats.n_level_pb_empty <- stats.n_level_pb_empty + 1;
  if closure = pb then stats.n_level_same <- stats.n_level_same + 1
  else (
    if subset pb closure then stats.n_level_narrower <- stats.n_level_narrower + 1
    else if subset closure pb then stats.n_level_wider <- stats.n_level_wider + 1
    else stats.n_level_incomparable <- stats.n_level_incomparable + 1;
    if List.length stats.level_diffs_rev < pb_reason_cap then
      stats.level_diffs_rev <-
        Printf.sprintf "closure %s vs pb %s (pb asserts at %d)" (show closure) (show pb)
          asserting_level
        :: stats.level_diffs_rev);
  (* [closure] is descending, so its last element is the lowest level it names. *)
  match List.rev closure with
  | lowest :: _ when asserting_level < lowest ->
      stats.n_level_assert_deeper <- stats.n_level_assert_deeper + 1
  | _ -> ()

(* M2-L6: PB conflict analysis, alongside the clause. [clause_converts] is whether the
   SAME conflict's M2-L3 clause would have converted, which is what makes [n_pb_stronger]
   a comparison rather than a count.

   Order: this runs AFTER [Learn.introduce] and therefore after the trace lines, the
   conflict line and the bridges. It does not have to -- the derivation cites model rows
   only, which are on the page before the first decision and are retired by nothing, so
   it is the one learned object in this solver with no ordering obligation at all. It
   runs here so that the two learned objects appear in the proof in the order a reader
   would expect, and so that [stats.learned_rev] retires them newest-first.

   The [Debug] check is lib/core/pb_analysis.ml's I-S4 discharge, made a check rather
   than left a paragraph: the derivation must cite constraint ids that are on the page at
   level 0. A [pol] citing a hole line across levels is the violation learn.ml's header
   says M2-L6's reduction steps are the first thing that could write. *)
(* M2-L15: returns the level set the learned row names, paired with its own asserting
   level -- [None] when no row was learned. The return value is DATA for
   [pb_level_verdict]; the default build compares it and acts on none of it. *)
let pb_at_conflict engine store ctx stats cfg (c : Store.conflict) ~clause_converts ~lbd
    ~decl : (int list * int) option =
  if not (cfg.learn && cfg.pb) then None
  else (
    stats.n_pb_attempts <- stats.n_pb_attempts + 1;
    match
      Pb_analysis.analyse store c ~row_of:(Engine.row_of engine store)
        ~name_of:(Engine.name_of engine)
        ~ladder_id:
          (if cfg.pb_ladder then Encoding.consistency_id ctx.Justify.encoding
           else fun _ _ -> None)
        ~break_ladder:cfg.break_ladder_mult ~reduction:cfg.reduction
        ~criterion:cfg.pb_criterion
    with
    | Pb_analysis.Fallback f ->
        stats.n_pb_fallback <- stats.n_pb_fallback + 1;
        if List.length stats.pb_fallback_rev < pb_reason_cap then
          stats.pb_fallback_rev <-
            Pb_analysis.fallback_to_string f :: stats.pb_fallback_rev;
        None
    | Pb_analysis.Learned_row t ->
        Debug.check "I-S4: a PB derivation cites only model rows, which no `w` retires"
          (fun () ->
            List.for_all
              (fun id -> id >= 0)
              (Pb_analysis.cited_ids t.Pb_analysis.derivation));
        let cid = Pb_analysis.introduce ctx t in
        stats.n_pb_learned <- stats.n_pb_learned + 1;
        stats.n_pb_steps <- stats.n_pb_steps + t.Pb_analysis.steps;
        let converts = Learned.to_linear_row t.Pb_analysis.row ~decl <> None in
        if converts then stats.n_pb_converts <- stats.n_pb_converts + 1;
        if converts && not clause_converts then
          stats.n_pb_stronger <- stats.n_pb_stronger + 1;
        (* M2-L11 test (b). [Learned.is_empty] is exactly "the empty contradiction": no
           terms left, and a degree the criterion already established is positive. *)
        if not (Learned.is_empty t.Pb_analysis.row) then
          stats.n_pb_nondegenerate <- stats.n_pb_nondegenerate + 1;
        if t.Pb_analysis.ladder_rungs > 0 then (
          stats.n_pb_lifted <- stats.n_pb_lifted + 1;
          stats.n_pb_rungs <- stats.n_pb_rungs + t.Pb_analysis.ladder_rungs);
        if List.length stats.pb_rows_rev < pb_reason_cap then
          stats.pb_rows_rev <- t :: stats.pb_rows_rev;
        stats.learned_rev <- cid :: stats.learned_rev;
        (* M2-L4. [~lbd] here is the CONFLICT's LBD -- the 1UIP clause's, from the same
           conflict -- and not the PB row's own. The row's literals come out of the
           elimination with no trail entry to read a level off, so there is no honest
           per-row figure to compute; scoring it by the conflict it came from is stated
           rather than dressed up, and a later row that gives [Pb_analysis] levelled
           literals should replace it. Registering it transfers I-X2's obligation to the
           database. *)
        ignore
          (Retention.add stats.db ~cid ~row:t.Pb_analysis.row ~lbd
             ~origin:"M2-L6 learned PB row");
        (* M2-L13. In the same place, and for the same two ordering reasons, M2-L12 put
           its own registration: AFTER [Retention.add], because [cite] replaces an
           entry's freedom to be evicted and the entry has to exist first, and BEFORE
           [reduce], so that a policy cannot evict on this very call a constraint the
           next line is about to give a consumer. *)
        if cfg.propagate_learned then
          register_learned_pb engine store ctx stats
            ~bump:(if cfg.break_pb_degree then 1 else 0)
            ~cid ~row:t.Pb_analysis.row;
        ignore (Retention.reduce stats.db ctx);
        Some (t.Pb_analysis.levels, t.Pb_analysis.asserting_level))

(* ------------------------------------------------------- M2-L12: making it propagate

   Everything below is D-0052's two steps and the retention obligation they create. See
   [type global] above for step 1's argument and lib/core/prop/clause.ml's header for
   step 2's.

   Why the two steps do NOT share a mechanism, which is the question a reader will have:
   a unit is applied by [Store.set_lo] at every node and a multi-literal clause is a
   registered propagator instance. A unit could have been a width-1 [Clause] instance and
   the code would be shorter. It is not, for two reasons that are about this engine
   rather than about taste. [Engine.add] appends to an array, so it is O(n) per
   registration and 72 units would be O(n^2) over a search. And a global applied at [dfs]
   entry is in force BEFORE the first propagation round of the node, where an instance
   would have to be woken and queued. D-0052 says step 1 "needs no clause propagator at
   all"; this is that, and the saving is real rather than notional. *)

(* The unit literal as a bound this search can move, or [None] when it is not one.

   [None] on a [Lit.Eq] literal: the direct encoding has no bound to move (a positive
   [Eq] fixes, which is two bounds from one literal; a negative one punches an interior
   hole, i.e. [Store.remove_with_facts], of which I-X10 records [Ne] is the sole caller
   in lib/ and which D-0052 told this row not to reach for). [None], too, on a name the
   ENCODING does not declare -- the declared bounds have to come from there and not from
   the store, because a learned constraint is built mid-search when the store's bounds
   are narrow, which is the hazard lib/core/learned.ml's "Why the [Linear.t] is built
   here instead of through [Linear.make]" spells out for the same reason. *)
let global_of store ~(decl : string -> (int * int) option) ~cid (l : Lit.t) :
    global option =
  match l.Lit.v with
  | Lit.Eq _ -> None
  | Lit.Ge (nm, k) -> (
      match (Store.var_named store nm, decl nm) with
      | Some x, Some (lo, hi) ->
          Some
            {
              g_lit = l;
              g_cid = cid;
              g_var = x;
              g_pos = l.Lit.positive;
              g_k = k;
              g_decl_lo = lo;
              g_decl_hi = hi;
              g_fact =
                (if l.Lit.positive then Reason.at_least ~name:nm ~decl:lo k
                 else Reason.at_most ~name:nm ~decl:hi (k - 1));
              g_expl = Explanation.clause [ l ];
            }
      | _, _ -> None)

(* M2-L13's instrument: how much a LEARNED constraint actually did at this node.

   M2-L12 reported 0 prunings from a learned clause over the whole suite, and that zero
   is the measurement D-0054 reinterprets -- so a row that claims to make learned
   constraints propagate has to be able to produce the same number, on the same
   instrument, and have it move. This is that instrument.

   It reads the TRAIL, not the propagators. Every entry carries the id of the instance
   that pushed it (M2-T7, [Store.entry.prop]), and [Engine.add] only ever appends, so an
   id at or above [first_learned_id] belongs to an instance this search registered. Which
   KIND it is comes from the two id lists, which are short (one entry per learned
   constraint) and are lists rather than hash tables because nothing in a solve may
   iterate a [Hashtbl] -- the determinism gate is exactly what a learned database
   iterated in hash order breaks.

   It is pure measurement: it returns its argument unchanged and no other code reads the
   counters. Passing a [stats] changes no byte of the emitted proof, which is the
   property [solve]'s own comment on [?stats] states. *)
let count_learned_activity stats store ~since (o : Engine.outcome) : Engine.outcome =
  let classify id =
    if id < stats.first_learned_id then ()
    else if List.mem id stats.pb_inst_ids_rev then
      stats.n_pb_prunes <- stats.n_pb_prunes + 1
    else if List.mem id stats.clause_inst_ids_rev then
      stats.n_clause_prunes <- stats.n_clause_prunes + 1
  in
  for i = since to Store.trail_length store - 1 do
    classify (Store.trail_entry store i).Store.prop
  done;
  (match o with
  | Engine.Conflict c ->
      let id = c.Store.c_prop in
      if id >= stats.first_learned_id then
        if List.mem id stats.pb_inst_ids_rev then
          stats.n_pb_inst_conflicts <- stats.n_pb_inst_conflicts + 1
        else if List.mem id stats.clause_inst_ids_rev then
          stats.n_clause_inst_conflicts <- stats.n_clause_inst_conflicts + 1
  | Engine.Fixpoint -> ());
  o

(* Apply every learned unit at this node. [Some c] is the first one that refuted it.

   The conflict is BUILT HERE rather than forwarded from the mutator, and that is not
   decoration. [Store.apply]'s [Failed] arm deliberately pairs the justification with
   [Reason.none] (its comment says why: the facts a conflict line needs are strictly more
   than the pruning's), so forwarding it would hand [Analysis] a conflict with no
   antecedents and the 1UIP walk would find nothing to learn. The fuller set is the one
   fact that makes it a contradiction: the OPPOSING bound the store already holds.
   lib/core/prop/linear.ml's [cross_conflict] and bool2int.ml's push arms do exactly this
   and for exactly this reason.

   [Store.conflict] stamps [Store.no_prop] as the reporting instance, because none is
   running -- which is the honest answer, and every consumer handles it: [Analysis] skips
   a [no_prop] antecedent by name (its [add_antecedent]), [Engine.vars_of] and [row_of]
   answer [None] out of range, and [Pb_analysis] turns that into its ordinary [No_row]
   fallback. *)
let apply_globals store stats : Store.conflict option =
  let rec go = function
    | [] -> None
    | g :: rest -> (
        let j = Reason.because ~concludes:(Some g.g_fact) Reason.none g.g_expl in
        let r =
          if g.g_pos then Store.set_lo store g.g_var g.g_k j
          else Store.set_hi store g.g_var (g.g_k - 1) j
        in
        match r with
        | Store.Unchanged -> go rest
        | Store.Changed ->
            stats.n_global_prunes <- stats.n_global_prunes + 1;
            go rest
        | Store.Conflict _ ->
            stats.n_global_conflicts <- stats.n_global_conflicts + 1;
            let d = Store.get store g.g_var in
            let nm = Store.name store g.g_var in
            let opposing =
              if g.g_pos then Reason.at_most ~name:nm ~decl:g.g_decl_hi (Domain.hi d)
              else Reason.at_least ~name:nm ~decl:g.g_decl_lo (Domain.lo d)
            in
            Some
              (Store.conflict store
                 (Reason.because ~concludes:None [ opposing ] g.g_expl)))
  in
  go (List.rev stats.globals_rev)

(* Give the learned clause a runtime consumer, and TELL RETENTION IT HAS ONE.

   The second half is the part that is easy to leave out and is the whole of step 3.
   Before M2-L12 nothing propagated a learned constraint, so [Retention]'s policy and the
   propagator set were independent -- D-0051's keep-all verdict was written on exactly
   that independence, and its own "what would reverse this" section names this row as the
   thing that ends it. A trace line from a global or from a registered instance is RUP
   only while the learned constraint is on the page. [Retention.cite] makes retiring a
   cited constraint raise [Retention.Cited] on OUR side, with a message naming the
   checker's wording, instead of the checker discovering it several lines later as
   "Trying to access constraint with ID n that has already been deleted".

   A DUPLICATE unit is not cited, and that is deliberate rather than an omission: the
   bound is already in force from the first derivation, the second constraint has no
   consumer, and leaving it uncited leaves the policy free to evict it. *)
let register_learned engine store ctx stats ~cid ~(lits : Lit.t list) =
  let decl = Learned.decl_of_encoding ctx.Justify.encoding in
  match lits with
  | [] -> ()
  | [ l ] -> (
      if List.exists (fun g -> Lit.equal g.g_lit l) stats.globals_rev then ()
      else
        match global_of store ~decl ~cid l with
        | None -> stats.n_global_declined <- stats.n_global_declined + 1
        | Some g ->
            stats.globals_rev <- g :: stats.globals_rev;
            Retention.cite stats.db ~cid
              ~by:
                (Printf.sprintf "the learned unit %s, applied at every node (M2-L12)"
                   (Lit.to_string l)))
  | _ :: _ :: _ -> (
      match Clause.of_lits store ~decl lits with
      | None -> stats.n_clause_declined <- stats.n_clause_declined + 1
      | Some p ->
          let id = Engine.next_id engine in
          Engine.add engine
            (Propagator.pack ~id
               (module Clause.Learned_clause : Propagator.S with type t = Clause.t)
               p);
          stats.n_clause_instances <- stats.n_clause_instances + 1;
          stats.clause_inst_ids_rev <- id :: stats.clause_inst_ids_rev;
          Retention.cite stats.db ~cid
            ~by:
              (Printf.sprintf "learned_clause instance #%d over %s (M2-L12)" id
                 (String.concat " " (List.map Lit.to_string (Clause.literals p)))))

(* M5-T1: the solution node of a branch-and-bound search.

   Called where a satisfaction search would have returned [NSat]. It logs the incumbent,
   yields the strictly-improving constraint, and installs the bound as a global unit --
   after which the node the solver is standing on is itself in conflict, because the
   objective variable is fixed at a value the new bound excludes. That is the whole
   trick, and it is why nothing else in [dfs] changes: the caller re-enters the node and
   [apply_globals] reports the conflict, which the ordinary conflict path then handles
   with the ordinary trace, learning, nogood and backjump.

   [`Proved] is the floor case of [type bnb]'s note (2): the improving constraint is
   already unsatisfiable, so no better solution exists and no search is needed to say so.

   THE CHECK RUNS HERE, on every improving solution, because every one of them is
   printed -- I-S1 is about solutions printed, and an optimisation run prints several. *)
let record_improving ctx store stats (b : bnb) (asn : assignment) : [ `Continue | `Proved ]
    =
  if not (b.b_check asn) then raise (Unsound_solution asn);
  let o = b.b_obj in
  let d = Store.get store o.o_var in
  (* Every variable is fixed at a solution node ([unfixed] returned nothing), so the two
     bounds agree; asserted rather than assumed because the value read here is the one the
     `soli` line and the conclusion are both built from, and a wrong one would be a wrong
     BOUNDS claim rather than a crash. *)
  if Domain.lo d <> Domain.hi d then
    invalid_arg
      (Printf.sprintf
         "Search.record_improving: objective %s is not fixed at a solution node (%d..%d)"
         o.o_name (Domain.lo d) (Domain.hi d));
  let value = Domain.lo d in
  b.b_on_solution asn;
  let bindings = List.map (fun (v, x) -> (Store.name store v, x)) asn in
  let lits = Encoding.assignment_lits ctx.Justify.encoding bindings in
  (* `soli` and not `sol`: `sol` adds nothing, and the constraint this line yields is the
     entire reason the bound below is derivable. It is also the reason the solution is
     handed over in full -- the checker PROPAGATES a logged solution, which is what lets
     it fill in the encoding auxiliaries (the `_neN` selectors of PROOF-FORMAT section 3)
     that nothing in the solver knows a value for. See [Writer.verdict]'s note on why the
     inline `conclusion SAT : <assignment>` form is unusable for the same reason. *)
  (* AT LEVEL 0, for the reason [Learned.introduce] is at level 0 (D-0045's addendum):
     the improving constraint holds everywhere in the tree from the moment it is derived,
     and a `w` at the level the solution happened to be found at would retire it out from
     under every later bound that rests on it. Found by measurement, not by foresight --
     emitted at the current level, the checker refused the conclusion with "The claimed
     upper bound of 2 mismatches the best recorded upper bound of 4", because wiping the
     constraint took the recorded bound with it. *)
  let cid =
    Justify.with_level ctx 0 (fun () ->
        Writer.improving ctx.Justify.writer ~origin:"M5-T1 improving solution" lits)
  in
  b.b_soli_ids <- cid :: b.b_soli_ids;
  b.b_best <- Some (asn, value);
  let at_limit, lit =
    match o.o_dir with
    | Minimise -> (value <= o.o_decl_lo, Lit.le o.o_name (value - 1))
    | Maximise -> (value >= o.o_decl_hi, Lit.ge o.o_name (value + 1))
  in
  if at_limit then (
    b.b_floor <- Some cid;
    `Proved)
  else
    let decl = Learned.decl_of_encoding ctx.Justify.encoding in
    match global_of store ~decl ~cid lit with
    | Some g ->
        stats.globals_rev <- g :: stats.globals_rev;
        `Continue
    | None ->
        (* [global_of] declines a literal whose variable the STORE does not know or the
           ENCODING does not declare. The objective variable is both, and [at_limit] has
           already excluded the one value for which no order literal exists, so this arm
           is unreachable -- and says so rather than silently dropping the bound, which
           would turn optimisation into enumeration of every solution. *)
        invalid_arg
          (Printf.sprintf
             "Search.record_improving: no order literal for the bound %s on objective %s \
              (declared %d..%d, incumbent %d)"
             (Lit.to_string lit) o.o_name o.o_decl_lo o.o_decl_hi value)

let rec learn_at_conflict engine store ctx trace stats cfg (c : Store.conflict) =
  if not cfg.learn then None
  else
    match
      Learn.at_conflict ~policy:cfg.policy store c ~vars_of:(Engine.vars_of engine)
        ~decl:(Learned.decl_of_encoding ctx.Justify.encoding)
    with
    | None -> None
    | Some l -> (
        (* The break: the `w` first, the derivation second. *)
        if cfg.break_i_s4 then Justify.wipe_level ctx (Store.level store);
        let ss = Learn.supports store trace l in
        let broken = Learn.support_check ctx.Justify.writer ss in
        stats.i_s4_supports <- stats.i_s4_supports + List.length ss;
        stats.i_s4_crossings <- stats.i_s4_crossings + List.length (Learn.crossings ss);
        stats.i_s4_broken_rev <- List.rev_append broken stats.i_s4_broken_rev;
        Debug.check
          (match broken with
          | m :: _ -> m
          | [] -> "I-S4: the learned clause's supports are live at its derivation")
          (fun () -> broken = []);
        let cid = Learn.introduce ctx l in
        stats.n_learned <- stats.n_learned + 1;
        let clause_converts = Learn.converts l in
        if clause_converts then stats.n_converts <- stats.n_converts + 1;
        (let b = Learn.lbd l in
         let b = if b >= lbd_buckets then lbd_buckets - 1 else b in
         stats.lbd_hist.(b) <- stats.lbd_hist.(b) + 1);
        (let w = List.length (Learn.lits l) in
         let w = if w >= lbd_buckets then lbd_buckets - 1 else w in
         stats.width_hist.(w) <- stats.width_hist.(w) + 1);
        stats.learned_rev <- cid :: stats.learned_rev;
        ignore
          (Retention.add stats.db ~cid ~row:(Learn.clause l) ~lbd:(Learn.lbd l)
             ~origin:"M2-L3 1UIP learned clause");
        (* M2-L12. AFTER [Retention.add] -- [cite] replaces an entry's freedom to be
           evicted, so the entry has to exist first -- and BEFORE [reduce], so that a
           policy cannot evict on this very call a constraint the next line is about to
           give a consumer. *)
        if cfg.propagate_learned then
          register_learned engine store ctx stats ~cid ~lits:(Learn.lits l);
        ignore (Retention.reduce stats.db ctx);
        let pb_levels =
          pb_at_conflict engine store ctx stats cfg c ~clause_converts ~lbd:(Learn.lbd l)
            ~decl:(Learned.decl_of_encoding ctx.Justify.encoding)
        in
        (* M2-L15. The comparison happens on EVERY build, including the default one that
           acts on none of it: the whole finding of this row is a pair of numbers, and a
           measurement taken only under the break knob is a measurement of the break. *)
        let closure = Learn.levels l in
        (match pb_levels with
        | None -> ()
        | Some (pb, asserting_level) ->
            pb_level_verdict stats ~closure ~pb ~asserting_level);
        match (cfg.backjump_on_pb, pb_levels) with
        | false, _ | _, None -> Some closure
        | true, Some (pb, _) ->
            (* THE BREAK. See [config.backjump_on_pb]: the row's levels are not a
               dependency set, so the nogood this filter produces claims the conflict
               rests on fewer decisions than it does. *)
            Some pb)

and dfs engine store ctx trace stats cfg (order : order) (decisions : Lit.t list) : node =
  (* M2-L12 step 1: the learned units, applied before anything else at this node. See
     [type global] on why this is where a "level-0 bound tightening" actually lands, and
     [apply_globals] on why the conflict it can report is built rather than forwarded.
     Before [Engine.propagate] and not after: a bound in force at the start of the round
     is one every propagator sees, and [Engine.propagate] enqueues every instance on
     entry anyway, so nothing has to be woken for it. *)
  let trail_before = Store.trail_length store in
  match
    count_learned_activity stats store ~since:trail_before
      (match apply_globals store stats with
      | Some c -> Engine.Conflict c
      | None -> Engine.propagate engine store)
  with
  | Engine.Conflict c -> (
      (* M2-T7: [c] carries the reporting instance's id ([c.Store.c_prop]) as well as its
         explanation and its bound facts. M2-L3's resolution starts from exactly this
         constraint. *)
      let e = c.Store.c_why in
      match decisions with
      | [] ->
          (* D-0013: with no decision active there is nothing to negate. Where the
             propagator's own derivation really *is* the contradiction -- the [pol]
             chain M1-T12 exists to build -- emitting it and citing it is still the
             answer, and a bare clause there would be the "trust me" that D-0012
             recorded veripb rejecting. Where it is not, [close_root_conflict] takes
             over; [rests_on_a_clause] above is the difference and says why.
             Nothing has been branched on yet, so the trace this writes is the root's
             own: [dfs] reaches this arm with [decisions = []] only on the very first
             call. Nothing is learned here either -- a conflict under no decision is
             already the strongest nogood there is. *)
          let cid =
            if rests_on_a_clause ctx.Justify.encoding e then
              close_root_conflict ctx trace store c
            else (
              (* M4-T2. A [Defining] resolves through the claim index to "the UNIT line
                 already stating the bound (the trace line, in practice)" -- D-0064's own
                 words -- and mints one only if there is none. On THIS arm there is no
                 trace: nothing has been branched on, so nothing wrote one, the claim
                 index is empty, and every [Defining] falls through to a minted
                 `rup <lit> >= 1`. That line is only accepted if the model entails the
                 bound by unit propagation alone, which is a property of the model and
                 not something the propagator can promise. It held for every bound M4-T1
                 and M4-T7 reached; M4-T2 reached one it does not hold for -- a bound the
                 `int_lin_le` row sets only after Regin's holes let it settle past them --
                 and 3.0.2 refused the minted line, correctly.

                 So write the branch's trace first, which is what the design assumed all
                 along: every landed pruning's line goes on the page, the claim index
                 holds it, and the [Defining] cites a line that is there rather than
                 minting one. The lines are globally valid and decision-free (there are
                 no decisions here), so this changes nothing about what the proof says --
                 only about what it contains.

                 Gated on the derivation actually HAVING a [Defining] at its top level,
                 so a root conflict that cites nothing keeps the shape it had. *)
              if top_defining e then Trace.emit ctx trace store;
              Justify.emit ctx e)
          in
          NFail ([], cid)
      | _ ->
          (* D-0018, in the order the record gives: the branch's own propagation trace
             first, then the conflict's reason line, then the nogood. Each of the first
             two is globally valid and decision-free; only the last one mentions the
             decisions, and it is RUP precisely because the other two are there to unit
             propagate along.

             M2-L3 inserts the learned clause between the bridges and the nogood, which is
             the one place it can go: after everything its [rup] rests on and before
             anything that retires them. *)
          Trace.emit ctx trace store;
          (match Trace.conflict_line ctx trace c with
          | Some _ -> ()
          | None -> (
              (* M4-T2 / D-0040, the same remedy [Trace.derive_ahead] applies to a
                 PRUNING, applied to a conflict.

                 A conflict states itself one of two ways. With bound facts,
                 [Trace.conflict_line] writes `rup ~fact ... >= 1` -- "these bounds are
                 jointly impossible" -- and the nogood unit-propagates along it. With
                 NO facts it writes nothing, and until M4-T2 nothing else did either: the
                 nogood was left to reach the contradiction by unit propagation over the
                 model rows alone. For a disequality conflicting with everything fixed
                 that works, which is why it shipped; for a COUNTING conflict it does
                 not, and 3.0.2 refuses the nogood.

                 A factless conflict is exactly the shape [Store.apply]'s [Failed] arm
                 produces -- the pigeonhole, realised as a pruning that empties a domain,
                 which lib/core/prop/alldiff.ml's [pass] and [regin_pass] both use
                 BECAUSE a `rup` over its facts would be a counting argument claimed as
                 reverse unit propagation. So the derivation is the statement, and it is
                 emitted here: under a decision it does not close to [0 >= 1] (the bounds
                 a decision set are not cancelled, by D-0037), and what it derives instead
                 is "not all of these bounds hold" -- which is a row, derived rather than
                 asserted, that the nogood's [rup] can propagate against.

                 Found by the M4-T2 random sweep, on a branch whose Regin conflict left
                 the nogood with nothing to propagate along. *)
              match Explanation.force c.Store.c_why with
              | Explanation.Combine _ | Explanation.Cut _ ->
                  ignore (Justify.emit ctx c.Store.c_why : Writer.cid)
              | _ ->
                  (* A conflict whose derivation IS a clause already states itself in the
                     currency the nogood propagates in -- [int_ne] with every variable
                     fixed is the case, and its nogood has always been RUP without help.
                     Emitting it here would put a redundant line on the page and, worse,
                     would state that clause in the claim index, which changes what a
                     LATER [Explanation.Clause] resolves to and so changes proofs that
                     have nothing to do with this. Measured: it made one int_lin_ne
                     nogood standalone-RUP, which test_matrix.ml's own check is there to
                     forbid. What needs stating is a conflict whose derivation is
                     ARITHMETIC, and that is what this arm selects. *)
                  ()));
          (* M1-T55: and then the bridge for any decision on this path that settled past
             a hole, which is the step the nogood's own [rup] needs and has until now
             been left to find for itself. It goes after the trace (D-0021) and before
             the nogood, at the nogood's own level, so the same [w] retires both. *)
          bridges ctx trace stats store decisions;
          let keep = learn_at_conflict engine store ctx trace stats cfg c in
          let all = levelled_nogood decisions ~top:(Store.level store) in
          let ng =
            match keep with
            | None -> minimise stats cfg.policy all
            | Some ls ->
                minimise stats cfg.policy (List.filter (fun (_, l) -> List.mem l ls) all)
          in
          let cid = emit_nogood ctx ng in
          NFail (ng, cid))
  | Engine.Fixpoint -> (
      let cands = unfixed store in
      if Array.length cands > 0 then
        branch engine store ctx trace stats cfg order decisions (order store cands)
      else
        let asn = extract_assignment store in
        match cfg.bnb with
        | None -> NSat asn
        | Some b -> (
            (* M5-T1. The solution is logged and the bound installed; then THE SAME NODE
               IS RE-ENTERED. [apply_globals] runs first at every node, the bound it now
               carries excludes the value the objective variable is fixed at, and the
               conflict that produces goes down the ordinary conflict path above -- trace,
               bridges, learning, nogood, backjump -- with nothing in it aware that the
               node it is refuting was a solution a moment ago.

               This is a re-entry, NOT a restart. docs/SPEC.md 3.4 fixes the search as
               depth-first with restarts disabled, and nothing here reopens a closed
               level, re-takes a decision or returns to the root: the decision stack is
               exactly as it was, the node is the one we are standing on, and the tree is
               still traversed once, left to right. [stats.nodes] is deliberately NOT
               incremented, because no node was dispatched -- M1-T36's identity counts
               [branch]'s children and this is not one.

               It terminates: the bound is strictly tighter than the incumbent, so the
               re-entry conflicts rather than reaching [Fixpoint] again, and no second
               solution can be found at the same node. *)
            match record_improving ctx store stats b asn with
            | `Proved -> NSat asn
            | `Continue -> dfs engine store ctx trace stats cfg order decisions))

(* Close out a level whose subtree is finished, leaving [ng] (filed below [lvl], so the
   wipe cannot touch it) as this frame's answer. D-0018 point 4's two lines, in the order
   gcs/solve.cc:296-297 has them: step the writer down, then wipe. *)
and close_level ctx ~lvl ~nogood =
  Writer.set_level ctx.Justify.writer (lvl - 1);
  wipe_after_nogood ctx ~lvl ~nogood

and branch engine store ctx trace stats cfg order decisions (dec : decision) : node =
  let v = dec.d_var in
  let d = Store.get store v in
  let k = dec.d_split in
  if k < Domain.lo d || k >= Domain.hi d then
    invalid_arg
      (Printf.sprintf
         "Search.branch: the order split %s at %d, outside [%d, %d) -- a decision must \
          strictly narrow both branches"
         (Store.name store v) k (Domain.lo d) (Domain.hi d));
  let name = Store.name store v in
  let lit = Lit.ge name (k + 1) in
  (* The two sides, in the order this decision asks for. They are the same two functions
     whichever way round they go: which side is explored first changes the tree, and
     changes nothing about what is emitted for either side. *)
  let first, second =
    if dec.d_high_first then (explore_ge, explore_le) else (explore_le, explore_ge)
  in
  (* M1-T36. One decision taken, and this decision sits one deeper than the ancestors
     it was handed. *)
  stats.decisions <- stats.decisions + 1;
  let depth = List.length decisions + 1 in
  if depth > stats.max_depth then stats.max_depth <- depth;
  Store.new_level store;
  let lvl = Store.level store in
  Writer.set_level ctx.Justify.writer lvl;
  stats.nodes <- stats.nodes + 1;
  let r1 = first store engine ctx trace stats cfg order decisions v k lit in
  Store.backtrack store;
  match r1 with
  | NSat asn ->
      Justify.wipe_level ctx lvl;
      NSat asn
  | NFail (ng1, cid1) when not (mentions_level ng1 lvl) ->
      (* THE BACKJUMP (M2-L3). Every literal of [ng1] is false under the decisions ABOVE
         this one, so [ng1] refutes the sibling branch as well -- it differs from this one
         only in the decision at [lvl], which [ng1] does not name. The sibling is not
         explored and [ng1] is this frame's answer unchanged.

         It is already filed below [lvl] ([filed_at]), so the wipe below retires this
         level's trace lines and leaves it standing. That is the half of D-0045's addendum
         this row had to get right, and getting it wrong is not a wrong answer -- it is
         "Trying to access constraint with ID n that has already been deleted" several
         lines later. *)
      stats.skipped <- stats.skipped + 1;
      close_level ctx ~lvl ~nogood:cid1;
      NFail (ng1, cid1)
  | NFail (ng1, _cid1) -> (
      Store.new_level store;
      let lvl2 = Store.level store in
      Debug.check "search: reopened level matches the one just closed" (fun () ->
          lvl2 = lvl);
      Writer.set_level ctx.Justify.writer lvl;
      stats.nodes <- stats.nodes + 1;
      let r2 = second store engine ctx trace stats cfg order decisions v k lit in
      Store.backtrack store;
      match r2 with
      | NSat asn ->
          Justify.wipe_level ctx lvl;
          NSat asn
      | NFail (ng2, cid2) when not (mentions_level ng2 lvl) ->
          (* The mirror of the arm above, on the second child: [ng2] alone already
             refutes this level, so there is nothing to resolve it against. *)
          close_level ctx ~lvl ~nogood:cid2;
          NFail (ng2, cid2)
      | NFail (ng2, cid2) ->
          Debug.check
            "search: each child's nogood names its own decision level before they resolve"
            (fun () -> mentions_level ng1 lvl && mentions_level ng2 lvl);
          ignore cid2;
          let combined = combine_nogoods stats cfg.policy ng1 ng2 ~lvl in
          Writer.set_level ctx.Justify.writer (lvl - 1);
          let cid = emit_nogood ctx combined in
          wipe_after_nogood ctx ~lvl ~nogood:cid;
          NFail (combined, cid))

(* The decision push itself. It is the first entry of the level just opened, which is
   what [Trace] relies on to tell a decision (no line -- nothing implies it) from a
   pruning (a line). [Store] asserts the same thing from its side via
   [is_level_start]; this check is the search's half, because the only way the two can
   disagree is a push here that did not actually change the domain. *)
and check_decision_landed store lvl outcome =
  Debug.check "D-0018: a decision is the first trail entry of its own level" (fun () ->
      (match (outcome : Store.outcome) with
      | Store.Changed -> true
      | Store.Unchanged | Store.Conflict _ -> false)
      && Store.level store = lvl
      && Store.is_level_start store (Store.trail_length store - 1))

(* The low side, [x <= k] -- the decision literal is [~lit]. With [k = lo] (docs/SPEC.md
   3.4's indomain_min) this fixes [x = lo], which is what it has always done.

   M1-T31/M1-T50: the reason pushed with it is [Explanation.decision ~lit] and not the
   old [Explanation.trivial]. A decision is an assumption, not an instance of the model
   constraint, and calling it [Trivial] was what let a propagator citing this entry
   render it as the ambient model row (see explanation.ml's header).

   M2-T8/D-0026: the push carries [Reason.none] beside that explanation, and it says so out
   loud rather than getting it by default. M2-L0/D-0043: and [~concludes:None] beside it,
   because the bound is ASSUMED, not derived. *)
and explore_le store engine ctx trace stats cfg order decisions v k lit =
  let lvl = Store.level store in
  let outcome =
    Store.set_hi store v k
      (Reason.because ~concludes:None Reason.none (Explanation.decision (Lit.negate lit)))
  in
  match outcome with
  | Store.Conflict _ ->
      (* [k >= lo] and [lo] is in [v]'s domain (I-D2), so [set_hi _ k] cannot empty it;
         kept only so this function is total against [Store.outcome] without assuming
         it. Nothing is learned here: the push never landed, so there is no trail entry
         to walk back from and [Analysis] would have nothing to resolve. *)
      Trace.emit ctx trace store;
      (* M1-T55: the ancestors only -- this push did not land, so it has no trail entry
         and nothing to bridge, and [bridges] drops it for exactly that reason. *)
      bridges ctx trace stats store decisions;
      let ng =
        minimise stats cfg.policy (levelled_nogood (Lit.negate lit :: decisions) ~top:lvl)
      in
      let cid = emit_nogood ctx ng in
      NFail (ng, cid)
  | Store.Changed | Store.Unchanged ->
      check_decision_landed store lvl outcome;
      dfs engine store ctx trace stats cfg order (Lit.negate lit :: decisions)

(* The high side, [x >= k + 1] -- the decision literal is [lit]. Symmetrically,
   [k + 1 <= hi] and [hi] is in the domain, so this push cannot empty it either. *)
and explore_ge store engine ctx trace stats cfg order decisions v k lit =
  let lvl = Store.level store in
  let outcome =
    Store.set_lo store v (k + 1)
      (Reason.because ~concludes:None Reason.none (Explanation.decision lit))
  in
  match outcome with
  | Store.Conflict _ ->
      Trace.emit ctx trace store;
      (* M1-T55: as in [explore_le] -- the ancestors only. *)
      bridges ctx trace stats store decisions;
      let ng = minimise stats cfg.policy (levelled_nogood (lit :: decisions) ~top:lvl) in
      let cid = emit_nogood ctx ng in
      NFail (ng, cid)
  | Store.Changed | Store.Unchanged ->
      check_decision_landed store lvl outcome;
      dfs engine store ctx trace stats cfg order (lit :: decisions)

(* ------------------------------------------------------------------------------ API *)

(* The tree walk itself, shared by [solve] and [optimise] (M5-T1).

   It stops where the two part company: it runs the search, checks the invariants and
   reports the oracle, and hands back the root node together with the [trace] and [stats]
   it may have had to create. It writes NO conclusion and retires NOTHING -- which of the
   live ids the conclusion is allowed to keep is exactly what differs between a
   satisfaction answer and a bounds answer, so it belongs to the caller that writes the
   conclusion. It takes no [check] for the same reason: a satisfaction search checks one
   solution at the end, a branch-and-bound search checks every improving one as it is
   found ([record_improving]), and neither is this function's business. *)
let search_core ~(engine : Engine.t) ~(store : Store.t) ~(ctx : Justify.ctx) ?trace ?stats
    ?(order = spec_order) ?(config = default_config) () : node * Trace.t * stats =
  let entry_level = Store.level store in
  (* [?trace] exists so a caller can read back *which* rules in the emitted proof were
     D-0018 trace lines (test/unit/test_trace.ml checks each of them standalone against
     the .opb -- the one check that distinguishes a real trace from a decorative one).
     It is state this function would otherwise own privately; passing one in changes
     nothing about what is emitted. *)
  let trace = match trace with Some t -> t | None -> Trace.create () in
  (* M1-T36. [?stats] is read back the same way [?trace] is: state this function would
     otherwise own privately, passed in so a caller can see it. Passing one changes no
     byte of what is emitted -- the counters are read by nothing inside the search. The
     root is counted HERE and nowhere else: [branch] counts the children it dispatches,
     so the one node no [branch] dispatches is this one. *)
  let stats = match stats with Some s -> s | None -> stats_create () in
  (* M2-L4: one database per solve, built from the configured policy. Installed here and
     not in [stats_create] because the policy lives on [config] and a [stats] is allowed
     to outlive a [solve]. *)
  stats.db <- Retention.create ~policy:config.retention ();
  (* M2-L12: and the learned units, for the same reason -- a [stats] may outlive a
     [solve], and a global from a previous search cites a constraint this one's writer
     knows nothing about.

     THE ENGINE IS NOT RESET AND CANNOT BE, and that is a stated limit rather than an
     oversight. Step 2 registers a learned clause with [Engine.add], which appends; there
     is no [Engine.remove], and adding one would mean rebuilding the watcher table that
     [Engine.check_attribution]'s second arm reads. So **a second [solve] on an engine a
     first [solve] has learned on is not supported**: the instances from the first search
     would still be there, propagating, and their `rup` lines would rest on constraints
     the first search's end-of-sweep already retired -- which the checker would find, a
     long way from here.

     Nothing does it. [Compile.compile] builds one engine per model and every caller in
     lib/, bin/ and test/ solves once on it; the whole suite is green with the audit on,
     which is what says so rather than this comment. If a caller ever needs to re-solve,
     it compiles again -- or [Engine] grows a truncate-to-a-mark and this comment becomes
     that function's reason for existing. *)
  stats.globals_rev <- [];
  (* M2-L13: the id boundary [count_learned_activity] tests against. Recorded here rather
     than in [stats_create] for the same reason the database is: a [stats] may outlive a
     [solve], and the engine it is about to be pointed at is not the one it last saw. *)
  stats.first_learned_id <- Engine.next_id engine;
  stats.pb_inst_ids_rev <- [];
  stats.clause_inst_ids_rev <- [];
  stats.nodes <- stats.nodes + 1;
  let result = dfs engine store ctx trace stats config order [] in
  Debug.check "I-S3: decision level on return equals level on entry" (fun () ->
      Store.level store = entry_level);
  (* M1-T36's identity, stated above [type stats]. [Unsat] means the tree was
     exhausted, so the equality must hold exactly; [Sat] means it was not, so only the
     bound does. *)
  Debug.check "M1-T36: nodes = 2 * decisions + 1 on an exhausted tree, <= it otherwise"
    (fun () ->
      stats_consistent stats
        ~exhausted:(match result with NFail _ -> true | NSat _ -> false));
  (* I-X2: the trace lines for prunings made at level 0 are the one class of rule this
     search emits that no [w] retires -- they are deliberately outside every branch's
     level, because a level-0 pruning outlives every branch and the checker needs it on
     both sides of a backtrack (see [Trace]'s header). Retire them here, once, on every
     path, before the conclusion. Doing it here rather than inside [Trace] keeps the
     rule "an id you receive is an id you delete" with the caller that owns the proof's
     shape. *)
  (* M2-T10: the search-side half of the consistency oracle -- its TRACE.

     [Engine.propagate] does the checking, at every fixpoint, which is every node of this
     search. What it cannot do is say how much of the tree that came to, because the
     engine does not know it is inside a search. This does, so it says so once per
     [solve], on stderr, behind the same gate.

     It matters that this line exists and is read. The whole failure mode of a brute-force
     audit is a silent skip: a scope too wide for [Debug.consistency_cap] is passed over,
     and a run that checked nothing looks exactly like a run that checked everything and
     found nothing. So the line reports SKIPS next to checks, and a reader who sees
     skipped>0 knows the verdict is partial. Nothing here fails on a skip -- a skip is a
     budget, not a bug -- but it is not allowed to be invisible.

     stderr and not the proof, not stdout: a model test compares stdout against
     test/expected/, and an audit that changed the answer would be an audit that could
     not be run over the suite it is meant to audit.

     And behind BAGUETTE_CONSISTENCY_TRACE rather than BAGUETTE_CONSISTENCY, because
     M1-T49 forbids stderr without --time and run_model_tests.sh enforces it per model:
     printing this whenever the oracle was on failed all 57 models for printing it. The
     oracle checks silently; this says how much it checked. See lib/core/debug.ml. *)
  if Debug.consistency_enabled && Debug.consistency_trace then (
    let nodes, checks, tuples, skipped = Engine.oracle_stats () in
    Printf.eprintf
      "M2-T10 consistency oracle: %d fixpoints audited, %d instance-checks, %d oracle \
       tuples, %d instance-checks SKIPPED over the %d-tuple cap%s\n\
       %!"
      nodes checks tuples skipped Debug.consistency_cap
      (if skipped > 0 then
         " -- a SKIP IS NOT A PASS: raise BAGUETTE_CONSISTENCY_CAP to cover them"
       else "");
    (* And the breakdown, because the totals cannot distinguish "every declared level was
       met" from "nothing carrying an obligation was ever reached". A run whose CHECKED
       list is empty has audited nothing however many fixpoints it visited, and the second
       list is what says which families that was and at which level -- [Value] and
       [Checking] owe no support, deliberately (see [Engine.check_consistency]'s header),
       so they belong on a line of their own and not in a failure. *)
    let show label rows =
      if rows = [] then Printf.eprintf "M2-T10   %s: (none)\n%!" label
      else
        Printf.eprintf "M2-T10   %s: %s\n%!" label
          (String.concat ", " (List.map (fun (n, c) -> Printf.sprintf "%s x%d" n c) rows))
    in
    show "CHECKED" (Engine.oracle_checked_families ());
    show "no obligation at its level" (Engine.oracle_unobliged_families ()));
  (result, trace, stats)

(* The two I-X2 sweeps, lifted out of [solve] when [optimise] came to need the same two.
   Their arguments are what they always closed over; the comments that were on them are
   below, unchanged in substance. *)

(* I-X2: the trace lines for prunings made at level 0 are the one class of rule this
   search emits that no [w] retires -- they are deliberately outside every branch's
   level, because a level-0 pruning outlives every branch and the checker needs it on
   both sides of a backtrack (see [Trace]'s header). Retire them once, on every path,
   before the conclusion. Doing it here rather than inside [Trace] keeps the rule "an id
   you receive is an id you delete" with the caller that owns the proof's shape. *)
let retire_trace ctx trace =
  match Trace.permanent_ids trace with
  | [] -> ()
  | ids -> Writer.delete_many ctx.Justify.writer ids

(* I-X2, and M2-L4 is what changed here. A learned constraint is introduced at level 0
   (D-0045's addendum, [Learned.introduce]) precisely so that no backjump retires it,
   which leaves exactly one party who can. Since M2-L4 that party is [stats.db] and not
   this function: the sweep deletes what the database still HOLDS, so a constraint the
   policy already evicted mid-search is not deleted a second time here.

   Reading it off [stats_learned] -- every id ever introduced -- is the double delete,
   and it is a double delete from ONE owner, which is the shape D-0045's warning about
   two owners does not cover. lib/core/retention.ml section 1 is the record.

   Note what is still NOT done: they are not retired at the backjump. A learned clause
   whose lifetime were a level's would be a learned clause that learned nothing.

   M2-L12: the citations are released first. They are a statement about the SEARCH -- a
   global or a registered instance will write a [rup] resting on this constraint at the
   next node -- and there is no next node. [Retention.release_all] says this at length;
   the double-delete and not-owned guards stay on. *)
let retire_learned ctx stats =
  Retention.release_all stats.db;
  ignore (Retention.retire_all stats.db ctx)

(* Depth-first search from the store's current decision level (I-S3: the level on
   return equals the level on entry -- true here by construction, since every
   [Store.new_level] this module calls is paired with exactly one [Store.backtrack]
   before returning).

   [?order] is the branching order and defaults to [spec_order], docs/SPEC.md 3.4's
   normative first-fail/indomain_min: nothing outside the tests passes it, and the
   default is byte-for-byte the tree this module has always built. [random_order] is
   the fuzzer's (M2-T11); see the branching-order section above for what an order is
   allowed to vary.

   [engine] is shared, reusable state (its watcher table does not depend on the
   store's contents); [store] and [ctx] carry the search's actual state. [check] is
   the independent re-verification invariant I-S1 requires -- "every solution printed
   satisfies every constraint, re-checked independently ... not by trusting the
   propagators". There is deliberately no way to skip it: a caller without a real
   model-level checker at hand (M1-T10 lands before the FlatZinc [Model.t] is wired to
   the solver) still has to pass one, even if it is a small hand-written one, as the
   tests below do.

   On [Sat], the proof's [conclusion] cites the found assignment directly (never a
   bare [sol], which the doc notes only works when deletion-checking was never turned
   off -- the assignment form always works). On [Unsat], it cites the id of the
   final, decision-free nogood. Both leave [Writer]'s audit-mode live set exactly as
   it was before the call plus that one id, which [Writer.conclusion] itself retires
   (invariant I-X2 -- see docs/PROOF-FORMAT.md section 5, "discharged by the
   conclusion"). *)
let solve ~(engine : Engine.t) ~(store : Store.t) ~(ctx : Justify.ctx)
    ~(check : assignment -> bool) ?trace ?stats ?(order = spec_order)
    ?(config = default_config) () : outcome =
  let result, trace, stats =
    search_core ~engine ~store ~ctx ?trace ?stats ~order ~config ()
  in
  match result with
  | NSat assignment ->
      if not (check assignment) then raise (Unsound_solution assignment);
      retire_learned ctx stats;
      retire_trace ctx trace;
      (* I-X2, and the SAT path needs it for the same reason the NFail arm below does
         (M4-T4b found this; the arithmetic family is simply the first thing in the tree
         to nest this deeply at level 0 on a SAT path). A level-0 pruning whose D-0013
         explanation NESTS -- a [Combine] citing a trail entry whose own explanation is a
         [Combine] -- mints intermediate [pol] ids at level 0, and no [w] retires a
         level-0 id. The audit then refuses the run with "constraint id(s) never
         deleted". Unlike the refutation arm there is no cited contradiction to spare:
         the conclusion is [Sat lits], which cites no constraint, so every live id goes. *)
      (match Writer.live_ids ctx.Justify.writer with
      | [] -> ()
      | ids -> Writer.delete_many ctx.Justify.writer ids);
      let bindings = List.map (fun (v, x) -> (Store.name store v, x)) assignment in
      let lits = Encoding.assignment_lits ctx.Justify.encoding bindings in
      Writer.conclusion ctx.Justify.writer (Writer.Sat lits);
      Sat assignment
  | NFail (lits, cid) ->
      (match lits with
      | [] -> ()
      | _ ->
          invalid_arg
            "Search.solve: the root nogood must be decision-free -- solve must be called \
             with no ambient decisions active");
      retire_learned ctx stats;
      (* I-X2: the live set must be empty at [conclusion], and the contradiction cited
         by the conclusion is the one id that counts as discharged by it
         (docs/PROOF-FORMAT.md section 5). A root refutation's derivation leaves its
         intermediate steps behind -- they are at level 0, so no [w] retires them --
         so retire them explicitly here. Nothing references them again: the proof ends
         on the next line. *)
      retire_trace ctx trace;
      let leftovers =
        List.filter (fun id -> id <> cid) (Writer.live_ids ctx.Justify.writer)
      in
      if leftovers <> [] then Writer.delete_many ctx.Justify.writer leftovers;
      Writer.conclusion ctx.Justify.writer (Writer.Unsat (Some cid));
      Unsat

(* ------------------------------------------------------------------ M5-T1/M5-T2 *)

(* What an optimisation run answers. The value is in MODEL units -- the objective
   variable's own value, which is what SPEC 2.2's output prints -- and never the
   checker's negated units, which exist only inside [optimise]. *)
type opt_outcome =
  | Opt of assignment * int (* proved optimal: the incumbent and its objective value *)
  | Opt_unsat (* the model has no solution at all *)

(* Branch and bound, and the `conclusion BOUNDS` that proves the answer optimal
   (M5-T1 + M5-T2). Read [type bnb] first: the proof argument is there.

   The relation to [solve] is that there is almost none -- the tree, the propagation, the
   learning, the backjumping and every rule they emit are identical, and the whole of the
   difference is [config.bnb], which turns the solution node from a stopping point into a
   conflict. What is different HERE is only the conclusion, and it is different in one
   way that matters: which live id survives the I-X2 sweep.

   THE SWEEP, AND WHAT THE CONCLUSION IS ALLOWED TO KEEP. Every `soli` hands back an id
   and every one of them is this function's to delete (ARCHITECTURE section 6, I-X2), so
   they are swept here with everything else. Exactly one id is spared, and
   docs/PROOF-FORMAT.md section 5 is the rule: "A contradiction consumed by
   `conclusion UNSAT : <cid>`, and the lower-bound id in `BOUNDS`, count as discharged by
   the conclusion, since they cannot be deleted before being referenced." That is asserted
   rather than assumed -- [Writer.conclusion] forgets the id it cites, and the audit runs
   at the end of it with the live set expected empty.

   THE UPPER BOUND CARRIES NO ASSIGNMENT, deliberately. `conclusion BOUNDS <lo> : <id>
   <hi> : <assignment>` is legal and 3.0.2 accepts it, but it is the same trap M1-T18
   found on `conclusion SAT : <assignment>`: the assignment we hold is over the MODEL
   variables, the .opb also carries encoding auxiliaries that nothing in the solver knows
   a value for, and an inline assignment is not propagated -- every unmentioned variable
   reads as false and an honest proof is REJECTED. A solution logged with `soli` IS
   propagated, and [record_improving] has already logged this one, so the number alone is
   both sufficient and safe. *)
let optimise ~(engine : Engine.t) ~(store : Store.t) ~(ctx : Justify.ctx)
    ~(check : assignment -> bool) ~(objective : objective)
    ~(on_solution : assignment -> unit) ?trace ?stats ?(order = spec_order)
    ?(config = default_config) () : opt_outcome =
  let b =
    {
      b_obj = objective;
      b_check = check;
      b_on_solution = on_solution;
      b_best = None;
      b_soli_ids = [];
      b_floor = None;
    }
  in
  let result, trace, stats =
    search_core ~engine ~store ~ctx ?trace ?stats ~order
      ~config:{ config with bnb = Some b } ()
  in
  retire_learned ctx stats;
  retire_trace ctx trace;
  let sweep_all_but keep =
    match
      List.filter (fun id -> Some id <> keep) (Writer.live_ids ctx.Justify.writer)
    with
    | [] -> ()
    | ids -> Writer.delete_many ctx.Justify.writer ids
  in
  (* The root's answer, and the two shapes it can take. A nogood that still names a
     decision cannot reach here -- [solve] refuses the same thing for the same reason --
     and an [NSat] that did not come from the floor case would mean [dfs] stopped at a
     solution while optimising, which is the one thing [config.bnb] exists to prevent. *)
  let root_contradiction =
    match result with
    | NFail ([], cid) -> Some cid
    | NFail (_ :: _, _) ->
        invalid_arg
          "Search.optimise: the root nogood must be decision-free -- optimise must be \
           called with no ambient decisions active"
    | NSat _ -> None
  in
  match (b.b_best, root_contradiction) with
  | None, Some cid ->
      (* No solution at all. `conclusion UNSAT` is NOT available here and the reason is
         not a matter of taste: 3.0.2 refuses it over a formula carrying a `min:` line --
         "'conclusion UNSAT' can only be used without an objective. Use 'conclusion
         BOUNDS INF INF' for infeasible optimization problems." -- and an optimisation
         model always carries one. So both bounds are INF, which is the honest reading
         anyway: the minimum over an empty set of solutions is +INF from either side. The
         contradiction is still cited, so I-X2 discharges exactly as it does on [solve]'s
         refutation arm. *)
      sweep_all_but (Some cid);
      Writer.conclusion ctx.Justify.writer
        (Writer.Bounds
           { lower = None; lower_id = Some cid; upper = None; upper_assignment = [] });
      Opt_unsat
  | None, None ->
      invalid_arg
        "Search.optimise: the search returned a solution but recorded no incumbent -- \
         record_improving did not run"
  | Some (asn, value), _ ->
      let lower_id =
        match (root_contradiction, b.b_floor) with
        | Some cid, _ ->
            (* Case (1) of [type bnb]: the tree was exhausted under the last improving
               constraint, so nothing better than the incumbent exists and the root
               contradiction says so. A contradiction syntactically implies every bound,
               which is what `conclusion BOUNDS <lo> : <cid>` needs of it. *)
            Some cid
        | None, (Some _ as floor) ->
            (* Case (2): the incumbent sits on the objective's declared floor, the
               improving constraint is itself unsatisfiable, and it is what implies the
               bound. No search was needed and none was done. *)
            floor
        | None, None ->
            invalid_arg
              "Search.optimise: an incumbent with neither a root contradiction nor a \
               floor constraint to establish its lower bound"
      in
      (* The checker minimises (docs: "An objective is minimised; FlatZinc maximisation
         is negated by the caller"), so a maximisation's objective value on the page is
         the negation of the model's. This is the single place that conversion happens
         and the only place [Maximise] is read outside [record_improving]. *)
      let page_value =
        match objective.o_dir with Minimise -> value | Maximise -> -value
      in
      sweep_all_but lower_id;
      Writer.conclusion ctx.Justify.writer
        (Writer.Bounds
           {
             lower = Some page_value;
             lower_id;
             upper = Some page_value;
             upper_assignment = [];
           });
      Opt (asn, value)
