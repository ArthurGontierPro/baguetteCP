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
     * there is no marker at all without --proof, and the two formats spell it
       differently (`# l` under 2.0, `% level l` under 3.0), so the proxy also depends
       on which checker the run was aimed at.

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
      (* I-X2: every id [Learn.introduce] handed back, newest first. They are at level 0,
         so no [w] retires them and [solve] must, on every path. *)
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
      (* ...of which [Learned.to_linear_row] accepts, i.e. which could be a runtime
         instance. Measured against the clause path's [n_converts], which is the
         comparison lib/core/pb_analysis.ml's "why the PB row can propagate where the
         clause cannot" makes and does not assume. *)
  mutable n_pb_stronger : int;
      (* ...of which convert where the SAME conflict's clause does not. This is test (a)
         as a counter: the number of times this row did something M2-L3 could not. *)
  mutable pb_rows_rev : Pb_analysis.t list;
      (* The PB rows learned, newest first, capped. Kept so a test can run the ORACLE on
         what a real solve actually derived -- test (e) -- instead of on a scene built to
         make the oracle pass. Capped for the reason [bridges_rev] is. *)
  mutable pb_fallback_rev : string list;
      (* Why, newest first, capped. A rate with no breakdown behind it cannot be acted
         on, and the breakdown is what says whether the traffic is [No_row] (expected,
         D-0044) or [Not_conflicting] (a finding about the reduction). *)
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
    n_converts = 0;
    learned_rev = [];
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
    pb_rows_rev = [];
    pb_fallback_rev = [];
  }

let stats_learned s = List.rev s.learned_rev

(* ------------------------------------------------------------------ M2-L6 counters *)

(* The same cap and the same reason as [bridge_cap]: keeping every reason of a long
   search would be a leak in a process that shares 15 GB, and no caller needs more than
   the first few. The RATE is computed from [n_pb_fallback], which is uncapped. *)
let pb_reason_cap = 64
let stats_pb_fallbacks s = List.rev s.pb_fallback_rev
let stats_pb_rows s = List.rev s.pb_rows_rev

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

(* docs/SPEC.md 3.4, and the default of [solve]: first-fail, min-value branching. This is
   the normative strategy and the only one the CLI can reach; `lib/flatzinc/compile.ml`
   rejects an annotation asking for anything else rather than silently ignoring it. *)
let spec_order store cands =
  let v = first_fail store cands in
  { d_var = v; d_split = Domain.lo (Store.get store v); d_high_first = false }

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
                from the decision closure and not from either learned object -- and M2-L3
                owns a body of assertions about it that this row has no business
                disturbing. What the PB row adds is a strictly stronger constraint on the
                page, under D-0044's same fork (ii): proof-only until M2-L4's retention
                policy decides which learned objects earn a runtime instance. Off is the
                state every M2-L3 measurement was taken in, so a comparison against those
                numbers has a switch to set.
   [reduction]  which [Reduce.t] brings the pivot's coefficient to 1. [round_to_one]
                dominates [division] (D-0044), and [division] is here so a test can show
                the difference on a real conflict rather than on a hand-built row.
   [pb_criterion] the slack-based stopping rule. See lib/core/pb_analysis.ml on why an
                assertive constraint is not a sufficient stop condition for PB. *)
type config = {
  learn : bool;
  policy : Learn.policy;
  break_i_s4 : bool;
  pb : bool;
  reduction : Reduce.t;
  pb_criterion : Pb_analysis.criterion;
}

let default_config =
  {
    learn = true;
    policy = Learn.Strongest;
    break_i_s4 = false;
    pb = true;
    reduction = Reduce.round_to_one;
    pb_criterion = Pb_analysis.assertive_slack;
  }

let no_learning = { default_config with learn = false; pb = false }
let no_pb = { default_config with pb = false }

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

   M1-T46: the two checkers word that rejection differently and **share no substring**,
   so match on neither alone. 2.2.2 says "Constraint is not a contradiction"; 3.0.2 --
   the checker of record, and the format emitted by default since D-0025 -- says "The
   constraint with ID <n> is not contradicting, as specified by the hint". Measured
   against both binaries, not guessed. lib/core/prop/ne.ml's header and
   test/unit/test_random.ml carry the same pair, and that test matches both deliberately:
   matching only the 2.0 wording is not a vacuous pass but it is a vacuous *diagnosis*,
   reporting a known bug as a brand-new one.

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
let rec rests_on_a_clause (e : Explanation.t) =
  match Explanation.force e with
  | Explanation.Clause _ -> true
  | Explanation.Decision _ | Explanation.Model_row _ | Explanation.Linear _ -> false
  | Explanation.Cut (a, b, _, _) -> rests_on_a_clause a || rests_on_a_clause b
  | Explanation.Combine (summands, _) ->
      List.exists
        (function
          | Explanation.Term (_, e) -> rests_on_a_clause e | Explanation.Weaken _ -> false)
        summands
  | Explanation.Deferred _ -> false (* [force] returns a non-deferred head *)

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
let pb_at_conflict engine store ctx stats cfg (c : Store.conflict) ~clause_converts ~decl
    =
  if not (cfg.learn && cfg.pb) then ()
  else (
    stats.n_pb_attempts <- stats.n_pb_attempts + 1;
    match
      Pb_analysis.analyse store c ~row_of:(Engine.row_of engine store)
        ~name_of:(Engine.name_of engine) ~reduction:cfg.reduction
        ~criterion:cfg.pb_criterion
    with
    | Pb_analysis.Fallback f ->
        stats.n_pb_fallback <- stats.n_pb_fallback + 1;
        if List.length stats.pb_fallback_rev < pb_reason_cap then
          stats.pb_fallback_rev <-
            Pb_analysis.fallback_to_string f :: stats.pb_fallback_rev
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
        if List.length stats.pb_rows_rev < pb_reason_cap then
          stats.pb_rows_rev <- t :: stats.pb_rows_rev;
        stats.learned_rev <- cid :: stats.learned_rev)

let rec learn_at_conflict engine store ctx trace stats cfg (c : Store.conflict) =
  if not cfg.learn then None
  else
    match
      Learn.at_conflict ~policy:cfg.policy store c ~vars_of:(Engine.vars_of engine)
        ~decl:(Learned.decl_of_encoding ctx.Justify.encoding)
    with
    | None -> None
    | Some l ->
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
        stats.learned_rev <- cid :: stats.learned_rev;
        pb_at_conflict engine store ctx stats cfg c ~clause_converts
          ~decl:(Learned.decl_of_encoding ctx.Justify.encoding);
        Some (Learn.levels l)

and dfs engine store ctx trace stats cfg (order : order) (decisions : Lit.t list) : node =
  match Engine.propagate engine store with
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
            if rests_on_a_clause e then close_root_conflict ctx trace store c
            else Justify.emit ctx e
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
          let _ : Writer.cid option = Trace.conflict_line ctx trace c in
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
  | Engine.Fixpoint ->
      let cands = unfixed store in
      if Array.length cands = 0 then NSat (extract_assignment store)
      else branch engine store ctx trace stats cfg order decisions (order store cands)

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
         lines later, or its 2.0 wording, which shares no substring with it (M1-T46). *)
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
  let retire_trace () =
    match Trace.permanent_ids trace with
    | [] -> ()
    | ids -> Writer.delete_many ctx.Justify.writer ids
  in
  (* I-X2, M2-L3's own half. A learned clause is introduced at level 0 (D-0045's addendum,
     [Learned.introduce]) precisely so that no backjump retires it, which leaves exactly
     one party who can: whoever asked for it. Until M2-L4's retention policy exists that
     is this function, on every path, once each -- [Learn.introduce] goes through
     [Writer.rup] and not through the memo, so no two conflicts share an id and this list
     has no repeats to delete twice.

     Note what is NOT done here: they are not retired at the backjump. A learned clause
     whose lifetime were a level's would be a learned clause that learned nothing, and the
     whole of D-0045's addendum is about it outliving the level it was derived at. *)
  let retire_learned () =
    match stats_learned stats with
    | [] -> ()
    | ids -> Writer.delete_many ctx.Justify.writer ids
  in
  match result with
  | NSat assignment ->
      if not (check assignment) then raise (Unsound_solution assignment);
      retire_learned ();
      retire_trace ();
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
      retire_learned ();
      (* I-X2: the live set must be empty at [conclusion], and the contradiction cited
         by the conclusion is the one id that counts as discharged by it
         (docs/PROOF-FORMAT.md section 5). A root refutation's derivation leaves its
         intermediate steps behind -- they are at level 0, so no [w] retires them --
         so retire them explicitly here. Nothing references them again: the proof ends
         on the next line. *)
      retire_trace ();
      let leftovers =
        List.filter (fun id -> id <> cid) (Writer.live_ids ctx.Justify.writer)
      in
      if leftovers <> [] then Writer.delete_many ctx.Justify.writer leftovers;
      Writer.conclusion ctx.Justify.writer (Writer.Unsat (Some cid));
      Unsat
