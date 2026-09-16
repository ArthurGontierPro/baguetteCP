# Design-choices diff: baguette vs the Glasgow Constraint Solver

Status: **report only — no code or roadmap changes made.** Produced 2026-09-16 by three
parallel read-only sweeps (engine, proof logging, propagation), plus direct verification
of the load-bearing claims by the orchestrating session.

Scale: GCS is 137k lines, 2716 commits, 47 constraint families. baguette is 6.5k lines,
7 propagator modules, 4 FlatZinc builtin families. This is a diff between a prototype and
its mature cousin; the useful output is *which structures to adopt before we write the
next twenty propagators*, not a port.

GCS lives at `/home/arthur_gla/gcs/glasgow-constraint-solver`. Its `dev_docs/` records
rationale, measurements, and abandoned experiments, and was more valuable than the C++.

---

## 1. What all three sweeps independently converged on

Three agents worked separate axes without seeing each other's findings. They agreed on
three things, which is the strongest signal in this document.

### 1.1 Split `Reason` (what) from `Justification` (how) — the top structural change

Our `Explanation.t` conflates three concerns GCS keeps apart: `Clause`/`Linear` are
*reasons*, `Combine`/`Weaken`/`Model_row` are a *justification recipe*, `Deferred` is
*timing*. Symptoms already visible in our tree:

- **Two mandatory reason channels that must not drift.** I-P4 requires an `Explanation`;
  I-P5 separately requires `~facts`. `lib/core/prop/linear.ml:367-375` derives both from
  one `row_snaps` call with a comment saying they must not drift apart — a comment doing
  a type's job. `int_ne` violated I-P5 from M1-T9 to M1-T17; under a single channel it
  could not have.
- **A trail scan on the propagator hot path.** Because an `Explanation` must cite a
  derivation, `linear.ml:161-186` scans the trail per other-term per pruning.
  GCS's identical derivation (same weaken, divide, add) is 31 lines and scans nothing,
  because the propagator names a *literal* and a shared tracker resolves it to a line.

GCS ran this experiment on itself: their old closure-valued `ReasonFunction` "looks lazy
but is not… measured at **~20% of runtime** on some benchmarks" (`dev_docs/reasons-improvement.md`).
They replaced it with declarative reason *data* materialised in exactly one place. Our
`Deferred` is genuinely lazy in the thunk, but the snapshot it closes over is built
eagerly *including the trail scan* — because I-X6 forbids reading live state. So we
arrived at GCS's pre-refactor shape via a correctness argument rather than an oversight,
and stand to hit the same cost.

It gates four of the next five roadmap items: M2-T3 (clause learning walks the trail and
wants a reason naming variables), M3-T2 (GCS's reification dispatcher is only ~224 lines
because a verdict can *carry* reason and justification as values), M4 (a Hall-interval
reason is one `Bounds_of vars` value versus a hand-built `Combine` plus a hand-built
facts list, written twice, per pruning, in the hardest propagator we will have), and M6
(GCS's `want_reasons()` has no analogue here and cannot have one, because no single place
decides whether the reason is needed).

Cost is now-or-never: 7 propagators, 5 of which are aliases or 2-var specialisations.

It does **not** remove D-0013's arithmetic — that becomes the `Justification` half. It
does not settle D-0003, but it narrows it: "what is a higher-order explanation" becomes a
question about `Justification` alone.

### 1.2 Integer overflow is unhandled, and it is the one soundness gap

`grep -rn 'overflow\|max_int\|min_int\|Int64\|Zarith' lib/ docs/SPEC.md docs/INVARIANTS.md`
returns **nothing** (verified). `linear.ml:147-149` multiplies raw OCaml ints, which wrap
silently at 63 bits.

Why this is worse here than in most solvers: a wrapped product prunes wrongly *and* the
`.opb` row is expanded from the same wrapped arithmetic, so **VeriPB accepts the proof**.
That is the exact failure mode this project's design exists to prevent. On a SAT model
I-S1's independent check catches it; on an UNSAT model nothing does.

GCS caps declared domains at ±LLONG_MAX/4 and checks every arithmetic operator. Their
rationale is worth copying verbatim: *"The boundary is measured, not chosen. At ±2^61
`LessThan`, `Plus` and `AllDifferent` all write their model; at ±2^62 all three abort
part-way through, leaving a truncated OPB (issue #852)."*

The 80% fix is small: a declared-bound cap at compile time plus checked add/mul in
`linear.ml` and `ne.ml`.

### 1.3 Domain changes carry no granularity, and propagators re-wake themselves

`Domain.result` is `Unchanged | Changed | Failed` — no event kind. `ARCHITECTURE.md:58-60`
already *promises* `NoChange | Bound of … | Holes of …` "so the engine knows which
propagators to re-queue"; the code never delivered it. Every change on a watched variable
wakes every watcher.

Separately, `linear.ml:22-29` documents that one pass reaches its fixpoint, yet
`engine.ml:97-98` re-enqueues the running propagator off its own prunings, so every
effectful run is followed by a wasted one.

Caveat from GCS's own measurements, which argues *against* over-investing here: tightening
a 2-term `int_lin_ne` to `on_instantiated` dropped 9.9M of 17.8M calls and "moved the wall
clock by nothing measurable"; the same change on a ten-term constraint was worth 6.9%.
The payoff scales with the scan the wake skips, not the call count. **Do it because it
makes the API honest and because it is the prerequisite for the rest, not because it is
fast at our scale.**

---

## 2. Verified in this session (not taken on an agent's word)

### 2.1 BUG: `del range` is half-open; we emit it as inclusive

`docs/PROOF-FORMAT.md:161` documents `del range LO HI` as "inclusive".
`Writer.wipe_level` (`lib/proof/writer.ml:418-421`) emits `del range lo hi` for the
inclusive run `[lo..hi]`.

Tested directly against veripb 3.0.2 with a hand-written proof and two controls:

| Case | Result | Meaning |
|---|---|---|
| `del id @c2` then `pol @c2` | **error**: "constraint with ID 2 … already been deleted" | citing a deleted id is a hard error, so the probe is meaningful |
| `del range @c1 @c1` then `pol @c2` | verified, **no** unchecked-deletion warning | an equal-bound range deletes *nothing* |
| `del range @c1 @c2` then `pol @c2` | **verified** | `@c2` survived the range that names it |
| `del range @c1 @c2` then `pol @c1` | **error**: ID 1 already deleted | `@c1` was deleted by that same range |

Conclusion: `del range LO HI` deletes `[LO, HI)`. **Every multi-id run we emit leaves its
last id live in the checker**, while `wipe_level` unconditionally drops it from `t.tags`
and `t.live`. That is an I-X3 violation ("proof state mirrors solver state"): we bookkeep
the constraint as retired, the checker keeps it forever.

Present in shipped output today — 7 `del range` lines across 5 of 14 models:
`chain_sat` (`@c41 @c44`), `guess_wrong_sat`, `ne_eq_unsat`, `ne_conflict_sat`, and
`offset_unsat` (×3). Runs of length 1 take the `del id` branch and are unaffected.

Not a soundness bug — it only ever leaves *more* constraints available — but it is
unbounded proof growth under search, and the documented semantics are wrong. Found only
because GCS's `proof_logger.cc` special-cases the top line for exactly this reason.

### 2.2 D-0011's blocker is genuinely dissolved — with a narrower reading than proposed

D-0015 states verbatim: "**Supersedes the ADT gaps recorded in D-0009, D-0010 and
D-0011**", and that `Model_row` is "D-0011's unresolvable `Trivial` made tractable: one
`Combine` can cite an explanation another propagator instance built against a *different*
row, in the same tree, which one mutable pointer cannot express."

So a **derivation citing several model rows is now expressible**, which is what M4-T1's
Hall-interval justification needs. A literal reading of D-0011 would forbid writing it at
all, and D-0011 is still marked DECIDED with no pointer forward.

Narrower than the sweep proposed, though: this dissolves D-0011's *stated reason*, not
necessarily its *policy*. "One instance per row" may still stand on its own grounds
(D-0011 judged a routing hazard worse than queue churn). The amendment should say the
ADT gap is closed and multi-row derivations are permitted — not automatically that
equality should be re-fused.

### 2.3 The `ne.ml` consistency-tag mismatch is deliberate, and constrains the test design

`ne.ml:10-19` declares `Value` while achieving domain consistency, and argues the case:
the level *bounds what an explanation may claim* (SPEC 3.2), so declaring weaker is
conservative in the only direction that matters. SPEC 2.2/3.2 makes the tag normative.

Consequence for the proposed per-node consistency check: it must assert **at least** the
declared level, never *exactly* it, or it fails on correct code — and this codebase
forbids weakening a test to make it pass.

---

## 3. Per-axis findings not covered above

### Engine

- **Conflict-by-return-value is where GCS is migrating *to*.** They measured their
  exception path at ~2.4µs / 17,500 instructions per throw, `libgcc_s` at 30.7% of one
  benchmark, 19.4M throws across the MiniZinc corpus worth 10-22% on six models. Our
  `Propagator.result = Fixpoint | Conflict of Explanation.t` is already the destination.
  **Do not "simplify" to exceptions.**
- **The engine rebuilds the whole trail per propagator call.** `engine.ml:60` calls
  `Store.trail_entries`, which allocates a list of the entire trail, then reads only the
  newest `n_new`. The O(1) accessor `Store.trail_entry` already exists and its own comment
  says `trail_entries` "allocates the whole list; this does neither". Ten-line fix; it is
  also exactly the minor-GC pressure D-0001 names as the known OCaml risk, available now
  instead of at M6-T2.
- **The trail records no propagator identity** — D-0011's own named blocker for M2-T3, in
  its own words: "Clause learning walks the trail, and there the explanation is all there
  is… It should be closed before M2-T3 starts, not during it." GCS's shape (one
  `ConstraintID`, several propagators) shows the "trail records the propagator" horn works,
  and keeps D-0003 open rather than forcing it.
- **Do not copy epoch-copy backtracking.** GCS deep-copies every domain per node; our
  trail is O(changes) and is the better structure. Their own doc admits the cost.
- **Bound-fact chains are width-proportional.** `order_reason.ml:38-43` builds one literal
  per value between declared and current bound (D-0010 requires the chain). D-0005's
  hole-span cap does *not* cover it. GCS's rule: "Every bounds-consistency path must be
  independent of domain width", and they flag reason-side width as the subtler hazard —
  "not a pruning loop but a **reason**… assembled on the propagation path and then
  discarded unread". Nothing in our SPEC subset triggers it today. Writing the policy down
  now costs nothing.

### Proof logging

- **Our eager order encoding is Θ(domain width) with no cap.** `encoding.ml:129-132`
  writes `hi - lo - 1` ladder clauses per variable at `declare_int`; `max_direct_values`
  guards only the *direct* encoding. `var 0..1000000: x` produces a million-row `.opb`
  today. This is the largest structural gap found, and it is correctness-of-scale, not
  performance. (GCS's primary encoding is a binary/bits sum at O(log w) with order/eq/
  interval atoms introduced lazily in-proof by `red`. We should **not** adopt bits — it
  would invalidate PROOF-FORMAT §3, D-0007, D-0010 and every justification, and GCS says
  plainly "bit sums propagate badly". Adopt the *cap and the policy*, not the encoding.)
- **D-0009 is fixable, not fundamental.** It says a bound fact cannot be cited in a `pol`
  "as `Explanation.t` is shaped today". GCS pins boundary atoms to persistent top-level
  lines precisely so a step can cite them, and resolves literal → defining line through one
  shared tracker. We already have the analogue: `Encoding.consistency_id` is a citable
  line, and D-0018 trace lines are citable ids that nothing cites. It is a missing field.
- **Our `drop-line` mutation lane is green for the wrong reason** under 3.0, by its own
  script header's admission: dropping a line un-defines its label, so the lane fails as a
  *parse* error, not on the derivation. That is precisely the failure mode D-0020 exists
  to catch. GCS puts mutation knobs in the *emitter*, typed, next to each derivation, with
  a mandatory control lane that must verify honestly.
- **Hints are all-or-nothing** if we ever adopt them: an engaged-but-empty hint list
  restricts propagation to nothing. Half-hinting our D-0018 trace chain would turn a
  working proof into a rejected one. Worth 6-14× on a real model, 25% on a toy one — so
  do not benchmark it in isolation, and do not build it before M3-T3 measures something.
- **Size and verify time move in opposite directions.** GCS measured a 5.9× *smaller*
  proof that takes 3.5× *longer* to check at an identical search tree. Any proof-size
  optimisation we do without a verify-time control is a coin flip. Our M3-T3 should report
  `.opb` bytes, `.pbp` bytes and verify seconds separately.
- **We have no independent oracle on the `.opb`.** GCS re-derives the model from a
  versioned wire format and lets the CakeML-*verified* checker have the last word, with
  VeriPB as an untrusted elaborator, across 169 cases. Nothing checks that our `.opb` says
  what the `.fzn` says except `Model.check_assignment` on SAT answers — and D-0012 already
  recorded that a SAT run's nogoods carry no weight.
- **Keep the two-format writer.** GCS is 3.0-only and hardcoded; our D-0025 has 925 checks
  green under both. That is a real asset against a checker built from a moving upstream.
- **Do not copy `AssertRatherThanJustifying`.** GCS's own doc: "**Not a single one of them
  may ever be merged**, and nothing in the test suite or CI will stop you" — and a proof
  with `a` rules exits 0 while printing `s UNDER ASSERTIONS`, which their harness cannot
  see because it reads only the exit code. Our stricter rule has no such hatch to leak.

### Propagation

- **`int_eq` is bounds-only and loses holes**, as its own header documents: `x∈{0,2,4}`,
  `y∈{1,2,3}` propagates nothing. GCS maps `int_eq` to a domain-consistent `Equals` with
  interval symmetric-difference. Adopting it walks straight into D-0019 point 3 — a reason
  that must mention a hole is exactly where the direct encoding becomes forced — so the
  direct encoding and its I-X2 audit problem are prerequisites, not details.
- **Reification already has an answer, and it is ~224 lines.** GCS's dispatcher has the
  author supply three callables (enforce-hold, enforce-not-hold, entailment detector) and
  handles the 5-kind static → 4-way runtime collapse, the contrapositive table, trigger
  augmentation, and the propagator state "so the constraint can't get it wrong". This
  turns M3-T2 from "reified linear *and* reified comparison, each with five cases" into
  two propagators plus one shared helper. Known limitation to inherit knowingly: one
  trigger set per dispatcher, which is why GCS's own `linear_equality` opted out.
- **`PropagatorState` (entailed / idempotent / enabled) must ship with its checker.** GCS
  re-runs every honoured idempotence claim on every test and aborts if it infers anything,
  and downgrades claims from aliased scopes at install time. Their issue #889: a wrong
  interaction between an idempotence claim and a watch took one model from 767 nodes to
  **1,089,375**, and "getting this wrong is invisible in everything but the node count".
  Adopt the checker in the same commit as the enum, or do not adopt the enum. This matters
  for us concretely: `compile.ml` merges duplicate terms but `Linear.others_except`
  excludes *by position* "since a variable could in principle appear twice".
- **Our test suite is genuinely ahead in one respect and behind in two.** Ahead: measured
  reach rates per interesting state in the fuzzer (already borrowed from GCS's 987/37
  ablation). Behind: (a) nothing checks a propagator reaches the strength its `consistency`
  tag claims — our oracle checks soundness only, "it is fine to keep an unsupported one";
  (b) the fuzzer varies models but never search *order*, and since M1's whole nogood story
  is that the branch's own trace supports the refutation, a different tree is a different
  trace. GCS seeds data generation and branching from one announced replayable seed.
- **Decomposition: we generalise upward, GCS specialises downward.** Our `int_le`/`int_lt`
  are thin aliases of `Linear`, `int_eq` is two `Linear`s — stated reason is a smaller
  trusted core. GCS specialises 2-term unit forms at the frontend, and does it where it
  buys *strength* (`int_lin_eq` → domain-consistent `Equals`), only incidentally for speed.
  Ours is right for M1 and a real strength cost from M4.
- **Views (`±x + k`) and constants-as-variables** are what let `array_int_element` take a
  1-based index with no auxiliary variable. GCS records the trap they avoided: a MiniZinc
  redefinition that rebased an array through an `int_lin_eq` "silently downgraded" every
  value-pruning propagator behind it, worth 4/15 → 9/15 optimal on one family once fixed.
  Worth having before M4-T3. Note the proof-side question it opens (each view needs its own
  range literals) is unresolved for our encoding.
- **M4-T4 (`int_times`/`int_div`/`int_abs`) is much cheaper than it looks.** GCS's
  `constraints/innards/product_bounds.hh` is ~178 lines of `constexpr` free functions using
  no solver types beyond `Integer`: `div_floor`/`div_ceil` (explicitly *not* `operator/`,
  which truncates toward zero — the same trap `linear.ml:138-142` already works around),
  `isqrt`/`ceil_isqrt`, `product_bounds` as four corner products, `square_bounds` kept
  separate because the result is never negative, plus `square_filter`/`quotient_filter` for
  the excluded middle. It is honest about its own strength ("sound but not exact: in the
  sign-fixed-y case the corner quotients can leave an unsupported endpoint"). That is a
  proof-free, dependency-free OCaml module testable against brute force **today**.
- **Two SPEC decisions M4-T4 needs before any code.** GCS pins truncated division
  "rounding towards zero, like C++ and every constraint programming ecosystem we know of",
  with the remainder taking the dividend's sign; and treats division by zero as
  *relational*, not an error — "zero simply has no support in the divisor's domain… a
  constant zero divisor makes the constraint unsatisfiable rather than an error. This
  matches MiniZinc and XCSP3 semantics." **Our SPEC says nothing about either.**
- **One total predicate per constraint family, shared with the oracle.** GCS's whole
  divide/modulus family is anchored on an eight-line `is_in_relation(x,y,q,r)` whose comment
  reads "Everything else in this file is scaffolding to propagate exactly this" — and the
  same predicate backs the GAC tabulation fallback, so propagator and fallback cannot
  disagree about the relation. We already have the analogue in `Model.check_assignment`
  (I-S1); the move is to *share* it rather than restate it.
- **`all_different` is one propagator with two stages, not two propagators.** The cheap
  value-consistency pass runs first and, if it inferred anything, returns without an
  idempotence claim so cheaper propagators react before the matching/SCC work. The cutoff
  is measured, not chosen: 256 var-value pairs, "22 × 33 = 726 (langford --size=11) is
  1.36× faster staged, while 10 × 10 = 100 (QWH quasigroup7) is ~2% slower, so the cutoff
  sits between them, at the rounded geometric mean." **This is how our M4-T1 and M4-T2
  should coexist: one constraint, one propagator, the consistency tag choosing the shape.**
- **The GAC Hall justification cites many model rows in one derivation** — per Hall value a
  recovered at-most-one line, per Hall variable an at-least-one line. That makes the D-0011
  amendment (M2-T0) a hard prerequisite for M4-T1, not a tidy-up. And that same Hall reason
  is a *lazy reason over the Hall variables* — variables named, domains materialised only if
  read — which is the strongest single argument for doing the reason/justification split
  **before** M4 rather than after.
- **Delegation is a first-class install outcome.** GCS's `Multiply` with a constant operand
  builds a `LinearEquality`, gives it its own constraint id, installs it, and reports that
  it has delegated itself in full. Our `compile.ml` does something adjacent by hand; the
  difference is GCS delegates *after* reading initial domains, so it can delegate on a
  dynamic property rather than only on syntax.

---

## 4. Things GCS tried and abandoned — do not re-run these experiments

- **Non-backtrackable refined watches.** A watch can fire and be consumed inside a
  `propagate()` that another propagator's contradiction ends before the owner processes it
  — an "abandoned fire" — and a non-backtrackable scheme loses it permanently.
- **Incremental covering-set maintenance for slack waking.** Prototyped, measured,
  abandoned: it did not close the cliff and made the tight case 2.4× worse, because "there
  is no sort-free minimal cover".
- **A logger-side per-constraint proof-data store.** "We built that, then removed it" —
  the state is owned by the constraint, which outlives the search.
- **A central assertion-hint enum**, and a reason-coalescing pass ("deleted, not ported").
- **Slack-covering refined watches ship off by default**: the win is confined to
  inequalities of ~128+ terms, a mis-engagement is ~5× slower when the constraint turns
  tight, and a refined wake costs ~38ns against a coarse trigger's ~4.5ns. Copying this
  would be copying the part of GCS that GCS turned off.

---

## 5. Proposed roadmap rows

The three sweeps each proposed IDs independently and collided (three different `M1-T22`s).
Deconflicted below. **Nothing here has been applied to `docs/ROADMAP.md`.**

| Proposed ID | Task | Why now | Depends on |
|---|---|---|---|
| M1-T22 | Fix `del range` off-by-one in `Writer.wipe_level`; correct PROOF-FORMAT §5 | Verified bug in shipped output, 7 lines across 5 models; I-X3 violation the audit cannot see | M1-T19 |
| M1-T23 | Checked arithmetic in `Linear`/`Ne` + declared-domain cap at compile time | The only *soundness* gap found; a wrapped product is a wrong pruning with an accepted proof. Add an overflow axis to `test_matrix.ml` | none — good parallel task |
| M1-T24 | Trail-cursor walk in `Engine.propagate`, replacing `Store.trail_entries` | Allocates the whole trail per propagator call; the O(1) accessor already exists | none |
| M1-T25 | Cap the eager order encoding; state a domain-width policy in SPEC | Θ(width) rows per variable, uncapped. Needs a decision record — it may mean refusing a model | M1-T4 |
| M1-T26 | Move mutation knobs from proof text into the emitter; add a mandatory control lane | `drop-line` is currently green as a parse error, not a derivation failure — the D-0020 failure mode | M1-T15, M1-T19 |
| M1-T27 | Decision record: bound-fact chains are width-proportional; state the policy | `order_reason.ml` builds one literal per value; D-0005's cap does not cover it. Doc-only now; interval restatement is M4 | none |
| M2-T0 | **Amend D-0011**: record that D-0015 closed the ADT gap; multi-row derivations permitted | A literal reading forbids writing a Hall-interval justification at all. Decision record only | **must land before M4-T1** |
| M2-T5 | `Domain.result` reports change granularity; engine masks wakes by trigger kind | Delivers what ARCHITECTURE.md already promises. Ship with a `BAGUETTE_DEBUG` I-P2 re-run check in the same round | blocks M2-T6 |
| M2-T6 | Do not re-wake a propagator from its own prunings; aliased-scope veto + claim re-checker | Copy GCS's two guards, not its claim/replay engine. Re-run the *proof* suite, not just unit tests | M2-T5 |
| M2-T7 | Record propagator instance id on every trail entry and on `Conflict` | Closes D-0011's own named blocker for M2-T3; lets `Store.conflict_facts`' one-shot slot go | **blocks M2-T3** |
| M2-T8 | Propagator interface v2: declarative `Reason` + separate `Justification`, via an inference context | §1.1. Collapses I-P4+I-P5 into one type, deletes the trail scan, precondition for M2-T3/M3-T2/M4. Non-narrowable reasons only (I-X6) | M2-T7; before M2-T3 |
| M2-T9 | Literal → defining-proof-line index in `Justify.ctx`, populated by `Trace` | Closes D-0009's "not today" by adding the field it names as missing. May also close D-0019's clause-in-a-`pol` gap — **verify, do not assume** | M2-T8 |
| M2-T10 | Harness: per-node consistency checking against the brute-force oracle | Nothing verifies the `consistency` tag SPEC makes normative. Must assert *at least* the declared level (see §2.3) | needs a search trace hook |
| M2-T11 | Fuzzer: randomise branching order from the announced seed | A different tree is a different trace, and the trace is what supports the nogood | M1-T16 |
| M3-T4 | Reification dispatcher: three callables, framework does the collapse and contrapositive | Turns M3-T2 into two propagators plus one shared helper | M2-T8, M3-T0 |
| M3-T5 | Proof benchmark reporting `.opb` bytes, `.pbp` bytes **and** verify seconds separately | They move in opposite directions at identical search; a size-only benchmark misleads | M1-T14; absorbs M3-T3 |
| M4-T0 | Views (`±x + k`) and constants-as-variables | Should precede M4-T3; GCS's aux-variable alternative silently downgraded propagators behind it | before M4-T3 |
| M4-T1/T2 | `all_different`: **merge the two existing rows** — one propagator, one consistency tag, two stages (cheap VC pass, then Hall/Régin) | GCS defers the expensive stage *inside* one propagator; cutoff a measured 256 var-value pairs. This is how BC and GAC coexist | **M2-T0**, D-0004 |
| M4-T4a | Integer interval arithmetic as a standalone, proof-free, unit-tested module | Port of GCS's `product_bounds.hh` (~178 lines, `constexpr` free functions, no solver types). No proof machinery, testable against brute force today | none — good parallel task |
| M4-T4b | `int_times`/`int_div`/`int_abs` over M4-T4a | Needs two SPEC additions first (§3, Propagation). Anchor on one total `is_in_relation` predicate shared with the oracle | M4-T4a, M2-T8 |
| M4-T5 | RUP hints on trace lines and nogoods, gated on M3-T5 showing they are needed | Hinted `rup` is O(hints), hint-free is O(live database). All-or-nothing — half-hinting breaks a working proof | M3-T5, M2-T9 |
| M4-T6 | **Spike** (not a build): in-proof tabulation as the GAC route for small-domain relations | Would give GAC arithmetic for ~10 lines per constraint with *no OPB change*, because the table is derived in-proof. **Unverified that this transfers to our order encoding** — hence a spike | M4-T4b |

---

## 6. Open / unverified

- **D-0003 is narrowed, not settled.** GCS's answer is reading (b), but *not* the shape our
  `Deferred` assumes: they rejected closure-valued reasons for declarative reason data.
  Nothing in GCS reads (a) as the contribution — their "higher-order" content is a typed
  serialisable witness for an *external* justifier, a cross-language concern we do not
  have. The pointed finding for whoever closes D-0003: **we have a reified cutting-planes
  expression on the trail where the mature solver has a closure, and nobody has yet said
  what the reified form buys.** That is evidence against (a) being the productive axis —
  or, if (a) *is* the contribution, an argument that needs making explicitly.
- Whether the literal → line index closes the D-0019 clause-in-a-`pol` gap: **unverified**.
- Whether GCS's in-proof table derivation (the basis of its cheap GAC arithmetic) is
  reachable under our order encoding: **unverified**, and the reason M4-T6 is scoped as a
  spike rather than a build.
- Whether GCS's boundary-pin answer to chain width transfers under D-0010: an encoding
  question for whoever owns PROOF-FORMAT.
- GCS's claim that VeriPB 3.0 needs no `f` rule at all, which contradicts
  `PROOF-FORMAT.md:157`: **untested here.**
- No benchmarking was done. The O(n²·|trail|) figure for `Linear.propagate` is read off
  the code, not measured.
