# Worklog

Coordination between concurrent Claude sessions. **Append only.** Add rows at the bottom
of a section; never reflow, reorder or rewrite rows you did not write. That is what makes
git merge two sessions' edits instead of conflicting.

Read this file at the start of every session. Claim before you edit. See `CLAUDE.md`.

---

## Active claims

**AN OVERNIGHT CORPUS RUN IS IN FLIGHT ON `fataepyc-07`. Do not re-launch it; read it.**

Launched 2026-09-22 ~16:05 from `/scratch/arthur/corpus_run.sh`, **detached (`setsid nohup`)**,
64-way parallel, 32 GB ulimit per job. It survives the SSH session that started it.

- **results**: `/scratch/arthur/corpus-out/results.tsv` — TSV, one line per instance:
  `id <TAB> outcome <TAB> fzn-bytes <TAB> pbp-bytes <TAB> detail`
- **per-instance logs**: `/scratch/arthur/corpus-out/log/`
- **completion marker**: a final `DONE-<epoch>` line in `results.tsv`. **If that line is absent
  the run was cut off**, and the file is partial — say so rather than reporting the total.
- 436 instances queued (every `.mzn` in the corpus, smallest data file each).

**It flattens with the M7-T3 library** (`MZN_SOLVER_PATH=/scratch/arthur/baguette/tools`), so
constraints stay high-level, and it runs the node's `main` at `b6fa825` — M7-T1's unlimited
defaults and M7-T2's annotations both in.

**Every solved instance has its proof checked by veripb 3.0.2**, and `PROOF-REJECTED` is its own
bucket, never folded into a failure. That bucket is the point.

**At 232 of 436 the distribution was**: `REFUSED-MODEL` 186, `FLATTEN-FAIL` 25,
`REFUSED-LIMIT` 14, **`PROOF-REJECTED` 3**, `SOLVE-ERR-134` 2, `OK-PROOF-VERIFIED` 2. **Read
that as provisional**: it is the first half of an alphabetical walk, so it is 2008–2012-heavy
and the early years are the least likely to flatten at all.

**Three things already visible, for whoever picks this up:**

1. **`PROOF-REJECTED` is not rare.** Three in the first 232, against two verified. **M7-T6 is
   not an exotic corner** — and remember D-0066: on an UNSAT instance the same defect is
   *accepted silently*, so this bucket is a **lower bound**.
2. **`REFUSED-MODEL` (exit 2) dominates at 186.** That is the front end refusing a builtin or a
   declaration, and D-0067 says the residual wall is **set-literal domains**. Worth confirming
   from the logs before anyone builds anything.
3. **Some `FLATTEN-FAIL` is the harness, not the corpus** — e.g. *"no function or predicate with
   this signature found: `int_search(array[int] of var int,string,string,string)`"*, which is a
   2008-era annotation syntax MiniZinc 2.10.1 no longer accepts. **Do not count those as
   unsupported instances.** Separate harness failures from solver findings before quoting any
   number.

**SOLVE-ERR-134 is SIGABRT** (134 = 128+6) and is unexplained — two instances. That is worth a
look on its own; an abort is not a refusal.


**Wave twenty-six is COMPLETE: M7-T1, M7-T2 and M7-T3 all merged, released and pushed.**

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `CLAUDE.md`, `Makefile`, `scripts/**`, `bench/**`,
`bin/main.ml`, `lib/flatzinc/**`, `lib/core/dune` and all merging.

Wave twenty-four (M4-T7, M4-T3) is merged, released and pushed. **Every builtin in SPEC §2.1 is
now implemented** — `planned` is empty. Baseline: **2663 ok / 0 FAIL, 280 matrix, 44 mutation,
85/85 models**.


**Wave twenty-four is running: M4-T7 (agent-defid) and M4-T3 (agent-element).**

**agent-defid holds** `lib/core/{explanation,justify}.ml`, `lib/core/prop/alldiff.ml`, and
`test/unit/{test_justify,test_prop,test_trace}.ml`. M4-T7 closes the gap M4-T1 made concrete:
`Justify.defining_lit` exists and has **no caller**, because nothing in an `Explanation.t`
*value* can ask for one. **This is the row where `explanation.ml`'s no-new-constructor rule is
most likely to be genuinely spent** — D-0044's table has held eight times, and if this breaks it,
the argument is the deliverable as much as the code.

**agent-element holds** `lib/core/prop/element.ml` (new), `lib/core/dune`, `lib/flatzinc/**`,
`test/models/**`, `test/expected/**` and `test/unit/{test_compile,test_flatzinc,test_endtoend}.ml`.
M4-T3 is `array_int_element`, **unblocked by M4-T0**: D-0058 settled that a 1-based index is
`View.shift (View.of_var i) (-1)` and prunes the index directly, with **no channelling step at
which to lose value consistency** — which is the failure GCS hit and M4-T0's row warns about.

**They meet only at `lib/core/dune`**, which is agent-element's (it adds a module; agent-defid
adds none). `lib/core/view.ml` is **read-only to both** — it landed in wave twenty-one and
neither row should be changing it.

**A standing note for both**: `test/models/width_sat_depth.fzn`'s header comment is stale
(43 ms against ~160 ms today, D-0062) and `test/models/**` is agent-element's this wave. If it is
convenient, fix the comment rather than delete it — a figure with a date on it is how the
regression was caught at all.

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `CLAUDE.md`, `Makefile`, `scripts/**`, `bench/**`,
`lib/proof/**`, `lib/core/{search,engine,store,domain,var,view}.ml` and all merging.

Wave twenty-three (M5-T1+T2, M6-T6) is merged, released and pushed. **M5 is open and every
milestone M0–M5 now has its core rows done.** Baseline: **2608 ok / 0 FAIL, 280 matrix,
44 mutation, 78/78 models**.


**Wave twenty-three is running: M5-T1+M5-T2 (agent-bb) and M6-T6 (agent-bisect).**

**agent-bb holds** `lib/core/{search,engine}.ml`, `lib/proof/{writer,encoding}.ml`,
`bin/main.ml`, `lib/flatzinc/**`, `test/models/**`, `test/expected/**` and
`test/unit/{test_proof,test_endtoend,test_output,test_compile,test_flatzinc,test_matrix}.ml`.
M5-T1 and M5-T2 go together because `conclusion BOUNDS` is the proof half of branch and bound;
splitting them would put the search and its conclusion in different branches.

**It is not starting from nothing**: `Ast.solve_kind` and `Model.objective` already carry
`Minimize`/`Maximize`, `Writer.obju` exists at `writer.ml:1183`, and the `Bounds` conclusion
variant at `:1244`. **`PROOF-FORMAT.md` line 136 already records the trap**: `obju` *"needs
explicit subproofs — Proofgoal #1 could not be autoproven"*, measured and filed against M5.

**agent-bisect holds `bench/**` and nothing else**, read-only over the rest. M6-T6 is the
`width_sat_depth` regression: the model's own header says 43 ms, it is 160 ms shipped and
**590 ms with learned propagation off**, so the tree underneath costs roughly **14×** what the
comment claims. M6-T1 hypothesised M2-L13 as the cause; measurement showed it is the
**mitigation** (worth ~4×). **The row says bisect, not hypothesise** — `perf` is unavailable on
this kernel, so the tool is `git bisect` plus a wall-clock harness, in its own worktree.

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `CLAUDE.md`, `Makefile`, `dune-project`,
`scripts/**`, `lib/core/prop/**` and all merging.

Wave twenty-two (M4-T1, M6-T1) is merged, released and pushed. Baseline: **2564 ok / 0 FAIL,
280 matrix, 44 mutation, 73/73 models**.


**Wave twenty-two is running: M4-T1 (agent-hall), ALONE.**

**This row goes out solo deliberately.** Its own text says it is *"an experiment, not
propagator number eight"* and to budget it as one; `docs/EXPLANATION-REVIEW.md` §3 calls it the
row where the project's central claim first becomes falsifiable. Precedent: wave twelve
dispatched M2-L3 alone for the same reason.

**agent-hall holds** `lib/core/prop/**`, `lib/core/dune`, `lib/core/{explanation,justify}.ml`,
`lib/proof/encoding.ml`, `lib/flatzinc/**`, `test/models/**`, `test/expected/**`, and
`test/unit/{test_prop,test_justify,test_compile,test_flatzinc,test_trace,test_proof}.ml`.

**`explanation.ml` is lent, not given.** Its header still forbids a new constructor without a
decision record and **that is not suspended** — but this is the first row that might genuinely
need one, so it holds the file and reports rather than being blocked by a boundary. `Combine`,
`Weaken` and `Model_row` were built for exactly this; if they suffice, that is itself the
result D-0027 anticipated.

**Added alongside wave twenty-two: M6-T1 (agent-prof).**

**agent-prof holds `bench/**` and nothing else** — `lib/`, `bin/`, `test/` and `scripts/` are
**read-only** to it. M6-T1 is "profile; establish the propagation hot path", and it is a
measurement row: if it finds a hot spot it **reports** it, it does not fix it. That is what
keeps it disjoint from agent-hall, which holds most of `lib/`.

**It is no longer premature, which it was when I declined it in wave seventeen.** The suite is
64 models with genuinely hard ones (`php_wide_unsat` is 1439 nodes unlearned), and PB
propagation, arithmetic and reification have all landed since. There is now something to
profile. It also has to land before M6-T2 (domains/trail to `Bigarray`) and M6-T3 (buffered
proof writing), or both of those are guesses.

**The trap it must not fall into is already measured**: `bench/README.md` §3 and §3a found that
most models sit at the **process floor**, where the timing column measures `exec` and not this
solver. §3b already split propagation from emission (M1-T47). It must build on those rather
than rediscover them.

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `CLAUDE.md`, `Makefile`, `dune-project`,
`scripts/**`, `bench/**`, `bin/main.ml`, `lib/core/{search,engine,store,domain,var,view}.ml`
and all merging. I am doing **M6-T5** (`check_determinism.sh` ignoring `test/models/PENDING`)
myself while this runs — `scripts/` only, no overlap.

Wave twenty-one (M4-T0, M4-T4b, M2-T10) is merged, released and pushed. Baseline: **2549 ok /
0 FAIL, 280 matrix, 44 mutation, 64/64 models**.


**Wave twenty is COMPLETE: M2-L15 and M3-T2+M3-T4 merged, released and pushed.**

**Wave twenty-one is running: M4-T0 (agent-views) and M4-T4b (agent-arith).**

**agent-views holds the VARIABLE layer**: `lib/core/{var,store,domain}.ml`, `lib/proof/{lit,encoding}.ml`,
and `test/unit/{test_core,test_domain,test_proof}.ml`. M4-T0 is views (`±x + k`) and
constants-as-variables. Its row opens a proof-side question — **each view needs its own range
literals** — which is why it holds `lit.ml` and `encoding.ml`.

**agent-arith holds the PROPAGATOR layer**: `lib/core/prop/**` (new modules only — it may
**read** every existing propagator and **edit none**), `lib/core/dune`, `lib/flatzinc/**`,
`test/models/**`, `test/expected/**`, `test/unit/{test_prop,test_interval,test_compile,test_flatzinc}.ml`.
M4-T4b is `int_times`/`int_div`/`int_abs` over M4-T4a's `interval.ml`.

**`lib/core/explanation.ml` and `lib/core/justify.ml` are NEITHER agent's.** A new constructor
needs a decision record and that is not suspended; arithmetic justification is exactly where one
would be wanted. Route it to me.

**M4-T1 IS NOT DISPATCHED, and the reason is not technical.** Its blockers M1-T31 and M2-T17 are
both DONE. But the row says **D-0048 should be closed before it, not after** — is a reified
explanation a research output? — because that is the row where the reified form either
demonstrates what it buys or looks like expensive ceremony. Decided before, M4-T1 reads as
evidence; decided after, it reads as a verdict already reached. **That is a question for the
project's owner, and it is with them.**

**Added to wave twenty-one: M2-T10 (agent-oracle), dispatched alongside.**

**agent-oracle holds** `lib/core/{search,engine,debug}.ml`, `test/unit/dune`, a new
`test/unit/test_consistency.ml`, and `test/unit/test_engine.ml`. M2-T10 is the per-node
consistency harness: **nothing verifies the `consistency` tag that SPEC §2.2 makes
normative**, and today's oracle checks soundness only.

**It is dispatched now because the timing is unusually good**: `reif.ml`, `reif_lin_le.ml` and
`reif_lin_eq.ml` landed yesterday, and `int_times`/`int_div`/`int_abs` plus `all_different` are
next — six new declared consistency levels with nothing checking any of them.

It reads `lib/core/prop/**` (agent-arith's) and must **edit none of it**. If it finds a
propagator weaker than its declared level, that is a **finding to report, not to fix** — and
weakening the test to match is forbidden.

**M4-T1 goes out as wave twenty-two** the moment agent-arith releases `lib/core/prop/` and
`lib/core/dune`. Nothing else blocks it: **D-0048 never did, and that claim is struck** — the
dependency ran backwards, since M4-T1 is the evidence that would inform D-0048 rather than
something waiting on it.

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `CLAUDE.md`, `Makefile`, `dune-project`,
`scripts/**`, `bench/**` and all merging, as standing.

Wave nineteen (M2-L13, M2-L14) is merged, released and pushed; gate re-verified on `main`
after the merge: **2256 ok / 0 FAIL, 280 matrix, 44 mutation, 44/44 models, `check: ok`**.


**Wave nineteen is COMPLETE: M2-L13 and M2-L14 merged, released and pushed. Every file is free.**

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `CLAUDE.md`, `Makefile`, `dune-project`,
`scripts/**` and all merging, as standing.

Wave eighteen (M2-L12, M3-T1) is merged, released and pushed. Baseline: **2190 ok / 0 FAIL,
280 matrix, 44 mutation, 39/39 models**, and **231 nodes suite-wide** — that last number is
M2-L13's target and M2-L12 pinned it.


**Wave eighteen is running: M2-L12 (agent-prop) and M3-T1 (agent-reify).**

**Two real editing tasks this time**, not a row plus a study, because the file split finally
allows it: M2-L12 is `lib/core/**`, M3-T1 is `lib/proof/**`, and they meet at exactly one
place, handled below.

**agent-prop holds `lib/core/**`, `bin/main.ml`, and all of `test/unit/**` EXCEPT
`test_proof.ml`** (including `test/unit/dune` and `test/models/**`). M2-L12 makes learned
constraints propagate: unit clauses as level-0 bounds first, then widen `bool_clause` to a
threshold. D-0052 settled that this is a **widening, not a new family**, so D-0044's bet is not
spent.

**agent-reify holds `lib/proof/**` and `test/unit/test_proof.ml` ONLY.** M3-T1 is `red`-based
definitions for reified variables. `Writer.red` already exists (`writer.ml:1069`) and is
already used for channelling (`encoding.ml:406,411,420`), so this extends a working pattern.

**THE ONE PLACE THEY MEET, and it is a hard constraint on agent-reify.** Fourteen `lib/core`
modules call into `Encoding` — `trace.ml` alone 11 times, plus `ne.ml`, `ladder.ml`,
`learned.ml`, `search.ml`, `linear.ml`, `lin_eq.ml`, `bool2int.ml`, `order_reason.ml`,
`reason.ml`, `justify.ml`, `analysis.ml`, `pb_analysis.ml`, `checked.ml`. **agent-reify may
ADD to `Encoding` and `Lit` but must NOT change any existing signature**, or agent-prop's
branch stops compiling. Same protocol as the standing `lib/proof/lit.ml` request above, and
for the same reason.

**A precondition on M2-L12 that is part of the row, not optional.** D-0052 marks the figure its
step ordering rests on — "~70 of 88 learned clauses are unit" — as **provisional, ±5, from
proof-text parsing**. agent-prop **re-derives it from an instrumented run first** and lets the
measurement pick the order. If the histogram comes back different, the plan changes and that is
the row working as intended.

**And M2-L12 must revisit `Retention` in the same change.** A trace line from a learned-clause
instance is RUP only while that constraint is **live**. Today nothing propagates a learned
constraint, which is the independence D-0051 assumed; giving one a registered instance couples
retention to the propagator set. D-0051 named this as the condition that reverses its keep-all
verdict, so the verdict gets re-run, not inherited.

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `CLAUDE.md`, `Makefile`, `dune-project`,
`scripts/**`, `bench/**` and all merging, as standing.

Wave seventeen (M2-L4, plus D-0050/D-0051/D-0052 and M4-T5's gate) is merged, released and
pushed. Baseline to beat: **2129 ok / 0 FAIL, 280 matrix, 44 mutation, 39/39 models**.


**Wave seventeen is COMPLETE: M2-L4 (agent-del) merged and released; three read-only
studies done (D-0050, D-0051, D-0052, M4-T5's gate). Every file is free.**

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `CLAUDE.md`, `Makefile`, `dune-project`,
`scripts/**`, `bench/**` and all merging, as standing.

**The one design question M2-L4 must settle before writing any policy** (its row says so, and
D-0045 found it): `Writer.wipe_level l` deletes every id tagged at level `>= l`, so a learned
constraint tagged at the level it was learned at is deleted **by the backjump**. If the
retention policy also deletes it, that is an I-X2 double-delete arriving from two owners.
**Decide who owns a learned constraint's lifetime first.**

Wave sixteen (M2-L11 agent-ladder, M2-T17 agent-size) is merged, released and pushed; its one
carry-over is that **M2-L6's `pb-*` figures in any older note are not to be trusted** — see the
wave-sixteen handoff and D-0047's amendment.


**Wave sixteen is COMPLETE: M2-L11 (agent-ladder) and M2-T17 (agent-size) are both merged,
released and pushed. Every file is free.** The whole tree is unclaimed as of this line.

The split is the usual one and it is forced. **agent-ladder holds all of `lib/`**, because
M2-L11 changes what `Linear` hands to PB analysis: that is `lib/core/prop/linear.ml`,
`order_reason.ml`, `pb_analysis.ml`, `justify.ml`, `search.ml`'s counters and
`lib/proof/encoding.ml`, which is the whole learning vertical plus the encoding edge. The
roadmap already says `lib/core` is held **exclusively** for the M2L sequence, so its partner
has to be outside `lib/` entirely.

**agent-size (M2-T17) is that partner, and it was scoped to be.** The row exists because
`docs/EXPLANATION-REVIEW.md` §6 asked for explanation size to be a tracked number before
M4-T1; it is deliberately specified against the **emitted `.pbp` artefacts**, which already
contain every literal count it needs, so it changes no `lib/` file and adds no counter. It
owns `bench/**` and nothing else. Same shape as M2-L8, for the same reason.

**Orchestrator holds** `WORKLOG.md`, `docs/**`, `Makefile`, `dune-project`, `scripts/**`
and all merging, as standing. Neither agent commits to `main`.

**Before this wave dispatched, three stale things were corrected** — read these before
trusting a roadmap row you remember:

- **M1-T44 was NOT open.** It was marked "TODO — highest priority open defect" and it has
  been fixed for some time; a wave aimed at it would have found nothing to do. Re-verified
  through the CLI on the row's own minimal model: `s VERIFIED UNSATISFIABLE`, veripb 3.0.2,
  binary `0011dc99`. The fix was **not** the one the row proposed (`rests_on_a_clause` was
  never the defect); the cause was a bound settled over a hole being stronger than the trail
  entry carrying it, fixed in `linear.ml`'s `settled_over_lo`. `test/models/root_hole_unsat.fzn`
  is byte-for-byte that minimal model, so the gate runs it every time.
- **M2-L11's test (c) said "verified under both formats".** It was written before D-0046;
  there is one format. Corrected on the row, and agent-ladder is told.
- **The `Makefile` line 106 request from agent-bench is CLOSED** — the comment already says
  `ARGS="-r 9"` and `23 of the 38 rows`. It landed with the wave-fifteen merge and was never
  marked.

Wave fifteen (M2-T16 agent-drop, M2-L8 agent-bench) is merged, released and pushed; every
file it held is free.


**Wave fifteen is running: M2-T16 (agent-drop) and M2-L8 (agent-bench).**

**M2-T16 is RELEASED, 2026-09-18 (agent-drop).** Moved to `## Completed`; handoff notes at
the bottom of the file. Every file except `bench/**` is free again. M2-L8 (agent-bench) is
still running. Note for whoever merges: `Makefile`'s `bench` comment now says `ARGS="-r 9"`
and `23 of the 38 rows`, replacing a `-F 2.0` example for a flag agent-bench removed.

**agent-drop has the whole repo except `bench/`**, and that is not laziness in the split:
removing `Writer.V2_0` breaks every test that names it, so the code half and the test half
**cannot** be separate sessions — a branch that does one without the other never compiles,
and this project's rule is to commit as soon as it compiles. M2-L8 is the only task that is
genuinely orthogonal, because every counter it needs (`learned`, `pb-fallback`, `skipped`)
is already on `--stats`, so it reads stderr and touches no `lib/` file at all.

Previously: wave fourteen — M2-L6 (agent-pb) and M2-T14 (agent-fmt2) — is merged, released and pushed. **With M2-L6 in, the M2-L
learning sequence is complete except M2-L4, M2-L7 and M2-L8.**

It was dispatched as: **M2-L6 (agent-pb) and M2-T14 (agent-fmt2).** agent-pb has all of
`lib/` — M2-L6 is the PB conflict analysis and touches the whole learning vertical — so its
partner is deliberately **outside `lib/` entirely**: a read-only-over-`lib/` audit of the
format-2.0 path. The two share no file; `test_justify.ml` goes to agent-fmt2, so agent-pb
puts its justification tests in `test_learn.ml` / `test_analysis.ml`.

Previously: wave thirteen (M2-L5 agent-reduce, M2-L10 agent-cover) is merged, released and pushed. M2-L10 was the row that unblocks the
measurement half of M2-L4, M2-L6 and M2-L8, which were deliberately held back for it.

Previously: **wave twelve was M2-L3, ALONE.** The M2-T3 briefing says twice that this row
should have `lib/core` exclusively, and M2-T10 — the obvious partner — needs a hook in
`search.ml`, so there is no honest parallel task. Waves ten and eleven are merged,
released and pushed. Wave ten was dispatched 2026-09-18 by the orchestrator: one git worktree each
under `.claude/worktrees/<tag>`, on branches `wave10-concl` / `wave10-cut` / `wave10-flaky`,
so no two share `_build`'s global lock. Build with `dune build --root .` from inside the
worktree. Baseline before dispatch was `6761435`, `make check` green at 1625 unit checks.

| Task | Files being touched | Session | Since |
|---|---|---|---|
| M7-T9 | `lib/core/search.ml`, `lib/flatzinc/builder.ml`, **`lib/flatzinc/model.ml`**, **`compile.ml`'s `phases_of_search` match arms (~:428-435) ONLY**, `test/unit/test_flatzinc.ml`, new `test/models/` + `test/expected/` | agent-strategy | 2026-09-23 |
| M7-T11 | **`lib/flatzinc/compile.ml` — `reject_set_domain` (~:266) and its call site (~:466) ONLY; `phases_of_search` belongs to M7-T9**, `lib/proof/encoding.ml`, `lib/core/domain.ml`, `test/unit/test_compile.ml`, `test/unit/test_proof.ml`, new `test/models/` + `test/expected/` | agent-holes | 2026-09-23 |
| M7-T5 | `test/unit/**` EXCEPT the four files above; read-only over `lib/` | agent-vacuity | 2026-09-23 |
| M2-T16 | **everything except `bench/**`** — the 2.0 removal lands atomically | agent-drop | 2026-09-18 |
| M2-L8 | `bench/**` only; read-only over `lib/` and `test/` | agent-bench | 2026-09-18 |
| M2-L6 | all of `lib/`, `test/unit/test_learn.ml`, `test/unit/test_analysis.ml`, `test/unit/dune`, new files under `test/models/` + `test/expected/` | agent-pb | 2026-09-18 |

**Wave twenty-seven, dispatched 2026-09-23 from `24336ee`.** Three rows, one worktree each
(`wave27-search` / `wave27-rup` / `wave27-guard`), files disjoint. All three are children of
D-0068, the first full corpus run. `lib/proof/encoding.ml` goes to agent-guard; if agent-rup
needs it, that is a `## Cross-session requests` row, not an edit.

| Task | Files being touched | Session | Since |
|---|---|---|---|


_(M2-L3 released 2026-09-18 by agent-learn3 — see `## Completed` and `## M2-L3 handoff`.)_

_(M2-T14 released 2026-09-18 by agent-fmt2 — see `## Completed` and `## M2-T14 handoff`.)_

Two rounds are recorded in `## Completed` below. The rows that stood here on
2026-09-15 (`integration`, M1-T12, M1-T13) were stale — see the handoff note "the
claims table had rotted" — and the round dispatched after it (M1-T18/T19 agent-proof3,
M1-T20 agent-matrix, M1-T21 agent-output, one worktree each so that no two shared an
`_build` lock) is merged and released.

**Read-only review, 2026-09-18 (agent-xreview).** A session from
`~/Explanations-by-constraint-decomposition` reviewed the explanation mechanism against the
explanation literature and added `docs/EXPLANATION-REVIEW.md` plus seven rows under
`## Cross-session requests`. It claimed no task ID, edited **no** file under `lib/`, `test/`,
`bench/` or `scripts/`, and committed nothing — `WORKLOG.md` and `docs/**` are
orchestrator-held, so route or revert these two files as you see fit. `bench/**` was left
alone throughout (M2-L8 / agent-bench is live).

| M7-T6 | `lib/core/search.ml`, `lib/proof/writer.ml`, `test/unit/test_learn.ml`, `test/models/{rup_level0_nogood_sat,empty_model_sat}.fzn` + expected, `test/models/PENDING`, `docs/DECISIONS.md` | agent-rup | released 2026-09-23 — D-0070 |

## Cross-session requests

Need a change in a file someone else has claimed? Write it here and move on to other
work. The owning session picks it up.

| Request | For file | From | Status |
|---|---|---|---|
| `lib/proof/lit.ml` is a shared dependency: agent-proof may **add** to it but must not change the existing signatures of `pbvar`, `t`, `ge`, `le`, `eq`, `ne`, `negate`, `to_string`, `var_name`, since agent-core compiles against them | `lib/proof/lit.ml` | orchestrator | standing |
| `WORKLOG.md`, `docs/**`, `dune-project`, `Makefile`, `scripts/**` and all committing are held by the orchestrator this round — agents touch none of them | — | orchestrator | standing |
| **M1-T46**: `lib/core/search.ml:260-261` quotes veripb 2.2.2's `"Constraint is not a contradiction"`. 3.0.2 shares **no substring** with it. Prose only — please widen the comment to name both wordings, as `ne.ml` and `test_random.ml` now do. Do not match on either alone anywhere | `lib/core/search.ml` | orchestrator | **CLOSED 2026-09-18, verified** — `search.ml:340-346` now names both wordings, gives 3.0.2's in full, says they share no substring, and points at `ne.ml` and `test_random.ml` as carrying the same pair. Done by an earlier session and never marked |
| **M1-T50, and a possible lead on M1-T44**: when the fact comes from a **decision**, `linear.ml` emits `pol <own row> <own row> +` — `Trivial` resolves to `ctx.model_id ()` at `justify.ml:288`, so the step derives twice the propagator's own row where the fact belongs. Confirmed by the orchestrator by reading `justify.ml:288` and `linear.ml:317,352`. **Worth checking against M1-T44's chain, which cancels to `0 >= 0`** — a citation that degenerates to the same row twice is exactly the shape that cancels. Do not treat this as a mandate to change `linear.ml` if your diagnosis says otherwise; it is a lead, not a conclusion | `lib/core/linear.ml`, `lib/core/justify.ml` | orchestrator | **CLOSED 2026-09-18 — obsolete, the code it describes is gone.** The lead was that `Explanation.Trivial` resolved to `ctx.model_id ()` and so made the `pol` derive the propagator's own row twice. `justify.ml:36` records that **M1-T31 deleted `Trivial`**, and it was its only user; `model_id` survives only in that file's history comments (`:28`, `:339`, `:360`), which state the old `pol <model_id>` shape was wrong and say what replaced it. Nothing left to investigate |
| **M1-T46**: same, at `test/unit/test_proof.ml:1125` and `:1150` — the second is an assertion *message*, so a reader who trips it gets told to look for a string 3.0.2 never prints | `test/unit/test_proof.ml` | orchestrator | **CLOSED 2026-09-18, verified** — `test_proof.ml:1485` tabulates both, and the assertion *message* at `:1518` (the half this request was really about, since a reader who trips it is told what to grep for) spells out both and says not to grep for one alone. `test_random.ml:726` matches both with an `||`. Done by an earlier session and never marked |
| **All `dune` files are orchestrator-owned.** `lib/core/dune` already has `(include_subdirs unqualified)` so a new `lib/core/prop/*.ml` needs no dune edit, and `test/unit/dune` already names `test_prop` and `test_justify`. Need another module named? Ask here | `**/dune` | orchestrator | standing |
| `lib/proof/encoding.ml` is now claimed by agent-encoding, and `lib/core/justify.ml` compiles against `Encoding.is_declared`: agent-encoding may **add** to encoding.ml but must not change the signature of anything already there | `lib/proof/encoding.ml` | orchestrator | standing |
| `lib/core/justify.ml`, `lib/core/explanation.ml`, `lib/core/prop/order_reason.ml` and `lib/proof/**` are **read-only** for both sessions this round: read them freely, edit none of them. Need a change? Write it here | — | orchestrator | standing |
| M1-T14 is split in two along a contract stated in full in the dispatch, not merely a type (the D-0009 lesson): agent-compile owns `lib/flatzinc/compile.ml` only; agent-output owns `lib/flatzinc/output.ml` and the `check_assignment` addition to `lib/flatzinc/model.ml` only. Neither touches `bin/main.ml`, any `dune` file, or the other's files; the orchestrator owns the wiring and the integration | `lib/flatzinc/**` | orchestrator | standing |
| M1-T7 is split across two sessions. The contract between them is the **existing** `Explanation.t` ADT in `lib/core/explanation.ml`, which neither may change: agent-core builds `Linear`/`Cut` values, agent-justify renders any of them. A change there is a cross-session request, not an edit | `lib/core/explanation.ml` | orchestrator | standing |
| **This round's split (D-0018).** agent-trace owns the trace vertical in `lib/core/`; agent-ne owns the direct encoding and `int_ne`; agent-mutate owns the mutation harness. The contract between agent-trace and agent-ne is that `Encoding` and `Lit` may only be **added** to — `Encoding.is_declared`, `Lit.ge/le/eq/ne/negate/to_string/owner` keep their current signatures, since `justify.ml` compiles against them | `lib/proof/encoding.ml`, `lib/proof/lit.ml` | orchestrator | standing, this round |
| **M6-T6 is done** (`bench/README.md` §3g, `WORKLOG.md` handoff above): please (1) mark M6-T6 `DONE` in `docs/ROADMAP.md`, and (2) update or remove `test/models/width_sat_depth.fzn`'s header comment ("at 99 it is 43 ms end to end") — it predates the regressing commit `aacbc8d` and is now off by ~7-14x depending on the flag. Both files are outside `bench/**`, which is all agent-bisect may touch | `docs/ROADMAP.md`, `test/models/width_sat_depth.fzn` | agent-bisect | standing |
| `lib/core/explanation.ml` is **frozen again** this round. D-0018's derivation needs no new constructor: `Combine`/`Weaken`/`Model_row` already express it, and the new work is *where and when* they are emitted, not what they say. If the trace genuinely cannot be said with the current ADT, that is a cross-session request and a decision record, not an edit | `lib/core/explanation.ml` | orchestrator | standing, this round |
| Each session builds into its own `--build-dir` (`dune build --build-dir=/tmp/baguette-build-<tag> <target>`). Three sessions share `_build/`'s global lock this round, so a bare `dune build` will fail for reasons that are not yours | — | orchestrator | standing, this round |
| Clarifying this round's split: `lib/core/prop/linear.ml` belongs to **agent-trace**, not agent-ne. A D-0018 trace line states `claim ∨ ¬(reason)` where the reason is the *other terms' current bound literals* — knowledge only the propagator has, and which `Explanation.t` deliberately does not carry in that shape (`Weaken` holds the declared-width chain the `pol` needs, which is a different projection). agent-ne owns `lib/core/prop/ne.ml` and no other file in `prop/` | `lib/core/prop/linear.ml` | orchestrator | standing, this round |
| **SPEC 2.2 never states the bool print rule.** It gives the line shape and the `----------` / `==========` / `=====UNSATISFIABLE=====` markers, but not that a bool MUST print as `false`/`true`, an int as a decimal, an array as `array<k>d(<ranges>, [...])`. M1-T21 found this: the rule lived only in `output.ml` and now in `test/expected/bool_out_sat.out`. The code is right by the FlatZinc standard; the spec is thin. agent-proof3 holds `docs/SPEC.md` this round — add the normative sentence, or hand it back | `docs/SPEC.md` | agent-output via orchestrator | CLOSED 2026-09-16 by orchestrator (SPEC 2.2 now states it) |
| M1-T16 runs alone: no other session is active, so agent-tests may add new files under `test/models/` and `test/expected/` (new files only — it must not edit an existing model, an existing expected output, or `PENDING`). Everything under `lib/` stays read-only: this task finds bugs and pins them, it does not fix them | `test/**` | orchestrator | standing, this round |
| **Hard coupling, no owner yet**: `Order_reason.weaken_declared` and `Encoding.expand_int_lin_le` perform the same substitution and must agree on the constant. If M1-T25 changes the row's shape, the weakening chain must change **in the same commit** or the justification stops matching the row it weakens. Both files are read-only for everyone right now, which is what makes this easy to miss | `lib/core/prop/order_reason.ml`, `lib/proof/encoding.ml` | agent-decisions via orchestrator | open |
| A width cap at compile time would naturally live in the same check as M1-T23's overflow cap, but it is **not** the same decision: a width cap refuses models the FlatZinc standard allows, so it needs its own SPEC change and decision record. Deliberately NOT folded into M1-T23 | `lib/flatzinc/compile.ml`, `docs/SPEC.md` | orchestrator | open |
| **Second wave, dispatched 2026-09-16 while M1-T23 is still running.** agent-overflow keeps `lib/core/prop/**`, `lib/flatzinc/compile.ml`, `test/unit/test_matrix.ml`, `test/unit/test_prop.ml` and any new `test/models/` file it names; the three new sessions were chosen precisely because none of them needs those. M1-T28 and M1-T31 are the two rows that ARE blocked on it, and are deliberately not dispatched | — | orchestrator | standing, this round |
| `scripts/mutate_proof.sh` passes from the orchestrator to **agent-mutate2** for M1-T26. The orchestrator's `pol-cite` half-open fix is already committed; build on it, do not revert it. Note the trap it cost: the awk program is inside a single-quoted shell string, so **one apostrophe in a comment breaks the script**, and the symptom is the control lanes going red rather than a syntax error you can read | `scripts/mutate_proof.sh` | orchestrator | standing, this round |
| agent-bench must prefix every model it adds `width_`, because agent-overflow is adding models to the same directory in a different worktree. Different filenames merge; the same filename does not | `test/models/**` | orchestrator | standing, this round |
| **MACHINE LIMIT: 15 GB RAM total, shared by every concurrent session.** On 2026-09-16 a `test_prop.exe` run reached **14.9 GB RSS** with 0 free and the box swapping; the orchestrator killed it. Cause is D-0028, not the test author: `Order_reason.weaken_declared` builds one literal per value across the **declared** width, per term, per pruning, even when nothing is pruned — so a test that declares a near-`max_int` domain tries to enumerate it. **No test may declare a wide domain.** Drive overflow through large *coefficients* against modest domains; a wide domain may only be used to assert that a compile-time cap **rejects** it, never to reach propagation or proof emission. Put `timeout` on anything that could allocate unboundedly | `test/**`, `bench/**` | orchestrator | standing, permanent |
| **Third wave, dispatched 2026-09-16 after M1-T23 released `lib/core/prop/**` and `compile.ml`.** agent-bool owns the Boolean vertical; agent-lazy owns the width vertical (`encoding.ml` + `order_reason.ml` + `linear.ml`). **M1-T31 is still NOT dispatched**: it needs `lib/core/search.ml`, which agent-fuzz holds for M2-T11. It goes out the moment agent-fuzz releases | — | orchestrator | standing, this round |
| M1-T32 is deliberately **not** dispatched with M1-T25 even though both concern `lib/proof/encoding.ml`: one adds a checked-arithmetic assertion, the other rewrites how atoms are declared, and they would collide line for line. M1-T32 follows M1-T25 | `lib/proof/encoding.ml` | orchestrator | open |
| M1-T25 changes `.opb` size by construction, which moves every number agent-bench is measuring for M3-T5. Not a file conflict; whichever lands second should re-run the benchmark rather than trust the other's figures | `bench/**` | orchestrator | open |
| `docs/PROOF-FORMAT.md` §5 says `drop-line`'s parse-error behaviour is a 3.0 quirk. **It is not** — under 2.0 it fails as a dead-id error, measured message `Accessing the database out of bound with index 3`. D-0023 got the same Status-line correction from the orchestrator; PROOF-FORMAT is agent-lazy's this round, so it is a request rather than an edit. See D-0030 | `docs/PROOF-FORMAT.md` | agent-mutate2 via orchestrator | open |
| **Three sessions were stopped mid-task on 2026-09-16 by a bug on the user's side, not by anything they did.** Their worktrees survived and the orchestrator salvaged them: agent-fuzz's branch was verified green (952 checks, 15/15) and **merged**; agent-bool's WIP was committed on its own branch `worktree-agent-a5a5eb6cbb5505ceb` as `97d982e`, explicitly marked DOES NOT BUILD and deliberately not merged; agent-lazy had touched no project file. Successor sessions continue each | — | orchestrator | standing, this round |
| M2-T11's **code** is merged but its **evidence is not**: the byte-identity check across the model suite was never reported, and the suite has since grown from 15 models to 20. Treat "the 20 models are unchanged by seeded branching" as unverified until agent-fuzz2 reports hashes. The gate passing is necessary but not sufficient — it would not catch a proof that changed yet still verifies | `test/models/**` | orchestrator | **CLOSED 2026-09-18 as superseded, with the residue named.** The concern as written is answered **structurally**, not by a hash run: `grep -rn '~order\|random_order' bin/ lib/` returns **nothing outside `lib/core/search.ml`**, and `Search.solve` takes `?(order = spec_order)` (`search.ml:775`). The CLI cannot select a random order at all, so no model artefact can depend on `random_order` by construction — a stronger argument than the hash comparison asked for, and one that does not decay as the suite grows. **What it does NOT establish**: that M2-T11's *refactor* of `solve` left the default tree byte-identical when it merged. That was partially evidenced at the time (`3cdd122` records the pinned instance as "byte-identical under the pre-M2-T11 `search.ml`") and is now unfalsifiable in place, nine waves of legitimate artefact changes later. What covers it going forward is M2-T12's determinism gate (34/34 byte-identical across two runs of one binary, self-tested) and wave nine's 120-seed sweep (~192,000 runs, zero rejections). **Do not dispatch a rebuild-and-compare for this** |
| **M2-T1/M2-T2 is half done and the green suite is misleading.** The branch builds and passes 1051 unit checks / 20 models, but **nothing exercises the new Boolean propagators** — all 19 bool-mentioning checks predate the work, and no `bool_clause`/`array_bool_or`/`array_bool_and`/`bool2int`/`bool_not` model or unit test exists. It is green because the new code never runs (D-0030's failure mode). **Do not merge it as done.** The remaining work is the tests and models, i.e. the half that matters | `test/**` | orchestrator | open |
| **The model suite cannot see the trail-scan direction, one layer below where M1-T24 found the same blindness.** With `linear.ml`'s walk deliberately reversed, all 60 model artefacts stay byte-identical and 20/20 models pass; only the unit suite goes red. So byte-identity is evidence of *no change*, never of *correctness*. Relevant to M2-T5/M2-T6, which both alter wake and reason selection | `test/models/**` | agent-lazy2 via orchestrator | open |
| **`test/unit/dune` is lent to agent-interval for exactly one line this round.** Normally orchestrator-owned. The reason is a mistake I made today: I added a `test_interval` stanza before the module existed and broke the gate for one run. A dune stanza and the file it names must land in the same commit | `test/unit/dune` | orchestrator | standing, this round |
| **M1-T32 has an architectural catch.** `Checked` lives in `lib/core`, and `lib/core` depends on `lib/proof`, not the other way round (ARCHITECTURE §1, "Dependency direction"). So `encoding.ml` **cannot** call `Baguette_core.Checked`. Inverting the dependency is not an option; the agent must choose another route and say which | `lib/proof/encoding.ml` | orchestrator | standing, this round |
| Two sessions on this task have now been interrupted — one by a user-side bug, one by an API session limit at 14:32 BST (resets 14:50). Each was salvaged to its own branch rather than restarted: `97d982e` (did not build) then `dc0b162`/`064a372` (builds). The lesson for whoever picks it up: **commit as soon as it compiles**, because this task has lost two working periods to things that had nothing to do with the code | — | orchestrator | standing |
| `test/unit/test_matrix.ml`'s empty-cell note (line ~1192) is stale: it says four `int_ne` cells (|a| > 1, common factor, offset domains, negative domains) are left unfilled because "every disequality pruning that moves a bound **currently** emits a factless trace line". M1-T17 fixed that and inverted `known_bug_ne_trace_facts` itself, so the stated reason no longer holds and those cells are fillable. Not touched here — M1-T11 claimed neither the matrix nor `lib/` | `test/unit/test_matrix.ml` | agent-ne-wiring | open |
| **Round of 2026-09-16, four sessions, disjoint file sets.** agent-delrange owns the writer's deletion vertical; agent-overflow owns the arithmetic vertical in `lib/core/prop/` and `compile.ml`; agent-trailcursor owns `lib/core/engine.ml`; agent-decisions is doc-only in `docs/DECISIONS.md`. No file appears in two columns | — | orchestrator | standing, this round |
| `WORKLOG.md`, `docs/ROADMAP.md`, `Makefile`, `dune-project`, `scripts/**` and **every `dune` file** are orchestrator-held this round. `lib/core/dune` has no `modules` field, so a new `lib/core/checked.ml` or `lib/core/prop/*.ml` needs no dune edit; a new *test executable* does, and that is a request here, not an edit | `**/dune` | orchestrator | standing, this round |
| `lib/core/explanation.ml`, `lib/core/justify.ml`, `lib/core/store.ml`, `lib/core/trace.ml`, `lib/proof/encoding.ml` and `lib/proof/lit.ml` are **read-only for all four sessions**. M1-T24 in particular is a pure rewrite of `Engine.propagate` over the `Store.trail_entry` API that already exists — if it looks like `store.ml` needs a new accessor, that is a request here | — | orchestrator | standing, this round |
| Each session works in its own git worktree under `.claude/worktrees/`. Build with `dune build --root .` and `dune runtest --root .` from inside it — a bare `dune build` or `make` fails there with "Don't know about directory", and a `--build-dir` outside the checkout breaks the model and mutation suites. See CLAUDE.md | — | orchestrator | standing, this round |
| M1-T22 changes emitted proof *text* for 5 of 14 models; M1-T23 adds models. Neither may edit the other's expected outputs, and neither may edit an existing `test/expected/*.out` to make a suite pass — a model whose **solution** changes because of a deletion fix is a bug report, not an expected-output edit | `test/expected/**` | orchestrator | standing, this round |
| **Both wave-eight sessions were interrupted by a session-end, not by anything they did. Salvaged, and the two outcomes differ sharply.** agent-del had **committed** its work (e7cfcfe: 1500 ok, 0 FAIL, 34/34 models) and is merged; the change left uncommitted on top was its deliberate **break** — it removes the trailing `del id`, leaving `@c<hi>` live, and reddens exactly the three checks that assert the pair — parked at `474a05f`, not merged. agent-iface had committed **nothing** after a long run, so its entire M2-T8 refactor was uncommitted; salvaged to `7e450db` on `wave8-iface`, marked **DOES NOT BUILD** (one error at `linear.ml:501`, a call site not yet moved onto the new type). **This is the case CLAUDE.md's "commit as soon as it compiles" exists for, and it is now the third session to pay it** | — | orchestrator | standing |
| **`lib/core` is FREE again, and five M1 rows plus M2-T9/M2-T3 unblock with it.** M2-T8 is merged. Before starting M2-T3, read **I-S4** (a cited hole line must outlive the line citing it — the level-discipline argument does **not** cover a learned clause citing across levels) and **D-0038**, which agent-iface recommends be resolved in `reason.ml` rather than `explanation.ml`: `Reason.fact` *is* the conclusion type, so a `justified` could carry `concludes : fact option` and let `Justify` use `Writer.pol_concluding` | `lib/core/**` | orchestrator | open |
| **Two blind spots M2-T8 measured rather than inherited.** (1) `explain_cross_conflict` still violates I-X6 and **breaking it reddens nothing** — the function is reached (proved by replacing it with `failwith`, which reddens `test_matrix`), but search forces conflict explanations immediately so the staleness never shows. M2-T3 is where it stops being harmless. (2) The agreement check catches a reason naming the **wrong variable**, not one naming the right variable at the **wrong value**; that needs D-0038's conclusion | `lib/core/**` | agent-iface via orchestrator | open, for M2-T3 |
| **Wave nine, dispatched 2026-09-17. Three sessions, and the shape is chosen to give M2-T3 a clean exclusive run next.** M2-T3 needs all of `lib/core` and D-0011's lesson was that its preconditions must be closed **before** it starts, not during. So this round closes the three things M2-T3 would otherwise trip over — the M2-T9 index it depends on, I-S4's unchecked argument, and `explain_cross_conflict`'s I-X6 blind spot — and sweeps the small M1 rows out of `lib/core` at the same time. **M2-T3 is deliberately NOT dispatched this round** | — | orchestrator | standing, this round |
| **File map, disjoint by construction**: `justify.ml`+`trace.ml` = agent-index; `prop/linear.ml` = agent-linear; `search.ml`+`bin/main.ml`+`bench/` = agent-search4; `store.ml`+`docs/**`+`WORKLOG.md`+`scripts/**` = orchestrator. `lib/core/reason.ml` and `lib/core/explanation.ml` are **read-only for all three** — M2-T8 landed them hours ago and a second reshape this round would be churn. `lib/proof/**` is read-only for all three. `test_core.ml`, `test_matrix.ml` and `test_random.ml` are unowned: if your change breaks one, that is a request to me, not an edit | — | orchestrator | standing, this round |
| **Request for agent-index, from agent-linear (M1-T63's remaining half).** `trace.ml:295-308`'s `remover` header duplicates what `store.ml:543-551` now says, but does **not** name `reject_set_domain` — it says only that SPEC 2.1 "does not admit" a set domain. Either point it at `Store.remover` or name the gate, so the two cannot drift. Small, prose only | `lib/core/trace.ml` | agent-linear via orchestrator | open, for agent-index |
| **D-0038 is RESOLVED as D-0043** (2026-09-17). The conclusion is a `Reason.fact` carried on `justified`, in `reason.ml`, not `explanation.ml`. **Two unrelated consumers needed the same missing value**, which is what decided it: M2-T8 found `Reason.fact` already *is* a bound claim, and M2-T9 found its index cannot key a `pol` at all because a `pol`'s content is computed by the checker — so the conclusion is exactly that key, and also exactly what `pol_concluding ~claim` wants. **Not a precondition of M2-T3 and must not be folded into it**; it pairs with M2-T9's follow-up and with M4-T1, which D-0040 requires to emit a `pol` ahead of its trace line | `docs/DECISIONS.md` | orchestrator | CLOSED |
| **Wave eight, dispatched 2026-09-17. Same shape as wave seven and for the same reason**: M2-T8 rewrites the propagator interface, so it needs all of `lib/core`. agent-del works in `lib/proof` only; the orchestrator holds `Makefile` and `scripts/**`. **M2-T3 is still not dispatched** — M2-T8 is its precondition and M2-T9 follows M2-T8 | — | orchestrator | standing, this round |
| **`lib/proof/writer.ml` is agent-del's and `lib/core/justify.ml` is agent-iface's, and they meet at the rule-emission boundary.** agent-del may **add** to `writer.ml` but must not change the signature of `pol`, `rup`, `rup_clause`, `implied`, `pol_concluding`, `fresh`, `delete`, `delete_many`, `wipe_level` or `del_run`, because `justify.ml` compiles against them and agent-iface is rewriting that file. A change there is a request here | `lib/proof/writer.ml` | orchestrator | standing, this round |
| **Wave seven, dispatched 2026-09-17. Three sessions, and the split is dictated by M2-T7's footprint.** M2-T7 threads the propagator instance id onto the trail and onto `Conflict`, which reaches ~110 call sites across seven test files and nearly every module in `lib/core`. So agent-instid gets **all of `lib/core`**, and the only parallel work is outside it: agent-widthcap in `lib/proof` + `lib/flatzinc`, and agent-property read-only. Do not add a fourth session in `lib/core` this round | — | orchestrator | standing, this round |
| **M1-T58 landed mid-round (bf9c84c), so agent-widthcap's dependency is gone.** Its brief said a row refused at `Encoding`'s door would surface as an uncaught exception; it now gets a positioned diagnostic and exit 4. If the report still says "uncaught exception pending M1-T58", that is stale and the orchestrator's fault for dispatching before fixing it, not the agent's | `bin/main.ml` | orchestrator | CLOSED |
| **I-X10 and D-0040 landed mid-round and they bear on `lib/core/prop/`, which agent-instid holds.** Nothing to change for M2-T7 — I-X10 is about what the checker accepts, not about the trail — but **read D-0040 before M4**, and note M1-T62: `Store.remove` and `Store.fix` are live, exported, have **no `lib` callers**, and silently record `no_facts`, which is the I-P5 violation that caused a real bug at M1-T17. **[STALE — do not brief from this row. M2-T8 killed both halves of the premise; see the wave-nine handoff note "Two of the three premises I dispatched were wrong". `no_facts` no longer exists in `store.ml` and `remove`/`fix` both take a `Reason.justified` through `apply` (`store.ml:560-561`). The orchestrator read this row and put the dead claim into a wave-ten brief on 2026-09-18; agent-cut caught it.]** If M2-T7's threading gives you a natural moment to make `no_facts` unreachable from `lib/`, take it and say so; if not, leave it — the tests use `Store.remove` deliberately to construct the factless case they assert against, so deleting it is not obviously right | `lib/core/store.ml` | orchestrator | open, for agent-instid to consider |
| **The M1-T25 coupling stayed quiet, as hoped.** Neither agent-instid nor agent-widthcap touched the `Order_reason.weaken_declared` / `Encoding.expand_int_lin_le` substitution, and all 102 proof artefacts are byte-identical across both merges. Closing this for the round; re-open it the moment anyone changes the row's shape | `lib/core/prop/order_reason.ml`, `lib/proof/encoding.ml` | orchestrator | CLOSED for wave seven |
| **I-S4 is still unchecked, and M2-T7 did not change that.** agent-instid confirmed it added no cross-level assertion: `entry.prop` supplies the material for one, but the missing check is about **levels**, not identity, and `Trace` already has `Store.level_of_index`. **Whoever takes M2-T3 owes this check** — a learned clause citing across levels is exactly the case I-S4's level-discipline argument does not cover | `lib/core/**` | orchestrator | open, for M2-T3 |
| **Wave ten, dispatched 2026-09-18. Three sessions, and the split is chosen so the learning sequence starts without two sessions inside the same types.** M2-L0 is a wide-but-shallow change to `Reason.justified` reaching 13 `Reason.because` call sites in `lib/` and 46 in `test/`; M2-L2 is purely additive (one new module, one new test file) and *reads* reasons without constructing them; M2-T13 is one test file. **M2-L1 is deliberately NOT dispatched**: it would write a new `lib/core/learned.ml` against the very `justified` shape M2-L0 is changing, and the two would merge textually clean and fail to build — the exact break wave eight paid for. It goes out the moment M2-L0 lands | — | orchestrator | standing, this round |
| **Routed from M2-T14, for whoever next owns `bin/`**: `bin/main.ml:502` writes the `.opb` with bare `Encoding.write_opb`, **before the writer exists** (I-X5 requires the `.opb` be complete first). It is **correct today** — both sides read `Writer.default_format ()`, so they agree — but they agree **by convention rather than by construction**, and that is precisely the shape of every defect M2-T14 found: two artefacts deciding their format independently. `Encoding.write_opb_for` ties them together, but needs the writer. Not urgent, not a bug today; worth closing the moment `bin/main.ml` is open for another reason. agent-fmt2 could not touch it (`bin/` was not its) and audited every other call site clean: `lib/proof/**` needs **nothing** | `bin/main.ml` | agent-fmt2 via orchestrator | open |
| **The contract between agent-concl and agent-cut.** agent-concl may **add** to `Reason` but must not change the signature of `Reason.owners`, `Reason.lits`, `Reason.fact_owner`, `Reason.fact_is_lower`, `Reason.at_least`, `Reason.at_most`, nor of `Store.conflict`, `Store.lo_support`, `Store.hi_support`, or the `entry.prop` field — agent-cut's cut walker compiles against exactly those. agent-cut must **not construct `Reason.justified` values directly**: drive every scene through a propagator or the engine, so that a field added to that record cannot break it | `lib/core/reason.ml`, `lib/core/store.ml` | orchestrator | standing, this round |
| **`test/unit/dune` is lent to agent-cut for exactly one line** (`test_analysis`), and to no one else. The stanza and the file it names **land in the same commit** — a dune stanza naming a module that does not exist yet broke the gate for a run last week. `lib/core/dune` needs no edit at all: it has `(include_subdirs unqualified)` and no `modules` field, so a new `lib/core/analysis.ml` is picked up automatically | `test/unit/dune`, `lib/core/dune` | orchestrator | standing, this round |
| `lib/core/explanation.ml`, `lib/core/engine.ml`, `lib/core/search.ml`, `lib/core/store.ml`, `lib/core/trace.ml` and all of `lib/proof/**` and `lib/flatzinc/**` are **read-only for all three sessions this round**. M2-L0 needs none of them (D-0043 puts the conclusion in `reason.ml` precisely to avoid `explanation.ml`), and M2-L2 learns nothing and backjumps nowhere, so it needs no mutator. Need a change? Write it here | — | orchestrator | standing, this round |
| **Baseline for wave ten, measured on `6761435` before dispatch**: `make check` green — **1625 unit checks**, 252 matrix checks, 44 mutation checks, 34/34 models, determinism green across two runs. Beat it or explain it. Note the gate **silently skips the formatting check if `ocamlformat` is not on PATH** and still says `check: ok`; run `eval "$(~/.local/bin/opam env --switch=baguette)"` first or you are verifying less than you think | — | orchestrator | standing, this round |
| **Correction to my own wave-ten dispatch, made minutes after it.** I listed `lib/core/search.ml` and `lib/core/store.ml` read-only for agent-concl, but both hold `Reason.because` call sites (search.ml 2, store.ml 1), so a **required** conclusion field cannot compile without them. **Both are agent-concl's this round**; agent-cut only reads them. The frozen signatures still hold and are now load-bearing: `Store.conflict` and its `c_prop`/`c_why`/`c_reason`, `Store.lo_support`, `Store.hi_support`, `entry.prop`, `Store.level_of_index`. search.ml's two sites are search *decisions* and are the **positive half of M2-L0's partition test** — a decision concludes nothing (D-0037) — not boilerplate | `lib/core/search.ml`, `lib/core/store.ml` | orchestrator | CLOSED, amended in flight |
| **D-0045 (M2-L9, restarts) turned up a finding that does not wait for its verdict, and it constrains M2-L1/L3/L4.** `Writer.wipe_level l` (`lib/proof/writer.ml:764`) deletes every id **tagged at level `>= l`**. A learned constraint exists to outlive the conflict that produced it, so **a learned constraint tagged at the level it was learned at is deleted by the very backjump that follows learning it** — it must be a level-0 object. M2-L3's row already says "attach at the backjump level, not the level being retired"; this is *why*. For M2-L4 it is sharper: if the retention policy and `wipe_level` both own the constraint's lifetime they will double-delete and break **I-X2**, which is exactly M2-L4's test (a). Decide who owns that lifetime before writing the policy. **Sharpened the same day, see D-0045's addendum**: `Writer.fresh` (`writer.ml:547`) tags every id with the writer's *current* level with **no override**, and `set_level` is the only lever — so this is automatic, not a risk. It collides head-on with M2-L3's own rule to emit the derivation *while its supports are still live*: that means emitting before the wipe, which is precisely what tags it for deletion. **M2-L1 probably owes `lib/proof/writer.ml` a new entry point** (an id allocated at a chosen level), and it must hold under **both** formats — 2.0 does not maintain `t.tags` at all, so a 3.0-only fix would be green and wrong | `lib/proof/writer.ml`, `lib/core/**` | orchestrator | open, for M2-L1/L3/L4 |
| `docs/PROOF-FORMAT.md` §5 `drop-line` — the request to correct the "3.0 quirk" claim. **Verified closed 2026-09-18**: §5's heading now reads *"fails on the grammar in BOTH formats (corrected — D-0030)"* and tabulates both checkers' words, and D-0023's Status line carries the correction too. Nothing left to do; closing the row so the next orchestrator does not re-check it | `docs/PROOF-FORMAT.md` | agent-mutate2 via orchestrator | CLOSED 2026-09-18 |
| **The checkout's branch `master` was renamed to `main` on 2026-09-18, mid-wave, and not by me.** Caught when `git branch --merged master` started failing with *"malformed object name"*; `git reflog` names it at `HEAD@{2}`, between the wave-ten claim commit and my next one. **Nothing was lost**: `62962b8` is still an ancestor of `main`, all three `wave10-*` branches are intact, and the two deliberately-preserved unmerged commits (`474a05f` on `wave8-del`, `97d982e` on `worktree-agent-a5a5eb6cbb5505ceb`) are both still unmerged and still reachable. Upstream was already `origin/main`, so the rename aligns the local name with it and I have **left it as `main`**. What it costs: **`master` no longer resolves**, so `git merge master` / `git diff master` / `git log master..` now fail with "unknown revision" — in CLAUDE.md, in older WORKLOG rows, and in any habit you have. All three wave-ten sessions were told. The real lesson is the one the rename itself illustrates: **a ref operation in a checkout shared by four sessions is not a local act**, and it belongs in a claim like any other edit | — | orchestrator | standing, permanent |
| **The M1-T25 coupling now has owners on both sides, and they are different sessions.** `Order_reason.weaken_declared` (`lib/core/prop/order_reason.ml`, agent-instid) and `Encoding.expand_int_lin_le` (`lib/proof/encoding.ml`, agent-widthcap) perform the same substitution and **must agree on the constant**. A width cap should not change the row's shape, so this should stay quiet — but if either of you finds yourself changing that substitution, say so here **before** committing, because the two halves must move in one commit or the justification stops matching the row it weakens | `lib/core/prop/order_reason.ml`, `lib/proof/encoding.ml` | orchestrator | open, this round |
| **M2-T8 and M2-T9 are deliberately NOT dispatched, and M2-T3 is not either.** The chain is strict: M2-T7 -> M2-T8 -> M2-T9 -> M2-T3, and M2-T7's own row says it 'should be closed before M2-T3 starts, not during it'. M1-T36, M1-T58 and M1-T59 are also held: all three want files in agent-instid's set. They go out next wave | — | orchestrator | open, wave eight |
| **Whoever takes M2-T3 must read I-S4 first.** D-0039 made a settle trace line RUP *in sequence* rather than standalone, so a cited hole line must outlive the line citing it. That holds today by an argument about the level discipline which **does not cover a learned clause citing across levels** — exactly what 1UIP produces | `lib/core/**` | orchestrator | open, for M2-T3 |
| **Wave six, dispatched 2026-09-17, five sessions, disjoint file sets.** agent-trace3 owns the trace-honesty vertical; agent-search3 owns `lib/core/search.ml`; agent-polcheck owns the writer's conclusion-checking vertical; agent-testhyg owns the test-tree hygiene; agent-cli owns the CLI/report honesty. No file appears in two columns — check the claims table before assuming otherwise | — | orchestrator | standing, this round |
| `lib/core/explanation.ml`, `lib/core/justify.ml`, `lib/proof/encoding.ml`, `lib/proof/lit.ml`, `lib/proof/opb.ml` and `lib/core/prop/**` are **read-only for all five sessions** this round. Read them freely, edit none. Need a change? Write it here and work on something else | — | orchestrator | standing, this round |
| `lib/core/store.ml` is lent to **agent-trace3 alone**, and **add-only**: it may add an accessor or widen a record with a new field, but must not change the signature of anything already there, because `search.ml` (agent-search3) and every propagator compile against it. If M1-T57 needs the propagator's *claimed* bound carried on the trail entry and that cannot be done additively, that is a request here and a decision record, not an edit | `lib/core/store.ml` | orchestrator | standing, this round |
| `WORKLOG.md`, `docs/**`, `docs/ROADMAP.md`, `Makefile`, `dune-project`, `scripts/**` (except `run_model_tests.sh`, lent to agent-cli) and **every `dune` file** (except `test/unit/dune`, lent to agent-testhyg) are orchestrator-held. All merging and all committing to `master` is the orchestrator's; agents commit on their own `wave6-<tag>` branch | — | orchestrator | standing, this round |
| **M1-T55 and M1-T56 are two sides of one fact and are deliberately in different files.** `search.ml:191-193` says a decision at a hole puts a bound on the trail strictly stronger than the literal its nogood negates, *and* that an interior hole gets no trace line because `Trace.claims` writes one only when a bound moves. `trace.ml:154` is the other end of that same sentence. agent-search3 owns the branching side, agent-trace3 owns the trace side. **Neither may fix the other's end**, and if one of you concludes the real fix lives in the other's file, say so here rather than reaching across | `lib/core/search.ml`, `lib/core/trace.ml` | orchestrator | open, this round |
| **New model filename prefixes are reserved this round**, because two sessions add models to the same directory in different worktrees: agent-trace3 uses `trace_`, agent-search3 uses `decide_`. Different filenames merge; the same filename does not | `test/models/**` | orchestrator | standing, this round |
| **CLOSED 2026-09-17 by the orchestrator (gate log, wave-six baseline).** `test/unit/test_matrix.ml`'s empty-cell note is no longer stale: the gate prints "int_ne / int_lin_ne x the offset and negative-domain shapes: FILLED as of M1-T20", and `int_ne/negative-domain` + `int_lin_ne/coprime-negative` fill them, each confirmed to fail with the M1-T17 fix reverted. 252 matrix checks, all passing | `test/unit/test_matrix.ml` | agent-ne-wiring, closed by orchestrator | CLOSED |
| **M2-T1/M2-T2's "green because the new code never runs" concern is CLOSED 2026-09-17.** The suite now has ten Boolean models — `bool_and_sat`, `bool_array_sat`, `bool_channel_sat`, `bool_channel_unsat`, `bool_clause_sat`, `bool_eq_sat`, `bool_not_sat`, `bool_or_sat`, `bool_out_sat`, `bool_reif_unsat` — all passing under the wave-six baseline, and `test_prop.ml` has 291 bool-mentioning lines. The half that mattered landed | `test/**` | orchestrator | CLOSED |
| **M2-T11's evidence is STILL open and the orchestrator has not closed it.** The byte-identity check across the model suite under seeded branching was never reported; the suite has now grown from 15 to **30** models, so the unreported figure is staler still. The wave-six gate passing is necessary and not sufficient — it would not catch a proof that changed yet still verifies. Not dispatched this round; whoever takes it reports hashes, not a verdict | `test/models/**` | orchestrator | open |
| **CORRECTION 2026-09-17: the row above me has a false premise, and I wrote it.** M2-T11's evidence *was* reported — its roadmap row states 60/60 artefacts byte-identical with a control that moved 19 artefacts and broke 6 models. What is actually wrong is that it was a **one-off session measurement and not a committed check**, so nothing reproduces it and the suite has since grown 20 -> 30 models. Measured today at 39cd0d5: the default path is deterministic (90/90 artefacts byte-identical across two runs, manifest digest `6fcd0415`), and `random_order` is not CLI-reachable, so the harness must live in a test binary. Re-scoped as **M2-T12**, not closed | `test/models/**` | orchestrator | superseded by M2-T12 |
| **M1-T48's other half, left open deliberately.** The usage text is honest now, but `--proof-comments` still switches a mechanism nothing reachable calls. Making it annotate the proof with the step that produced each rule needs `Writer.comment` wired into `lib/core/justify.ml` and the propagators — out of agent-cli's file set this round, and arguably M4's job rather than M1's. The tripwire's end-to-end half is **prospective, not a live control**: it compares `.pbp` bytes with and without the flag, which cannot differ until a reachable path emits a comment. Whoever lands M4's direct encoding should expect it to go red and should treat that as the signal to revisit the usage text | `lib/core/justify.ml`, `lib/proof/encoding.ml`, `bin/main.ml` | agent-cli via orchestrator | open, for M4 |
| **One line each, for the three sessions holding a test file.** `Mem_guard.install ()` is now armed in twelve of fifteen test binaries. `test_engine.ml` (agent-search3), `test_proof.ml` (agent-polcheck) and `test_trace.ml` (agent-trace3) are the three left, because you hold them. Add `let () = Mem_guard.install ()` after your module aliases — no `dune` change is needed, the helper is already linked. **The orchestrator will add it at merge time if you would rather not**, so this is not a blocker. Verify with `BAGUETTE_TEST_HEAP_CAP_ANNOUNCE=1 ./_build/default/test/unit/<b>.exe`; a binary that prints no `mem_guard: armed` line has not called it | `test/unit/test_engine.ml`, `test/unit/test_proof.ml`, `test/unit/test_trace.ml` | orchestrator | open, this round |
| **D-0038 is open and it is the gate on M1-T51's adoption**, not a formality. `Writer.pol_concluding` exists, is demonstrated against the checker, and has **no caller in `lib/`**, because `Explanation.Combine`/`Cut` record how a bound was derived and not what was derived — there is no claim to pass. Four routes are written down in the record; route 3 folds it into **M2-T8**'s interface v2, where D-0026 already separates `Reason` from `Justification`, and is the only one that does not pre-empt D-0003. **Do not adopt `ia` piecemeal without deciding this** — a control with holes invites the assumption that it has none | `lib/core/explanation.ml`, `lib/core/justify.ml` | orchestrator via agent-polcheck | open, needs D-0038 |
| **RESOLVED 2026-09-17, not a defect.** agent-search3 flagged `del id @c17 @c18 @c19 ;` followed by `del range @c14 @c17 ;` — `@c17` in both — as worth a glance from whoever owns `writer.ml`. It is correct: `del range` is **half-open**, `[LO, HI)`, as M1-T22 measured and PROOF-FORMAT §5 records, so the range stops at `@c16` and `@c17` is deleted exactly once. The appearance is consecutive ranges *chaining* on a shared bound, visible in `width_sat_depth`'s six ranges. I scanned all 34 proofs modelling half-openness: **zero overlapping deletion targets**. Right to flag, and the glance closes it | `lib/proof/writer.ml` | agent-search3, closed by orchestrator | CLOSED |
| **M1-T36 is deliberately NOT dispatched in wave six.** A real node counter needs `lib/core/search.ml` (agent-search3) *and* `bin/main.ml` + `bench/run_bench.sh` (agent-cli) in one commit, and splitting it across two sessions would repeat the D-0009 mistake for a row the roadmap itself calls "Small". It goes out whole in wave seven, when both files are free | `lib/core/search.ml`, `bin/main.ml` | orchestrator | open, wave seven |
| **`Makefile`'s `bench` comment offers a flag that no longer exists.** Line 106 documents `make bench ARGS="-F 2.0"`; D-0046 removed format 2.0 and M2-L8 removed `-F` from `bench/run_bench.sh`, so that example now fails with a usage error. The target body itself is fine. `Makefile` is not `bench/`'s to edit, so this is a one-line request rather than a commit. While there: the same comment says "fifteen of the eighteen rows are at the process floor" — the suite is **38** models now, and the re-measured figure is **23 of 38 at 90%+ `notslv%`** | `Makefile` | agent-bench | **CLOSED 2026-09-18, verified** — line 106 already reads `ARGS="-r 9"` and `23 of the 38 rows`; it landed with the wave-fifteen merge and was never marked |

| **Explanation review, external (`docs/EXPLANATION-REVIEW.md`)** — a session on `~/Explanations-by-constraint-decomposition` read `lib/core/` against the *explanation* literature (LCG explaining propagators, step-wise explanations, proof logging) and wrote a report-only doc, same footing as `GCS-COMPARISON.md`. **No code, roadmap or decision change was made**, and no `lib/` file was touched. Six warnings, each scoped to a file or a row; the five below route them to their sites. Two findings from its draft were **withdrawn** after checking the roadmap (M1-T23 overflow, M1-T25 width — both DONE); they are named in the doc so nobody resurrects them from `GCS-COMPARISON.md`, which predates both | `docs/EXPLANATION-REVIEW.md` | agent-xreview | open |
| **`concludes` must not become optional.** D-0043's required-field-with-optional-value spelling is the single thing in this tree the explanation literature has no counterpart for: nothing in GCS or the proof-logging papers checks that a derivation *concludes what the propagator claimed*. It costs 13 call sites in `lib/` and 46 in `test/` and it looks like ceremony, so a future session will propose a defaulted `?concludes` — the move D-0026 already reversed once. Please add a line to `reason.ml`'s header saying the relaxation needs a decision record arguing the point, so the argument does not have to be rediscovered | `lib/core/reason.ml` | agent-xreview | **ROUTED 2026-09-18** to agent-ladder (wave sixteen), which holds all of `lib/` |
| **Do not reintroduce literal counting in the PB stopping criterion.** `assertive_slack` is stated in slack precisely because Le Berre et al. show assertiveness gives no backjump guarantee over PB. A later optimisation that counts conflict-level literals because it is cheaper or "matches the SAT solver" reintroduces the bug the citation prevents, and it does **not** surface as a wrong answer — it surfaces as worse backjumps, which nothing here measures. Worth one explicit sentence at `assertive_slack` | `lib/core/pb_analysis.ml` | agent-xreview | **ROUTED 2026-09-18** to agent-ladder (wave sixteen), which holds all of `lib/` |
| **D-0003's (a)-claim needs closing by an argument, not a profiler.** `GCS-COMPARISON.md` §6 says "nobody has yet said what the reified form buys" and reads that as evidence against. That holds only if explanations are a solver internal. The literature answer: a closure cannot be printed, diffed, compared against a published explanation, lifted into a schema or shipped — a reified `Combine` can, and every use of explanations *outside* conflict analysis needs them as data (GCS reified theirs too, at a different boundary). So retiring `Deferred`/`Combine` on runtime grounds is only sound if the project has *also* decided explanations are not a research output. Those two decisions are coupled and the coupling is unrecorded. §2 of the review states it in full | `lib/core/explanation.ml`, `docs/DECISIONS.md` | agent-xreview | **CLOSED 2026-09-18 — raised as D-0048**, open question with no verdict, per D-0045's pattern. Also cross-referenced on M4-T1, which is where it stops being abstract |
| **M2-L6's negative result is a prediction and should be recorded as one.** The finding — our integer propagator is stronger than PB propagation on the same row, because the ladder implications live in separate `.opb` rows — predicts that PB learning keeps producing degenerate rows *for as long as a reason is the model row without its ladder chain*. It currently lives in one commit message and one module header, so whoever takes M2-L7 can reasonably re-run the experiment and re-derive the same negative. A `DECISIONS.md` record with a falsifier would let the next attempt start from "carry the ladder rows into the reason" instead of from zero | `docs/DECISIONS.md` | agent-xreview | **CLOSED 2026-09-18 — raised as D-0047**, with the falsifier named. Written *before* M2-L11 reported, so it is a prediction and not a postdiction |
| **No roadmap row asserts anything about explanation *quality*.** M2-T10 proposes per-node consistency checking for propagator *strength*; the explanation-side sibling does not exist. The literature's whole quality metric is generality — a shorter, weaker-premised explanation prunes more later, which is why Schutt's window beats naming every task and why Downing compares three `alldifferent` propagators. **A sound but maximally weak explanation, naming every variable in scope, passes every test in this repo today and VeriPB accepts it.** Harmless while every propagator is linear and the derivation is forced; not harmless at M4-T1, where the *choice* of Hall set is the whole game. Suggest a row — even just recording explanation size per model so a regression is visible — landing **before** M4-T1 | `docs/ROADMAP.md` | agent-xreview | **CLOSED 2026-09-18 — became M2-T17**, dispatched this wave as agent-size. Scoped to `bench/` and to artefacts that already exist, so it needed no `lib/` change and could run beside the M2L sequence |
| **M4-T1 is an experiment, not "another propagator."** It is the first derivation that actually needs `Combine`/`Weaken`/`Model_row`: a Hall justification cites many model rows in one tree. Everything green today is linear rows and clauses — the case nobody doubted. The design anticipates Hall (that is why `Model_row` exists); anticipation is not evidence. Suggest the row carry that framing so it is budgeted as the test of the project's central claim rather than as propagator number eight | `docs/ROADMAP.md` | agent-xreview | **CLOSED 2026-09-18** — the framing is now on the M4-T1 row itself, where it will be read, together with D-0048 |

| **Wave 26 RECIPROCAL GRANTS — two branches touched each other's files, deliberately.** `bin/main.ml` is agent-unlimit's; agent-annot has **two lines only** at `:741`/`:753` adding `?order:compiled.Compile.order` to the `Search.solve`/`Search.optimise` calls. `lib/flatzinc/compile.ml` and `test/unit/test_flatzinc.ml` are agent-annot's; agent-unlimit has **`compile.ml:366`** (print the live width limit, not the stale constant) and **the `(* === the width cap === *)` block** of `test_flatzinc.ml` (inverted with a control). **Both granted by the orchestrator, both scoped to those regions, and the regions are far apart** — annot edits `compile.ml:181,291` against unlimit's `:366`; unlimit edits `bin/main.ml` at ~`:77-165`, ~`:507-600`, ~`:856-880` against annot's `:741,753`. **The reason in both cases was the same**: routing the change through the owner would have left a branch whose gate is red, and a branch whose gate is red is one the orchestrator merges on trust. Merge reconciliation is the orchestrator's | `bin/main.ml`, `lib/flatzinc/compile.ml`, `test/unit/test_flatzinc.ml` | orchestrator | wave 26, both landed in their own branches |
| **A THIRD category of limit, found by M7-T1 and not in its brief: REPRESENTABILITY.** The brief named hardware/RAM and proof-size-and-checker-time. A width not expressible as a native int is refused because the arithmetic **cannot be computed** — without it `declare_int` sits in a 2^64 loop — so `min_int..max_int` stays refused **unconditionally** and no flag turns it off. The sentence to keep: *a limit that exists because the machine is small is a flag; a limit that exists because the arithmetic does not exist is not.* Someone will eventually read "M7-T1 removed the width limits" and try to remove this one | `lib/proof/encoding.ml`, `lib/flatzinc/compile.ml` | agent-unlimit | recorded, goes in M7-T1's decision record |

**UPDATE 2026-09-16 (orchestrator): this is now ENFORCED, not requested.** Two further test binaries had to be killed at the ceiling after sessions were warned, so warning is evidently not a control. `make`, `scripts/run_model_tests.sh` and `scripts/verify_proof.sh` apply `ulimit -v 4000000` themselves; `CLAUDE.md` carries the rule where every session reads it first. The cap is verified to bite (5 GB allocation -> `MemoryError`, 100 MB fine, gate peaks at 18.5 MB). **A bare `dune runtest --root .` in a worktree is still uncapped** — that is M1-T53, and until it lands, wrap your runs yourself: `(ulimit -v 4000000; timeout 900 dune runtest --root .)`. A run that dies against the cap is a finding to report, not a cap to raise.

| **D-0069's and D-0068's tables need correcting, and `docs/DECISIONS.md` is not mine (`scripts/**`, `tools/**` only).** M7-T10's re-run changes the numbers both records publish. (a) The cause was an **instance-ID collision**, not a non-atomic capture: the id was `<year>_<family>` and a family holds many `.mzn` files, so up to fifteen jobs shared one output path. Temp-plus-rename alone would not have fixed it. (b) **101 of the 436 rows are void**, not 22 -- every row of the 18 colliding ids -- and the run covered **353 distinct instances**, not 436. (c) D-0068's headline **`OK-PROOF-VERIFIED` 8 becomes 17**: `2010_bacp` alone is **8 verified proofs and 7 timeouts**, recorded as 15 model refusals. (d) D-0069's row "a torn `.fzn` -- 13" should read 26 suspect rows over 101 void ones, and its "no `solve` item / no such file: 9" resolves to 5 genuine `REFUSED-LIMIT` (set-literal domain, M6-T2) and 4 genuine `REFUSED-MODEL` (`bool_search` with a constant in the array, M7-T7). **`REFUSED-MODEL` 248 and the M7-T7 count of 143 are both lower bounds until the void rows are re-run.** Corrected data: `fataepyc-07:/scratch/arthur/corpus-out-m7t10/results.tsv` | `docs/DECISIONS.md`, `docs/ROADMAP.md` | agent-harness | raised 2026-09-23, **open** |

## Completed

| Task | Session | Date | Summary |
|---|---|---|---|
| M0-T1 | setup | 2026-09-14 | Project skeleton, docs, dune files, test harness, `.claude/` setup |
| M0-T2 | orchestrator | 2026-09-14 | opam 2.5.2 + OCaml 5.1.1 switch `baguette`; bootstrap.sh rewritten to fetch the opam binary |
| M0-T3 | all | 2026-09-14 | Everything compiles; 253 unit checks pass |
| M0-T4 | orchestrator | 2026-09-14 | `make check` green, with `test/models/PENDING` for not-yet-working models |
| M1-T1, M1-T2, M1-T3 | agent-core | 2026-09-14 | Domain (bitset holes), Store (trail + explanation arena), Explanation (memoised Deferred) |
| M1-T4, M1-T5 | agent-proof | 2026-09-14 | Encoding, OPB writer, proof writer; proofs accepted by veripb 2.2.2 |
| M1-T6 | agent-flatzinc | 2026-09-14 | Hand-written lexer/parser/builder; parses all five test models |
| M1-T7a | agent-core | 2026-09-14 | `int_lin_le` bounds propagator, deferred explanations, 33 checks incl. brute-force soundness |
| M1-T7b | agent-justify | 2026-09-14 | `Justify`: memo, level-wipe lockstep, `Linear` as faithful `rup` (D-0009) |
| M1-T7c | agent-encoding | 2026-09-14 | `Encoding.expand_int_lin_le`: integer term to PB row over the order encoding |
| M1-T7 | orchestrator | 2026-09-14 | Chain fix (D-0010) + cross-session repairs; a real pruning's reason is accepted by veripb |
| M1-T14 | orchestrator + agent-compile + agent-output | 2026-09-15 | The CLI is wired: `.fzn` in, solution + verified proof out. 5 models pass, 564 checks |
| M1-T13 | agent-trace + orchestrator | 2026-09-15 | D-0018/D-0021: one `rup` line per pruning, root prunings included. `chain_sat` and the three D-0012 parity models verify; no veripb xfail left anywhere |
| M1-T9 | agent-ne | 2026-09-15 | D-0019: `int_ne`/`int_lin_ne` over the **order** encoding — the direct encoding is not what a disequality needs. 182 checks. CLI wiring still open |
| M1-T15 | agent-mutate | 2026-09-15 | D-0020: mutation harness + control lane, 18 checks. Found `lin_unsat`'s refutation has a unit of slack |
| M1-T16 | agent-tests | 2026-09-15 | Case matrix + randomised differential tester, 152 checks, 17 verified break-it mutations. Found 3 real bugs (2 new), all pinned; gate is red until M1-T17 |
| M1-T17 | agent-fix + orchestrator | 2026-09-15 | D-0022/I-X7/I-P5: `remove_with_facts`, and a clausal root conflict closed by the empty clause. Gate green |
| M1-T11 | agent-ne-wiring | 2026-09-15 | `int_ne`/`int_lin_ne` posted by `compile.ml` instead of rejected, + five disequality models. 14/14 models verify, `PENDING` empty, 864 unit checks. On branch `worktree-m1-t11-ne-wiring` |
| M1-T12 | agent-explain + orchestrator | 2026-09-15 | D-0015: `Combine`/`Weaken`/`Model_row` made real and the root conflict wired to its derivation; two UNSAT proofs verify. Row added 2026-09-15 — the task shipped but was never released from Active claims |
| integration | orchestrator | 2026-09-15 | `test/unit/test_endtoend.ml` is green as part of the 864-check suite. Row added 2026-09-15 — released late, same reason |
| M1-T21 | agent-output + orchestrator | 2026-09-15 | An output item carries its declared `out_ty`, captured in `builder.ml` where the declaration is still in hand. `bool_out_sat.fzn` pins all three routes to the printer. 868 unit checks, 15/15 models |
| M1-T20 | agent-matrix + orchestrator | 2026-09-15 | Three new disequality instances fill the offset and negative-domain cells for both propagators and `|a|>1` / common-factor for `int_lin_ne`; the note now distinguishes cells blocked by a bug from cells unreachable by construction. 194 matrix checks |
| M1-T18 | agent-proof3 + orchestrator | 2026-09-15 | Checker selection in one place (`Checker.find` / `scripts/checker.sh`), 3.0.2 the checker of record, and a missing checker now FAILS instead of skipping. Found and fixed a real proof bug: 3.0.2 rejected `ne_conflict_sat` |
| M1-T19 | agent-proof3 + orchestrator | 2026-09-15 | VeriPB 3.0 is the emitted default. 925 unit checks / 0 failures under **both** formats, 15/15 models. D-0023, D-0024, D-0025 |
| M1-T24 | agent-trailcursor + orchestrator | 2026-09-16 | `Engine.propagate` walks the trail by index instead of materialising it. Wake order is preserved exactly, not merely as a set — verified by the orchestrator by flipping the loop and confirming the two order checks go red while the three vacuity guards stay green. 931 unit checks, 15/15 models, all 45 model artefacts byte-identical. Perf: ~2.7x on a synthetic 12000-entry trail, **no measurable difference on the real models** — reported as the null result it is |
| M1-T22 | agent-delrange + orchestrator | 2026-09-16 | `del range LO HI` deletes `[LO, HI)`, re-measured with controls before anything was changed. `Writer.del_run` emits the exclusive bound, falling back to a `del id` list when the run ends at the newest id. 7 leaked ids now retired; +0.4% proof bytes; no solution changed. The **same off-by-one was in `scripts/mutate_proof.sh`** and the orchestrator fixed it |
| M2-T0 | agent-decisions | 2026-09-16 | **D-0027**: D-0011 is a rule about *naming* rows, not counting them. Multi-row derivations are permitted, so **M4-T1 is unblocked**; the decomposition default stands and `int_lin_eq` is not re-fused |
| M1-T27 | agent-decisions | 2026-09-16 | **D-0028**: width-proportional justifications are accepted and not weakened; no cap today. Measured, not predicted — a model with **zero prunings** emits a 29.8 MB proof line. Corrected its own roadmap row, which named a function with no caller in `lib/` |
| M1-T23 | agent-overflow + orchestrator | 2026-09-16 | **The soundness gap is closed.** D-0029 + a normative SPEC 2.1 paragraph. Orchestrator reproduced the gap independently before merging: a model whose true answer is SAT printed UNSAT and veripb returned `s VERIFIED UNSATISFIABLE`, because the `.opb` row was folded from the same wrapping arithmetic as the propagator. `Checked` raises rather than declines — declining is unsound once the row is already written. Cap `max_int/16`, derived and asserted. 1005 unit checks, 17/17 models |
| M3-T5, M3-T3 | agent-bench + orchestrator | 2026-09-16 | The proof benchmark: four separate columns, no total, minimums one at a time, spreads printed, and deltas inside the spread labelled `noise`. **It measured the process floor first, and that reframes the suite**: 15 of 18 models are timings of `exec`. Refuses models above w=10^5 or an estimated 2 GB peak (~1.5 kB RSS per unit of width, measured). `make bench` added by the orchestrator |
| M1-T30 | agent-bench + orchestrator | 2026-09-16 | Three `width_` models. Orchestrator confirmed `width_root_unsat`: 6 proof lines, longest 23,779 B = **99.5% of the proof**, zero prunings. The gate can finally see width. +0.20 s on the model suite, stated plainly |
| M1-T26 | agent-mutate2 + orchestrator | 2026-09-16 | **D-0030.** Typed mutation knobs moved into the emitter; controls made mandatory *in the type system* (a lane takes a token only the control gate produces). Lanes 14 -> 24, checks 18 -> 37. Found that `drop-line` fails on the grammar in **both** formats, and that **`root_unsat` cannot test load-bearingness at all** — one of its model rows is infeasible by itself. Orchestrator confirmed: a proof deriving *nothing* verifies on it. Registered `Known_slack`, not weakened away. Ninth instance of this project's signature failure mode |
| M1-T25 | agent-lazy2 + orchestrator | 2026-09-16 | **D-0031. Answered, not implemented — and that is the right outcome.** The ladder is load-bearing because the checker's own unit propagation needs it, which no citation census can see. Lazy-by-`red` needs a *rotation* witness (the obvious swap is refused) and costs Θ(w²) — 5× larger on a committed model. `encoding.ml` and `order_reason.ml` are byte-identical to before the task started |
| M1-T28 | agent-lazy2 + orchestrator | 2026-09-16 | Index-walk in `linear.ml`. Direction shown by experiment, not argued: flipping it gives **10 veripb rejections**. 60/60 artefacts byte-identical; **9.9× at N=300**, null on the committed models |
| M2-T1, M2-T2 | agent-bool (x2, interrupted) + agent-bool3 + orchestrator | 2026-09-16 | **D-0032.** Six Boolean builtins, 9 models, 1168 unit checks, 29/29 models. No `Explanation` ADT change needed. Delivered across three sessions, two of which were killed mid-task; each was salvaged to a branch rather than restarted. **13 deliberate breaks, each watched go red** — and break 7 showed a justification with no facts at all passing everything, because the test scenes held their facts as `.opb` model rows |
| M2-T11 | agent-fuzz (interrupted) + agent-fuzz2 + orchestrator | 2026-09-16 | Seeded branching order, default unchanged. **60/60 artefacts byte-identical with hashes**, and a control showing the check can fail. ~500k solver runs. **Found M1-T44**: a correct UNSAT answer whose proof veripb rejects, CLI-reachable and predating the task — orchestrator reproduced it and confirmed the derivation lands on `0 >= 0`. Also found `random_order`'s hole guard shipped disabled by a short-circuit |
| M4-T4a | agent-interval | 2026-09-16 | `lib/core/interval.ml` + `test/unit/test_interval.ml`, 94 brute-force checks, 12 deliberate breaks each watched go red. Orchestrator reproduced break 12 independently before merging |
| M1-T34, M1-T35, M1-T37 | agent-cli | 2026-09-16 | `--time` (CPU clock, stderr only, artefacts byte-identical — orchestrator verified), `Checked.Overflow` arm exiting 4 not 3, path-independent `.opb` header. **26 of 29 models are 84-96% process start-up.** **Eleventh instance of the signature failure mode — and the first found *inside the check written to prevent it*** |
| M1-T42, M1-T33, M1-T40 | agent-oracle | 2026-09-16 | **8 of 9 veripb builders accepted a factless justification** — measured first, and the two causes separated. I-S1's oracle now evaluates in arbitrary precision. Found M1-T50 (`pol <own row> <own row> +`). 1223 checks, 174 artefacts byte-identical |
| M2-T5 | agent-granularity | 2026-09-16 | `Domain.change` + engine trigger masking + the `BAGUETTE_DEBUG` I-P2 re-run check. **An unsound mask passes all 29 models** — orchestrator reproduced. `masked = 0` on every model. D-0034 |
| M1-T44 | agent-rootfix | 2026-09-16 | **The rejected root proof is fixed**, and the rival diagnosis refuted rather than argued down. Orchestrator verified both directions on the original reproducer. D-0035, I-X9, new model `root_hole_unsat.fzn` |
| M1-T32, M1-T38, M1-T39, M1-T41 | agent-proofhyg | 2026-09-16 | The committing door guarded (I-X8, D-0036), `triple_unsat` certified two ways, `pol_raw` deleted, `consistency_id` asserts the transition. **Caused and then diagnosed the second OOM**; the cause is now linted in the gate |
| M1-T47 | agent-emit | 2026-09-16 | Emission split out of `search`. **Corrected the premise the task was written on**: three funnels plus a flush, and `always_comment` carries every level marker under the default format. Emission is 7.7%/2.3% of search on the two heavy models. 90/90 artefact hashes identical |
| M1-T31 + M1-T50 | agent-ambient | 2026-09-16 | `Explanation.Trivial` deleted, `Decision of Lit.t` added, ambient row unrepresentable. **Found that pushing the wrong decision literal left the whole suite green**; `test_matrix.ml` now observes it. D-0037. Zero of 30 artefacts change |
| M1-T48 + M1-T49 | agent-cli | 2026-09-17 | `--proof-comments`' usage text now says what the flag does (a no-op on every shipped model; `Writer.comment`'s three callers are all in the M4 direct-encoding path), plus a tripwire in `test_endtoend.ml`. `run_model_tests.sh` now asserts stderr is empty, closing the hole where M1-T35's break read 30/30 because the harness diffed stdout only. **Independently re-verified by the orchestrator**: a wrapper solver with byte-identical correct stdout and one stderr line fails 30/30. Merged as 96c9aa1; gate green, 1398 ok, 30/30 models |
| M1-T52 + M1-T53 | agent-testhyg | 2026-09-17 | `Mem_guard`, a `Gc.create_alarm` heap guard that aborts naming the binary and the MB it crossed, with its blind spot (anything off the OCaml heap) documented in its own header; `ulimit -v` stays the outer backstop. M1-T52's move is check-neutral, 145 -> 145. Merged as 89d8267 |
| M1-T53 (coverage + falsifiability) | orchestrator | 2026-09-17 | **Fixing my own dispatch error.** I had scoped agent-testhyg to two test files, so the guard missed `test_prop.exe` — the binary that actually reached 14.9 GB. Wired into the ten binaries no live session holds. Also: `MEM_GUARD_DEMO` installs its *own* guard, so it never tested the installed one, and at cap=1 only test_prop/test_output have heaps big enough to abort — so arming was unfalsifiable. Added `BAGUETTE_TEST_HEAP_CAP_ANNOUNCE` (12/12 binaries announce) and `BAGUETTE_TEST_HEAP_CAP_MB`. b77b039 |
| M1-T51 + M1-T46 | agent-polcheck | 2026-09-17 | **The mechanism, not the adoption.** `Writer.implied` (`ia`, hint mandatory) and `Writer.pol_concluding` (`pol` / `ia` / `del`, returns the *claim*'s id so I-X2 reads unchanged). Headline: **PROOF-FORMAT §2a was missing `e` and `ia`, and both exist in both checkers** — the control was available all along. Break performed on the production writer: a truncated `pol` deriving something strictly weaker is **accepted** bare, **rejected** with the `ia`. No caller in `lib/` yet — see **D-0038**. Merged as 3cbfd1c; gate 1404 ok, 30/30, peak RSS 54 MB |
| M1-T55 + M1-T46 | agent-search3 | 2026-09-17 | Rejected **both** routes the row named — guarding `spec_order` changes where it splits, which *is* SPEC §3.4, and making the trail entry land on its literal is **impossible** (the low side lands iff `k` is in the domain, the high side iff `k+1` is; demanding both *is* the guard condition). Wrote the missing step instead: `Search.bridges` emits, per settled decision, `rup +1 x_ge_m +1 ~x_ge_b +1 ~<ancestors> >= 1`. Tree **unchanged** — all 30 pre-existing proofs byte-identical, verified by regenerating with and without. Merged as c33f809 |
| M1-T56 + M1-T57 | agent-trace3 | 2026-09-17 | T56 turned out to be T57's **prerequisite**, not its sibling: a claim never had to be an order literal — `x <> v` is the clause `x <= v-1 or x >= v+1` — and once a hole has a line, a settled bound can cite the holes the settle crossed. `store.ml` was lent add-only and **not touched**. Breaks: 7/4/9 unit checks and 2 model tests red, with veripb *rejecting*. Forced **D-0039** and **I-S4**. Merged as 3ddd2b7 |
| Conflict resolution + D-0039 | orchestrator | 2026-09-17 | The two soundness sessions reached **opposite conclusions about each other's files**, each correctly stopping at its boundary. Resolved: the bridge is still needed and the reason was never the hole but the *implication*, which is ancestor-conditioned and can have no globally valid line. Corrected the stale prose in `search.ml`, and in `store.ml` where a **third** copy sat that neither agent owned or found. Measured and retired PROOF-FORMAT §4's standalone-RUP property. a7b6e79 |
| M1-T58 | orchestrator | 2026-09-17 | `bin/main.ml` catches `Encoding.Unrepresentable`. Pre-fix, measured by injecting the raise into `solve` on the pre-fix binary: `Fatal error: exception ...`, **exit 2** — the same code as a bad command line — no context, no artefact warning. Post-fix: positioned diagnostic, **exit 4**, matching `Checked.Overflow` since M1-T34. Unblocks agent-widthcap's user-facing story for M1-T54. bf9c84c |
| M1-T60 | agent-property | 2026-09-17 | Verified the property **and refuted the orchestrator's mechanism for it**. Real property: every M1 pruning follows from a **single model constraint**. Landed as **I-X10** + **D-0040**. Bounds-consistent Hall pruning removes *nothing* — it pushes a bound out of a saturated interval — so a hole-phrased invariant would have let M4-T1 through silently. All measurements independently reproduced by the orchestrator before landing. Read-only session; edited nothing, as briefed |
| M2-T7 | agent-instid | 2026-09-17 | **The long pole; M2-T8 -> M2-T9 -> M2-T3 is unblocked.** Engine brackets each `run` with `Store.with_running inst.id`; `Store.apply` stamps `entry.prop`. No mutator takes an id. `conflict_facts`' one-shot slot is **gone** — `Conflict of Store.conflict` carries the facts. `Engine.check_attribution` reads the stamp back **always on**, not `BAGUETTE_DEBUG`-gated. Breaks: 121 and 123 unit FAILs, 30/34 and 34/34 models red; both now ship as permanent tests. **All 102 artefacts byte-identical, re-verified by the orchestrator after a failed first attempt that compared a stale binary with itself.** Landed **I-T4**. Merged as 338c611 |
| M1-T54 | agent-widthcap | 2026-09-17 | `Encoding.max_order_width = 10_000` on `hi - lo`, raised before the Hashtbl and before the ladder loop so a refusal allocates nothing; `Compile` carries the positioned diagnostic and exit 3. Deliberately **not** `Unrepresentable` — that arm exits 4 and blames baguette, which is wrong for a legal model. Boundary re-verified through the CLI by the orchestrator: 10000 solves at exit 0, 10001 refused at exit 3. Overflow-safe by construction (`min_int..max_int` would compute width −1). Ratified as **D-0041** + SPEC §3.1 |
| M1-T61 | orchestrator | 2026-09-17 | The I-X10 closure gate: a classification table asserted exhaustive against a read of `lib/core/prop/`, plus the Hall-bound-move refusal with an accept-side control on the same `.opb`. All three breaks performed; my first attempt at the missing-checker break was invalid (a bad `HOME` falls through to PATH and hits 2.2.2) and `$VERIPB` is the route to it |
| M1-T64 | orchestrator | 2026-09-17 | `make check` now depends on `fmt-check`, which **verifies** formatting; `make fmt` stays the explicit fixer. `scripts/check_fmt.sh --self-test` runs first on every gate and proves **both** polarities in an isolated throwaway project — refuses unformatted, accepts formatted — so the self-test cannot leave a stray module in this shared checkout. Break measured both ways: unformatted code now fails the gate at exit 2 **and is left alone**, where `make fmt` silently rewrote it and passed |
| M1-T43 | orchestrator | 2026-09-17 | Confirmed by performing the flip in a throwaway worktree (`bool_clause.ml` is agent-iface's). `bool_reif_unsat` still reports `s VERIFIED UNSATISFIABLE` under a `pb_lit` polarity flip; **six** SAT models catch it, not the five the row claimed. Documented in the model header with the general rule: SAT models are the net for encoding bugs, UNSAT models for refutation bugs. **My first sweep classified all 34 models wrong** — the case pattern was `*ok*` and the script prints `OK` — so the numbers here are from the corrected run |
| M1-T65 | orchestrator | 2026-09-17 | **Declined as D-0042, on measurement rather than on principle.** The cost is ≈40–58 bytes of `.opb` per unit of **total** declared width, so D-0041's filed gap is real — but total 100 000 is only 4.4 MB / 1 s / 0.3 s verify, and reusing 10 000 as an aggregate would refuse 1 000 variables declared `0..10` (367 kB, 142 ms), an ordinary model. No code. Four reversal triggers named, and the table is in the record so nobody re-derives it |
| M1-T29 | agent-del | 2026-09-17 | The newest-id run is now a **pair**: `del range @c<lo> @c<hi>` (half-open) then `del id @c<hi>`, so it is two bounded lines instead of one carrying `hi-lo+1` citations. Rejected the numeric exclusive bound the row suggested and **measured why**: 3.0.2 accepts one past the last id, errors two past, and silently UNDER-deletes on the last id — a spelling with no margin, reintroducing the bare-integer citation D-0023 removed. Over-deletion is loud in both directions, **re-verified by the orchestrator on its own scene**. Artefacts: 0 `.opb`, 0 `.out`, **14 `.pbp`** moved, all still verifying. Merged as 51f819f |
| M2-T12 (determinism half) | orchestrator | 2026-09-17 | `scripts/check_determinism.sh` in the gate: 34 models solved twice, `.opb`/`.pbp`/stdout must agree. **No golden digest** — a stored hash would be wrong on the next legitimate proof change and would train people to re-bless it, so the check is self-relative instead. Breaks: the self-test catches a flaky `.opb` and accepts the real solver; the real check against a flaky `.pbp` fails 34/34. 0.7 s. The seeded-branching half waits for `lib/core` |
| M2-T8 | agent-iface | 2026-09-17 | D-0026 delivered. `Reason.t` frozen facts, `Reason.lits` takes no store (I-X6 by type on that half), one `Reason.justified` per mutator so I-P4+I-P5 are one obligation, `linear.ml`'s trail scan deleted. 1551 ok, 34/34, **102/102 artefacts byte-identical** (binaries hashed). Ten breaks. Merged as 16ad7c6 |
| M1-T64 followup | orchestrator | 2026-09-17 | `scripts/check_fmt.sh` ran `dune build @fmt` with no `--root .`, so it failed in every worktree — **and reported "files are not formatted"**, a false failure blaming the reader. My bug: M1-T64 put it in the gate without running it from a worktree, which is where every agent works. Fixed and verified from a worktree; a harness error is now reported as one, in dune's words |
| M1-T62 | orchestrator | 2026-09-17 | **Closed by M2-T8, not by work.** Checked the premise before dispatching and both halves were dead: `no_facts` is gone, all four mutators take one `Reason.justified` with no factless sibling and no optional argument, and `ne.ml:343` is a real `lib` caller. What remains — `Reason.none` in three commented places — is the explicit route the row wanted to keep, not the silent one it wanted gone. **One dispatch saved by checking a premise** |
| I-X6 (`explain_cross_conflict`) + M1-T63 | agent-linear | 2026-09-17 | **Corrected the premise I gave it.** The function read nothing live — M1-T13 hoisted the lookup out and it never returned; the real defect was `store` staying in scope beside the thunk. Now structural: takes `~opposite` and **no store**, so re-breaking needs a signature change. Also found the cross-row path is **unreachable from any `.fzn`** (`normalise_terms` merges duplicate coefficients; verified — 0 `pol`, 0 `rup`), so no model can cover it and none was added. Test fires on a wrong answer, not a crash; reddens 2, the only 2 in the suite. Merged as 0916937 |
| M2-T9 + M1-T59 + I-S4 check | agent-index | 2026-09-17 | Index keyed structurally over `Lit.t` (**`Lit.sanitize` is non-injective** — names would have aliased). M1-T59 fell out of it; 2 of 102 `.pbp` moved, verified. **D-0019's gap NOT closed, verified.** I-S4 is now measured: retiring one cited hole line is reported and veripb still verifies (I-X9 re-derives it); retiring both is reported **and refused**. Break A: index one id high leaves 34/34 models green and veripb **accepts a `pol` citing the wrong line**. Merged as f72e902 |
| M1-T36 + M1-T45 | agent-search4 | 2026-09-17 | Node = one child dispatched by `branch` plus the root, counted at dispatch; `stats_consistent` checks `nodes = 2·decisions + 1` on **every** `--stats` run. `lvl` differs structurally (99/49 vs 196 markers on `width_sat_depth`). Hole guard **removed on evidence**: 40 previously-refused shapes forced through 3.0.2, 0 rejections, sweep sensitive to its own corruption. 102/102 artefacts identical. Merged as 06302fd. Produced **M1-T66** |
| M1-T63 (`trace.ml` half) + D-0043 | orchestrator | 2026-09-17 | `trace.ml`'s hedge now names `reject_set_domain` rather than saying SPEC 2.1 "does not admit" a set domain — a subset can be widened, a gate is a line someone must delete. And **D-0038 is resolved as D-0043** |
| M2-T3 plan | orchestrator-plan | 2026-09-18 | Split M2-T3 into **M2-L0 … M2-L9** (new `## M2L` section in `docs/ROADMAP.md`) and recorded the architecture as **D-0044**. Docs only; no `lib/` change. Gate green |
| M2-T13 | agent-flaky | 2026-09-18 | `test_random.ml`'s five `!x > 0` coverage checks (deep decisions, root conflict, div>1, div-remainder, ne-moved-bound) made seed-independent: bounded top-up (cap 4000 extra draws, same seeded stream) keeps generating until every shape is reached, and failure of the check now prints `COVERAGE-GAP (... NOT a soundness failure)` through a new `coverage_check`, distinct from `check`. 130-seed sweep (1-130), 0 failures; top-up actually engaged on seeds 21/53/68/89 confirming it isn't a no-op. `make check`-equivalent gate green: fmt-check, width lint, determinism (34/34), 1625 unit checks, 252 matrix checks, 44 mutation checks. Commits `fb0ebf9`, `30b1d73` on `wave10-flaky` |
| M2-L0 | agent-concl | 2026-09-18 | **D-0043 implemented.** `justified` gains `concludes : fact option` via a **required** `~concludes` — the recommendation taken, for `reason.ml`'s own `none` reason: a defaulted `?concludes` would be `set_lo` silently meaning `no_facts` again. 13 lib + 46 test sites write it out. `Writer.pol_concluding`/`implied` have their **first caller in `lib/`** (`Justify.emit_concluding`), closing M1-T51's adoption gap: a truncated `pol` is ACCEPTED bare and REJECTED once the conclusion is stated, matched against both checkers' wordings. **Finding**: the naive "exactly the new bound" check reddens three *real* scenes — `Domain.set_lo` settles over holes (I-D2), so the bound a propagator can **prove** and the bound the trail **lands on** are two different honest numbers; `conclusion_holds` admits exactly that window, value by value. +34 checks. Merged as `a229509` |
| M2-L2 | agent-cut | 2026-09-18 | **The cut, as data** — learns nothing, backjumps nowhere, so it was oracle-tested before anything depends on it. The criterion is a record carrying its **own postcondition**; three ship (`one_uip`, `conflict_side`, `decision_cut`), and `conflict_side`'s two-conflict-level cut is **accepted**, with an explicit check that `one_uip`'s postcondition is false of it — the line that would have reddened had 1UIP been written as an invariant of the cut, which is exactly what D-0044's amendment warned about and what M2-L6 needs. Holes load-bearing and measured: strip the folded `int_ne` facts and the cut is brute-force SAT. +64 checks. Merged as `a229509` |
| M1-T66 | agent-bridge | 2026-09-18 | **Row NOT closed — the prize is out of reach in M1, and here is the proof.** The bridge's absence is now observable at the **derivation** rather than by grepping proof text: `Search.bridges` files a `Search.bridge` per settle (decision, literal assumed, bound settled onto, holes crossed, and which line states each hole at which level) and one `Trace.record_citation` per named hole, so a **decision** settle enters the I-S4 audit it was entirely outside of before (`Trace.emit` skips level-start entries, so a decision push writes no line and recorded no citation). Two scenes in `test_matrix.ml` read those records. Measured with `bridges` made a no-op: `bridge_derivation` reddens **at the derivation**, with a message saying the settle step is missing — while **veripb still accepts the proof**. That is route 1 answered in the negative and answered *analytically*: the settle is re-derivable from the page by two routes, the hole's own trace line (M1-T56) and, under it, `int_lin_ne`'s big-M `.opb` rows (I-X10) which no `w` can retire. `br_unnamed` is empty in both scenes, i.e. the page always names the hole. **No proof bytes change.** +15 unit checks (1723 -> 1738), 34/34, peak RSS 36 MB. Commits `7ae1843`, `6d08c4b` on `wave11-bridge` |
| M2-L1 | agent-learned | 2026-09-18 | `Learned.t` (PB inequality over `Lit.t`, clause = degree-1 case), its runtime instance as a **`Linear` instance** registered through the new `Engine.add`, and its proof-side introduction/deletion through the new `Writer.with_level`. D-0044's central claim **converted**: measured green on all 27 scenes. D-0045's prediction **measured before fixing**, in both formats. 1766 unit checks, 34/34, determinism clean. |

| M2-L3 | agent-learn3 | 2026-09-18 | 1UIP clause learning over order literals, proof-only (**D-0044 fork (ii)**), with conflict-directed backjumping over the **decision closure** and its `rup` derivation at level 0. **I-S4's cross-level debt is discharged** and the check is wider than the invariant's wording. Backjump measured: 31 -> 9 nodes on `backjump_unsat.fzn`. **M1-T66 stays OPEN**: with `Search.bridges` disabled, 35/35 models still pass and no checker rejects — a learned clause citing across levels did NOT make the bridge load-bearing. 1833 unit checks, 267 matrix, 44 mutation, 35/35 models, determinism 35/35 byte-identical |
| M2-T14 | agent-fmt2 | 2026-09-18 | Format-2.0 vacuity sweep. Three more instances of the M2-L0 defect found and fixed (test_proof 3.0-only lanes resolving 2.2.2 via `$VERIPB`; D-0030's certification in test_mutation writing a 3.0 proof against an env-format `.opb`; 20 blanked-trace controls asserting on exit status alone). Test (c) now checks the claim index by content, so it runs under both formats. |
| M2-L8 | agent-bench | 2026-09-18 | The learning benchmark. Third table in `bench/run_bench.sh` reporting learned / convertible / skipped / pb-tried / pb-learned / pb-fallback / fb% / pb-stronger **beside** `.opb` bytes, `.pbp` bytes and verify ms, per model and summed over the suite as counts only. Verdict widened from M1-T36's nodes-alone to all four tree counters. **`bench/run_bench.sh -c`** is the control the row demanded: three scenes, asserted in both directions, exit non-zero on a misclassification, watched fire against three broken classifiers. `-f`/`-F`/`BAGUETTE_PROOF_FORMAT` gone from `bench/` (D-0046). Suite: 86 clauses over 21 of 38 models, 13 convertible, 9 skips over 4 models, PB 86/36/50 = **58% fallback**. |
| M2-T16 | agent-drop | 2026-09-18 | **Proof format 2.0 removed from the project entirely** (D-0046). `Writer` emits 3.0 and only 3.0; `V2_0`, `BAGUETTE_PROOF_FORMAT`, `default_format`, every `v3 t` branch, `Pol.to_string`, `Opb.write ?labels` and `Encoding.write_opb_for` are gone, and `Checker.find` / `scripts/checker.sh` resolve one checker. **Artefact bytes byte-identical across all 38 models** (`.opb`, `.pbp`, stdout), binary hashed on both sides and different. Unit checks 1986 → 1972, all 14 accounted for. History kept and marked: D-0023/24/25/30 and `PROOF-FORMAT.md` §2. |
| M6-T6 | agent-bisect | 2026-09-21 | Bisected `width_sat_depth`'s regression: the 43 ms comment was true when written; the whole ~14x jump is one commit, `aacbc8d` (M2-L6 wired into `Search`), 18.6 ms parent -> 258.7 ms. `git bisect run`, 7 steps, 0 skipped. Recommend accepting as the cost of M2-L6's PB analysis, which M2-L13 already claws most of back. `bench/README.md` §3g, new `bench/width_sat_depth_bisect.sh`. |

## Handoff notes

Newest at the bottom. Two or three lines: what changed, what surprised you, what the next
session should know before touching the same area.

**2026-09-14 — setup**
Scaffolded the project. Two things the next session must know:
(1) There is **no OCaml toolchain on this machine** — `ocaml`, `opam` and `dune` are all
absent. Run `scripts/bootstrap.sh` first. M0-T2.
(2) The OCaml under `lib/` was written **without a compiler available to check it**.
Treat it as a typed sketch of the intended shape, not as working code; M0-T3 is making it
actually compile, and correcting it is expected rather than a sign something went wrong.
`veripb` is already installed (`~/.local/bin/veripb`, format 2.0) and works.

**2026-09-14 — orchestrator**
Toolchain installed: opam 2.5.2 binary in `~/.local/bin`, switch `baguette` on OCaml
5.1.1 being built by `scripts/bootstrap.sh`. `bootstrap.sh` now downloads the opam
release binary rather than piping the installer script, which is what actually worked
here; `bubblewrap` is absent so sandboxing stays disabled.
Three agents dispatched in parallel on disjoint file sets (see Active claims). They do
not commit — the orchestrator commits each area as it lands, to avoid racing on the git
index.

**2026-09-14 — orchestrator, after the first parallel round**

Three agents ran concurrently on disjoint file sets and none collided, but file-level
claims turned out not to be enough: **dune holds a global lock on `_build/`**, so
concurrent builds corrupt `_build/.lock` and both fail. Build into your own
`--build-dir` while others are working. This is now in CLAUDE.md.

Seven errors in `docs/PROOF-FORMAT.md` were found by building against the real checker
and are fixed. Two of them silently corrupt a proof rather than failing it — the worst
being that an `.opb` line with `=` counts as **two** constraints for the `f` rule, which
shifts every later id so `pol` steps quietly reference the wrong constraints. If you are
touching the proof layer, read section 2's "Traps" before anything else.

`make check` is green but five model tests are `xfail` via `test/models/PENDING` — the
solver does not solve yet. Delete lines from that file as propagators land; the runner
fails if a listed model starts passing, so the list cannot rot.

**Next is M1-T7** (`int_lin_le` + its `pol` justification). It is the reference
propagator — every later one copies its shape — so it is worth doing carefully and alone
rather than in parallel with M1-T8/T9.

**2026-09-14 — orchestrator, after the M1-T7 round**

Two agents ran on disjoint files, both reported success, both were individually good, and
**their halves did not compose**. `Explanation.Linear` was read as "the bound facts" by
the propagator and as "the model row restated" by the bridge. veripb accepted the bridge's
output because restating a constraint is trivially valid, so nothing went red; the id it
handed back simply did not assert what the explanation claimed. Composed, the two would
have emitted twice the model row and justified nothing.

The lesson for the next round is not "claim files more carefully" — the file claims worked
perfectly. It is that a shared *type* is not a shared *contract*. When a task is split, the
split must state what each constructor means operationally, with an example of the emitted
text, or two sessions will agree on the type and disagree on the semantics.

D-0009 records the underlying finding, which was checked against the checker rather than
argued: **a bare literal in a `pol` is the trivial axiom `lit >= 0`**, so bound facts can
only enter a `pol` as constraint ids. That is why `Linear` cannot render as a `pol` today,
and why `Cut`'s missing division matters. Both belong to D-0003, still open — this is the
first time leaving it open has cost real work.

Also found: nothing expands `sum a_i x_i` into PB literals over the order encoding, so the
model row an `int_lin_le` proof must cite cannot be written at all yet. That is now M1-T7c
and it blocks the end-to-end check. `make check` is green, and `test/models/PENDING` is
unchanged at five — the solver still does not solve.

**2026-09-14 — orchestrator, M1-T7 closed**

It works: `Linear.propagate` prunes, its explanation renders, and veripb accepts the
result. The two-step case that broke is now a counted I-X1 check emitting
`rup +1 x2_ge_1 +1 x2_ge_2 >= 2 ;` followed by `pol 10 11 +`.

Three bugs in three rounds, none of which a green test suite caught:

1. Two sessions read `Explanation.Linear` differently and veripb accepted the mismatch,
   because re-stating a constraint is trivially valid (D-0009).
2. A bound fact stated as one literal instead of a chain. It verified at a one-step bound
   and is unsatisfiable at every larger one, so the first test written happened to land
   on the only value where the bug is invisible (D-0010).
3. `make`'s new signature broke the other session's test file, seen by neither, because
   each builds scoped to its own target — which is exactly what the shared `_build/` lock
   forces them to do.

The pattern in all three: **each session verified its own half and every half was green.**
What found the bugs was running the halves together against the real checker. Whoever
orchestrates the next round should treat "both agents report success" as the beginning of
review, not the end of it, and should own one integration test that no single agent can
make pass alone.

For M1-T8: copy `prop/linear.ml`'s shape *and* `prop/order_reason.ml`'s chains. Do not
re-derive bound-fact literals by hand — that is the D-0010 bug, and it will look like it
works.

**2026-09-14 — orchestrator, after D-0013**

The whole M1-T7/T8 vertical (propagator, explanation, bridge) is being handed to **one**
session this round rather than split. Splitting it along `Explanation.t` is exactly what
produced D-0009: two sessions agreed on the type and disagreed on its meaning, and the
checker accepted the mismatch. A shared type is not a shared contract, so this time the
type and both of its users move together.

`lib/core/explanation.ml` is unfrozen for agent-explain, and only for it. D-0013 says what
the ADT is missing and why; the change is no longer speculative.

**2026-09-15 — orchestrator, M1-T14: the CLI is wired**

`bin/main.ml` no longer prints "not implemented yet". Five of the seven models solve
and veripb accepts every proof; `make check` is green at 564 checks, up from 462.
`test/models/PENDING` is down to two: `ne_sat` (M1-T9, `int_ne` is now *rejected* with
a position and a name rather than absent) and `chain_sat`.

Two things the next session should know.

**The split worked this time, and the reason is worth keeping.** Two sessions ran on
disjoint files again, but unlike the M1-T7 round the contract between them was written
out operationally — what each function must *mean*, which index space it lives in, an
example of the bytes it emits — rather than being left implicit in a shared type. The
one cross-piece invariant (`Var.of_int i` denotes `Model.var m i`) was stated in both
briefs, implemented in `Compile`, and re-checked at run time in `main.ml`, because a
permutation there is invisible to I-S1: the check would be handed the same permuted
array and confirm it. Nothing had to be repaired at integration.

**`chain_sat` was added to catch an index permutation and caught something else.**
It is satisfiable, the answer is right, and veripb rejects the proof — see D-0017.
D-0012 said a SAT run's nogoods carry no weight because `conclusion SAT` checks the
assignment. True of the conclusion, false of the steps: veripb checks every rule as it
is emitted, so a nogood logged while the search is still hunting sinks the proof. That
makes **M1-T13 gate satisfiable models too**, which is a much larger claim than the
roadmap's framing — any model whose search takes one wrong turn before succeeding emits
an unverifiable proof. It stayed hidden because a SAT run only logs a nogood if a branch
fails first, and every satisfiable instance in the suite happens to be solved by a search
that guesses right at every level.

For whoever takes M1-T13: it is now the single thing standing between this solver and
being usable on anything non-trivial, and D-0016 point 1 is the most promising lead —
`pol` can recover a leaf's nogood by going through a root contradiction. D-0016 also
warns that guarding the wrong literal produces a valid but useless generalisation, so a
derivation recipe has to identify which decision the branch's refutation actually turns
on.

Smaller notes: `Encoding.add_equality` looks like the way to post an `int_lin_eq` and is
not — it takes PB literal terms and skips the order-encoding expansion; use two
`add_int_lin_le` calls. An empty term list is a real, representable PB row (`>= 1 ;`) that
veripb accepts, which is what makes a false ground constraint like `int_le(2, 1)` provable
rather than a special case. And `make check` reformats a tree someone else has already
called clean, so the reformat lands on whoever runs the gate next.

**2026-09-15 — orchestrator, the D-0018 round**

Three sessions on disjoint files, all three landed, nothing had to be repaired at
integration. `make check` is green with **no veripb xfail anywhere for the first time**;
`test/models/PENDING` is down to one line, and that line is CLI wiring, not proof work.

**The headline is not the code, it is that we had the wrong diagnosis for three decision
records.** D-0012, D-0014 and D-0017 all elaborated on "the branch nogood is unreachable".
It was reachable the whole time. What was missing was that we never wrote down the
propagation the checker was supposed to replay. Reading a solver that had already solved
it (GCS) took about three minutes to overturn what we had been theorising about for three
rounds — and GCS's own docs record the identical misdiagnosis as a known trap, in wording
that matches D-0012 almost line for line. When something in this area resists, read
someone else's implementation before writing another decision record.

Two corrections to my own D-0018, both found by building it:
- point 1 was wrong. "Every pruning **under a decision**" should be "every pruning". A
  `rup` check starts from nothing and does not inherit the root fixpoint. D-0021.
- point 3 (the conflict's own reason line) is redundant for `int_lin_le` and is kept
  deliberately. D-0021 says why, so nobody removes it as dead weight.

`chain_sat` turned out not to discriminate between those two readings: blank either half
of its trace and it still verifies; blank both and it fails. That is the fifth time in
this project that the instance chosen to test a thing could not see the thing break. The
mutation harness (M1-T15) now exists precisely for this, and its first run found that
`lin_unsat`'s refutation carries a unit of slack — veripb accepts that proof with a
corrupted coefficient. Reproduced by hand before believing it.

For the next session: **`int_ne` is written, proved, tested, and not reachable from the
CLI.** `compile.ml:365` still rejects it. agent-ne's handoff has the three lines, and the
one wrinkle is that `instances` is typed to `Linear.t` and needs to become
`Propagator.instance list`; `test_prop.ml` has a worked `pack_ne`/`pack_linear` example.
That clears the last `PENDING` line and closes M1-T11. After that, M2-T3 (clause learning)
is the next real one, and note I-X6 before starting it: conflict analysis is exactly the
caller that will break a `Deferred` thunk that reads live store state, which is a bug
`linear.ml` actually had until this round.

**2026-09-15 — orchestrator, the M1-T16/T17 round**

Populating the tests paid for itself in one round. The matrix and the fuzzer found
**three real bugs, two of them new**, all in the seam between `int_ne` (M1-T9) and the
trace machinery (M1-T13) — two pieces built the same morning and never run against each
other until something deliberately composed them. The root cause of the worst one was a
comment that went stale within hours: `store.ml` justified having no `remove_with_facts`
with "M1 is bounds-only … nothing punches a hole", which M1-T9 made untrue in the same
round. The emitted line was not merely unprovable, it was **false** on a satisfiable model.
That is now invariant I-P5.

Two process notes worth keeping.

**A pin that asserts a bug's symptom expires the moment the bug is fixed.** M1-T16 pinned
bug B as `contains "rup +1 y_ge_2 >= 1 ;"` — the presence of the bad line. Correct while
the bug stood, red the instant it was fixed, and indistinguishable at a glance from "a
test we broke". The replacement asserts the line the same pruning must now write, which
pins the situation and the content together. When pinning a bug, prefer an assertion that
stays true after the fix.

**Two of the three "bugs" had a fix that looked obvious and was wrong.** Weakening the
`Clause` out of the `pol` (the obvious fix for bug A) makes the derivation `0 >= 0`, which
still does not close, *and* erases the signal the real fix reads. Both were settled by
running the checker rather than by argument.

Also: `veripb` here is the **Python 2.2.2** implementation and the 2.0 proof format. The
current VeriPB is a **Rust** rewrite at 3.0.2 and it reads our 2.0 proofs unchanged
(advisory only), agrees with the old checker on all 9 of our proofs including which
mutations it rejects, and is ~30× faster per invocation — 223 ms to 7 ms, almost all of it
Python startup, which matters because the suite shells out to the checker hundreds of
times. Two-phase upgrade proposed and not yet taken: adopt the Rust checker while still
emitting 2.0 (no proof changes), then migrate emission to 3.0 before M2. Phase 2
supersedes D-0002 and needs its own decision record; its prize is **labels**, which delete
the `=`-counts-as-two-constraints trap in PROOF-FORMAT section 2 outright.

**2026-09-15 — agent-ne-wiring, M1-T11: the last PENDING line is gone**

`compile.ml` now posts both disequalities, so `test/models/PENDING` is empty and all 14
models solve with a proof veripb accepts (864 unit checks, 0 failures). M1-T11 and the
CLI half of M1-T9 are closed.

**The wiring itself was three lines, as the last handoff said. The hour went on finding
an instance that could watch it fail.** `ne_sat.fzn` — the model this task was measured
by, and the one line in `PENDING` — carries `int_lt(x, y)` beside its `int_ne`, and
`int_lt` alone fixes `x = 1, y = 2`. It passes whether or not the disequality does
anything, and its SAT proof contains no `rup` at all, because a search that never
conflicts never cites a reason and `conclusion SAT` is self-checking. Wiring `int_ne`
and calling that green would have been the sixth instance in this project that could not
see the thing it tested break. Five models now cover what it cannot: a bound moved by
`int_ne` alone, `int_lin_ne`'s division under a non-unit coefficient (nothing exercised
`int_lin_ne` from the CLI before — every `int_ne` is `1*x + (-1)*y <> 0`), a satisfiable
run refuted once *by* a clause, both branches closed by clauses and resolved to the
empty clause, and `int_ne(x, x)`.

Two things worth knowing before touching this area.

**`Engine.create` indexes its array by `Propagator.id`**, so an instance's id must equal
its position in the list it is handed — and an arm of `compile`'s match may yield one
instance or two, so it cannot know its own position. The arms now yield `pending`
instances (`int -> Propagator.instance`) and `compile` assigns ids once with a single
`List.mapi`. A new arm that packs its own instance with an id it invents will look
correct and will run the wrong propagator.

**`int_ne(x, x)` is a real case and it works.** `normalise_terms` merges the two
occurrences into a zero coefficient and drops it, leaving the false empty sum, and both
halves agree about it with no variable left to disagree over: the A/B rows degenerate to
two contradictory units on the auxiliary Boolean, the propagator conflicts with an empty
`Clause`, and the refutation is `rup >= 1 ;` closed the D-0022/I-X7 way. That is
`ne_self_unsat.fzn`. No special case was added and none should be — it is the
ground-constraint argument in `compile.ml`'s header, a second time.

One finding handed back rather than fixed, in `Cross-session requests`:
`test_matrix.ml`'s empty-cell note still says disequality prunings emit a factless trace
line, which M1-T17 fixed. Four `int_ne` shape cells are now fillable and the note says
they are not. M1-T11 claimed neither the matrix nor `lib/`, so it is a request.

Note for whoever merges: this work is on branch `worktree-m1-t11-ne-wiring`, not on
master. `test_output` and `test_mutation` locate the checkout from the cwd or the
executable path, so building into a `--build-dir` outside the tree makes both FAIL
loudly (not skip) — pass `BAGUETTE_ROOT`, or just use `dune --root .` inside the
worktree, which gives each worktree its own `_build` and no shared lock at all. That is
a cheaper answer to the `_build` contention in CLAUDE.md than a private `--build-dir`.

**2026-09-15 — orchestrator: the claims table had rotted, and M1 is merged to master**

Three rows sat under `## Active claims` describing work that had already shipped:
`integration`, M1-T12 and M1-T13. M1-T13 was *simultaneously* listed under Completed, so
the two tables contradicted each other. M1-T12 and `integration` were in neither. A
session reading the protocol in good faith would have believed `explanation.ml`,
`justify.ml` and `prop/**` were held by a live agent and routed around files nobody was
holding — which is exactly the cost the protocol exists to avoid, paid for nothing.

Both tables are now correct and Active claims is empty. **The lesson is not "remember to
release"** — every one of those three sessions *did* write a handoff note; what they
skipped was the one-line table edit, because the note felt like the deliverable. If a
session writes a handoff note without also moving its row, the row is what a later
session reads. `/handoff` does both; the rows that rotted were released by hand.

`worktree-m1-t11-ne-wiring` is merged to master as a fast-forward (4 commits, 0 behind).
M1 is closed: M1-T1..T17 all DONE, 14/14 models solve, `PENDING` empty, 864 unit checks.

**On the checker.** `veripb` resolves to the **Python 2.2.2** build at `~/.local/bin`,
but a **Rust 3.0.2** build is already installed at `~/.cargo/bin/veripb` — `~/.local/bin`
simply comes first on PATH. The previous handoff's two-phase proposal is therefore
cheaper than it reads: phase 1 needs no new install, only a decision about which binary
the harness invokes. Dispatched this round as M1-T18 / M1-T19.

**2026-09-15 — orchestrator, M1-T21 merged: the bug was in the builder, not the printer**

`output.ml` blamed `Model.t` for losing the type. It was not `Model.t`: `builder.ml` had
the declaration's `Ast.base_type` in hand at the moment it recorded the output item and
threw it away. The type now rides on the output item (`Out_var of string * out_ty *
operand`), so `Const` and `Var` render by one rule and the constructors do not typecheck
without it. That is the difference between a fix and a guess-it-back-at-print-time patch.

Verified here rather than taken on report: merged, rebuilt, `bool_out_sat.fzn` matches
its expected output byte for byte and veripb accepts its proof; 868 unit checks, 0 FAIL;
15/15 models pass; `PENDING` still empty.

**A trap worth writing down, because I fell in it.** `dune runtest` does **not** rebuild
`bin/main.exe`. I ran the suite green, then invoked `_build/default/bin/main.exe` by hand
and watched the *old* binary reproduce the bug — 868 checks green and the CLI still
printing `aliased = 1;`. The gate is not affected (`make check` is `fmt build test`, and
`models:` depends on `build`), and the unit-level model assertions link the library
rather than the exe. But anyone spot-checking the CLI after a `dune runtest` is holding a
stale binary. Build before you believe what the CLI tells you.

Two gaps agent-output found and correctly did not fix, neither an output bug today:
a **par** declaration carrying `output_var` is silently dropped (`record_scalar_output`
is reachable only from the var path), and `bool: q = 3;` is accepted silently
(`check_par_domain` has no `Tbool` arm). The second is now caught wherever it matters —
aliasing such a par into a `var bool` is a declaration-site error.

One file outside the assignment: `test/unit/test_flatzinc.ml`, unowned this round,
changed mechanically for the constructor arity. No assertion changed meaning.

**2026-09-15 — orchestrator, M1-T20 merged: two cells stay empty, and the reason changed**

The note was wrong and the task was live: M1-T17's `Store.remove_with_facts` really did
unblock those cells. Three new instances now cover the offset and entirely-negative
shapes for both disequalities, and `|a| > 1` and common-factor for `int_lin_ne`.

**`int_ne` x `|a| > 1` and x common-factor stay empty, and the note no longer blames the
bug.** `int_ne` *is* `1*x + (-1)*y <> 0` — its coefficients are 1 and -1 in every
instance there can ever be, so those shapes are unreachable **by construction**. They
could be turned X by putting a big coefficient on some *other* row of an `int_ne` model,
since a shape is credited to every propagator in an instance's `props`; that would record
something `int_ne` did not do. Left empty on purpose, like the `int_lt` row. The
remainder column is empty for the same kind of reason: a non-zero remainder is precisely
where a disequality declines to prune, so there is no push to round.

Verified here rather than taken on report. I re-ran the agent's mutation myself — stubbed
`Ne.propagate` to `Fixpoint`, rebuilt, and watched all three new instances fail by name
(`int_ne/negative-domain`, `int_lin_ne/common-factor-offset`, `int_lin_ne/coprime-negative`),
58 failures in all — then reverted and confirmed 915 `ok`, 0 FAIL, 194 matrix checks.

**The finding to carry forward.** The agent's first drafts were two-variable models, and
they failed the existing `every nogood needs the trace — none is standalone-RUP` check:
over domains whose declared bounds the search reaches directly, veripb's own unit
propagation replays the whole refutation from the `.opb`, so the nogood is standalone-RUP
and the trace it was supposed to rest on was never load-bearing. A passing, hollow proof
— the seventh instance of this project's signature failure mode, caught this time by a
check rather than by a human. The instances were fixed, not the check. That check has now
paid for itself twice.

**2026-09-15 — orchestrator: 3.0 is the default, and the round is closed**

All three agents merged. `Active claims` is empty and, unlike last time, that is true.

**agent-proof3 was told to re-verify the inherited equivalence claim rather than trust
it, and the claim was false.** 3.0.2 rejected `ne_conflict_sat`. It was our proof, not
the checker: `conclusion SAT : <assignment>` carried only the model variables' order
literals, and 2.2.2 quietly unit-propagated the missing `_ne0` selector while 3.0.2
states outright that a conclusion's assignment is not propagated. `encoding.ml` had
recorded that as "checked against veripb 2.2.2, not assumed" — and it *was*, for 2.2.2.
A fact measured against one checker had been written down as a fact about proofs. The
fix is `sol` plus a bare `conclusion SAT`, which is what PROOF-FORMAT already claimed we
did. **That bug shipped in every SAT proof this project has ever emitted.**

**I finished the flip agent-proof3 left open**, because "3.0 behind an env var with a
2.0 default" is not the upgrade. It cost one line in `format_from_env` and six test
files, and not one failure was a proof being wrong — every one pinned 2.0 *text*.

**Two of those pins are the reason this note is long.** `test_matrix` asserted
`not (contains "# 1" proof)` — "this model is refuted at the root, so no level is ever
opened". Under 3.0 the string `# 1` does not occur *whatever the proof says*, so both
assertions go **vacuously true**. They would not have gone red. They would have stopped
testing, silently, inside a green suite. That is the eighth instance of this project's
signature failure mode and the first where the trigger was a *format* change rather
than a propagator change.

So the spellings now live in `Writer`, which is what writes them — `level_marker`,
`level_of_line`, `opens_level`, `strip_label`, `rule_body` — and tests read proof text
through it. This is the same shape of fix as collapsing nine private `veripb` lookups
into `Checker.find`: a project-wide fact had been copied into many files, and copies
cannot all stay right. **The rule for the next format change: a test that reads emitted
proof text goes through the module that wrote it.**

Measured, not asserted: **925 unit checks, 0 failures, under BOTH 3.0 and 2.0**;
15/15 models; 194 matrix, 18 mutation, 11 random; `fmt` clean; `PENDING` still empty;
`scripts/checker.sh` resolves `~/.cargo/bin/veripb` 3.0.2. The 2.0 fallback is exercised
in full rather than merely retained — an escape hatch nothing runs would rot in a week.

**Correcting D-0023's speed note.** It reported 17–29x per invocation but no change in
suite wall time, because `test_matrix` ignored `$VERIPB` and was 28–31s of a 32s run.
With that file on the shared resolver, **`test_matrix` alone went ~30s → 1.2s.** The
speedup was always real; one file's private lookup hid it from the clock.

Open, and worth knowing before M2:
- `solx` and `obju` are not usable as we emit them under 3.0 (`solx` needs a preserved
  set, `obju` explicit subproofs). Nothing in M1 reaches either; M5 and any enumeration
  work will.
- D-0024's asymptotic cost is unmeasured on a deep search. 3.0 proofs are ~19% larger on
  the current models and the deletion-vs-wipe effect is invisible at this size. Measure
  it before M2-T3 lands, since that is where D-0008's argument mattered.
- Under 3.0 the `drop-line` mutation changes character: deleting a step un-defines its
  label, so a later citation is a parse error. A green `drop-line` lane now means "the
  label was still referenced", not "slack found".
- `docs/SPEC.md` 2.2 still never states the bool print rule M1-T21 enforced (the request
  above). agent-proof3 held SPEC and did not take it; it is still open.

- **GCS comparison, and D-0003 closed** (agent-gcs-diff, 2026-09-16). Three read-only
  sweeps against `/home/arthur_gla/gcs/glasgow-constraint-solver` on the three axes the
  user named — engine, proof logging, propagation. Full report in
  `docs/GCS-COMPARISON.md`; it is the reference for every roadmap row added this round,
  and it records what GCS **tried and abandoned** so we do not re-run those experiments.
- The three sweeps ran independently and converged on the same top item, which is why
  D-0026 was written: split the reason (which facts) from the justification (how the
  checker is convinced). Our `Explanation.t` conflates them, which is why `linear.ml`
  keeps `expl` and `facts ()` in agreement with a *comment*, and why it scans the whole
  trail once per term per pruning to find who established each bound.
- **One verified bug, not yet fixed** (M1-T22). `del range LO HI` is **half-open** in
  veripb 3.0.2 — tested directly, with controls in both directions — but
  `Writer.wipe_level` emits it for an *inclusive* run. Every multi-id run therefore
  leaves its last id live in the checker while `tags`/`live` drop it (I-X3 mirror
  violation). Present in 7 lines across 5 of 14 models today. Not unsound; it is proof
  growth, and `PROOF-FORMAT.md:161` documents the wrong semantics. A run of length 1
  takes the `del id` branch and is unaffected.
- **The one soundness gap** (M1-T23): there is no overflow handling anywhere in `lib/`.
  A wrapped product prunes wrongly *and* the `.opb` row is expanded from the same wrapped
  arithmetic, so veripb accepts the proof. On a SAT model I-S1 catches it; on an UNSAT
  model nothing does.
- D-0003 and D-0011 now carry forward pointers. D-0011 sitting at DECIDED with no note
  that D-0015 had already closed its ADT gap is the trap the comparison found: read
  literally, it forbids writing M4-T1's Hall-interval justification at all. Whether its
  *policy* still stands is M2-T0 and is deliberately left open.
- D-0026 was accepted under a condition the next session should hold it to: "not slower"
  is a **prediction**, not a measurement. M3-T5 is the named falsifier. If the layered
  form measures slower on a real model, that reopens D-0026 rather than being absorbed —
  this project has already corrected a speed claim twice (D-0023, D-0025).
- Nothing under `lib/` was touched this round. The roadmap rows are proposals with
  dependencies, not a batch to apply in order; the four worth taking first are M1-T22,
  M1-T23, M1-T24 and M2-T0, of which two are defects and one gates M4.

### M4-T4a released (orchestrator, 2026-09-16)

`Interval` is on master: pure arithmetic over `Checked`, no `Store`/`Explanation`/`Var`,
and no proof machinery -- which is the whole point of the split, because every claim in
it is checkable by brute force over small ranges. 94 new checks, gate green at 29/29.

Three things the next session should carry forward rather than rediscover:

- **The `isqrt` deviation from GCS is load-bearing, do not "restore the port".** GCS's
  initial estimate `(n+1)/2` overflows at `max_int` and the loop then returns a
  *negative* square root. `(n / 2) + (n mod 2)` is the same number and does not wrap. I
  reproduced this myself before merging: 3 checks go red, one of them by raising
  `Checked.Overflow` on `-2305843009213693952 * -2305843009213693952`. The upstream file
  still has the defect; it is unreachable in GCS's own use because their bounds are capped.
- **`quotient_filter` is inexact and says so.** 40 of 4095 small cases are wider than the
  exact hull. The suite counts and prints that number rather than hiding it, and pins one
  instance by name. Containment is asserted, equality is not -- and break 8 shows why:
  swapping `div_ceil` for `div_floor` in the lower bound leaves the containment sweep
  **green**, because a looser bound is still sound. Only the separate exactness claim sees it.
- **A trap is waiting for M4-T4b**, flagged in `interval.ml`'s header. `int_div` truncates
  toward zero (the *relation*); `div_floor`/`div_ceil` round outward (the *bounds*). They
  are two functions apart in one file, and using the relation's rounding to compute a
  bound prunes values that have support.

### M1-T34/T35/T37 released (orchestrator, 2026-09-16)

The CLI can now time itself, and the first thing the instrument showed is that **26 of
the 29 models are 84-96% `exec`**: the solver's own share of them is 0.37-1.6 ms. Three
orders of magnitude of dynamic range were sitting under a wall-clock column that read
6-8 ms for everything. `width_root_unsat` spends **18.8 ms writing the `.opb`** against
5.2 ms of search on a model with *zero prunings* — D-0028's shape on the clock instead
of in bytes.

What the next session must not misread:

- **No row today supports "propagation costs X".** `search` fuses propagation, search and
  `.pbp` emission, because every emission point is below `bin/main.ml`'s reach. The agent
  said so in the CLI's own report, in the harness footer *and* in the README rather than
  letting someone discover it. M1-T47 is the fix: one accumulator at
  `lib/proof/writer.ml:402`, the funnel every rule passes through.
- **The clock is CPU, not wall, and that was forced** — `bin/dune` does not link `unix`.
  So every phase excludes time the process was descheduled, and a CPU number must never be
  subtracted from a wall number as if the difference were an error bar. `notslv%` is
  labelled an upper bound everywhere it appears. Making it exact is one word (`unix`) in
  `bin/dune`, which is mine to add, not an agent's — filed, not done silently.
- The choice of clock was **measured, not assumed**: `Sys.time` resolves to 1 us here,
  while `/proc/self/schedstat` — the obvious nanosecond alternative — only moves every
  1.9 ms and cannot see a 400 us parse.

**The eleventh instance of this project's signature failure mode, and the most instructive
one yet, because it was inside the check written to prevent it.** The bench's own
self-check decided "does this binary support `--time`?" by looking for a `time:` line on
*stderr*. With the whole report deliberately sent to *stdout* — the worst failure this
area can have — it concluded there was no `--time` support, skipped the quietness check as
inapplicable, printed a benign `note`, and **exited 0**. A test that cannot observe the
property it was written to check, found only by performing the break. Detection now turns
on the argument parser's answer, and the report's destination is asserted before anything
about stdout. If you take one habit from this round, take that one: perform the break.

### M1-T42/T33/T40 released (orchestrator, 2026-09-16)

The most useful thing in this round is a distinction the roadmap row did not know it
needed. M1-T42 assumed one cause and measured two:

- The three `int_ne` scenes were D-0032 — facts held as `.opb` model rows, so a factless
  `rup` is genuinely **true** of that model and veripb is *right* to accept it. Moving the
  facts into the store fixes them, and six new factless controls are now rejected.
- The five `pol` builders are weakened by something moving facts cannot fix: **a `pol`
  states a derivation, not a claim.** veripb recomputes the expression and accepts any
  well-formed one, so deleting a summand does not make a false line — it makes a weaker
  constraint, validly derived. **A factless control on a `pol` is impossible**, whatever
  holds the facts. That is now M1-T51: `Writer` exposes no rule stating what a step
  *concludes*, so every `pol` guard in the suite is a shape pin, and the code says so
  rather than implying more.

`build_ne_conflict` — the one scene that never posted a pin — was the only one already
sound. D-0032 restated as a controlled experiment.

**M1-T50 is a real defect and the thing to read next.** When a bound comes from a
*decision*, the explanation is `Trivial`, and `justify.ml:288` resolves `Trivial` to
`ctx.model_id ()`. So `linear.ml`'s `Combine` emits `pol <own row> <own row> +`: it
derives twice the propagator's own row where the fact should be. The proof step does not
say what the explanation says. I confirmed this by reading the three lines rather than
trusting the scene. It is invisible today because a `pol` has no claim to check and
`search.ml` discards the id — which is precisely the kind of "harmless" that M1-T44 turned
out not to be. Routed to agent-rootfix as a lead, explicitly not as a mandate.

**A test can be commutative and useless at once.** Two of M1-T33's deliberate breaks came
back *green* first, and the agent strengthened the tests rather than softening the
finding. With `mul`'s inner carry dropped, the routine computes a convolution mod 2^30 —
which is still **symmetric in its operands**, so pinning it by commutativity
(`A*B - B*A = 0`) is provably blind. What sees it is the same product reached by two
*factorisations*: `6*M - 2*(3M) = 0`. Worth remembering the next time a commutativity
check looks like enough.

### Fourth wave fully merged and released (orchestrator, 2026-09-16)

Five agents, all merged. Gate on master: **30 models, 0 failures; 239 matrix checks;
width lint green; `make check` rc=0.**

**The day's most important result is M1-T44**: a correct `=====UNSATISFIABLE=====` whose
proof the checker rejected, found by the M2-T11 fuzzer, and fixed at the cause rather than
the symptom. `Domain.set_lo` settles past holes, so a recorded bound can be strictly
stronger than what its own explanation derives — the premise `linear.ml` relied on was
false and had never been written down. It is written down now: **I-X9** and **D-0035**.
Two things about the diagnosis are worth imitating. The rival explanation ("the route is
wrong") was *refuted* — the three rows cited are jointly satisfiable, so no re-routing
could ever have closed them. And the tempting narrow fix (discriminate on `0 >= k`) was
declined because it would leave the explanation still lying about what the bound rests on,
and `Explanation.lits` feeds M2-T3 conflict analysis, where that becomes **unsoundness**.

**M2-T5's measurement matters more than its code.** With the wake mask deliberately made
unsound, **all 29 models passed** — I reproduced it. The mask never fires on the suite at
all (`masked = 0`, 970 propagator runs, 1210 wakes), because no `Domain.Holes` change
occurs anywhere. So the mask's entire value and entire risk are in the future, and the
`BAGUETTE_DEBUG` I-P2 check is its only instrument. D-0034 settles the design question the
agent put to me: a trigger is a property of what a propagator **reads**, and
`Propagator.consistency` is a promise about what it **writes** — the two coincide today by
audit, not by construction, so the derivation is a stopgap with a named expiry condition.

**The memory problem is now enforced rather than requested.** Three binaries died at the
ceiling in one day, all the same shape: a wide declared domain. `make` and the scripts
apply `ulimit -v 4000000`; `CLAUDE.md` carries the rule; and
`scripts/check_test_widths.sh` lints the syntactic tell in the gate, with a self-test that
runs **first** so the guard re-proves it can fail before it is trusted to pass. Both its
own bugs were caught by running it against the line it exists to catch — the first draft
was waved through by its own `~lo:0`, and the second fired on a *comment* explaining the
trap. Still open: a bare `dune runtest` is uncapped (M1-T53), and a real width cap in
`declare_int` is normative (M1-T54).

Counting instances of the signature failure mode is getting hard to keep straight, and the
number matters less than the habit. This round produced at least four more — the bench
self-check that exited 0 on the worst possible failure, two checks in the proof layer that
could not see their own subject fail, and both drafts of my lint. **Every one was found by
performing the break, and none by reading the code.** That is the habit to carry forward.

### M1-T47 released (orchestrator, 2026-09-16)

I wrote this task's brief around "one accumulator at `writer.ml:402`, the single funnel
every rule goes through". **That premise was wrong, and the agent measured it rather than
following it.** Three writes bypass `line`, and the one that matters is `always_comment`:
under format 3.0 — the default since D-0025 — every level marker in every proof goes
through it. Taking the brief at face value under-counts emission by **46%** on
`width_sat_depth`, with no symptom at all; the column would simply have been wrong by
about half on the one model it matters on.

A second trap is worth carrying: a timer wrapped around `line`'s *body* does not measure
the write, because `Printf.fprintf` returns a closure that consumes the format's remaining
arguments after `line` has already returned. It does not read zero — it reads **18% low**,
which is far more dangerous than zero, because a plausible number invites no scrutiny.
Driven to 200 kB lines the same two wrappers report 283 µs against 25,128 µs.

**The answer is less dramatic than M1-T28 implied, and that is the useful part.** Emission
inside `search` is 7.7% of `width_sat_depth` and 2.3% of `width_root_unsat`. The proof is
still the expensive half of this solver — 39% of `inmain` on the heavy model — but M1-T35
had already separated nine tenths of it into the `.opb` phase. What was fused was small.

Two things about how the numbers are published set a standard worth keeping. `emit` is a
**lower** bound and `propag` an **upper** bound, because rendering (`Pol.to_string_cited`,
`Opb.constr_to_string`) happens at the call site before the writer is entered — so the
fusion is not gone, it moved, and the labels say so. And the instrument's own cost is a
**column**, not a correction folded silently into the numbers: `Sys.time` costs 0.65–0.77 µs
per read, about as much as its own granularity, so on `width_sat_depth` 350 µs of the 805 µs
`emit` is the clock. Publishing that raw would have been wrong by 1.8× with nothing in the
number to say so. Calibration is min-of-nine bursts, because a single burst ranged 836–1871 ns
across five runs and would have swung the published correction by 2×.

`bin/main.ml` was unowned this round and the agent changed it, keeping it in one commit so
it could be routed or reverted whole. Reviewed and kept: the four new rows are deliberately
outside `phases`, so `inmain` still equals the sum of the phases exactly.

### M1-T31 + M1-T50 released — and the fifth wave closes the round (orchestrator, 2026-09-16)

The ambient row is gone, and gone in the strong sense: `Justify.ctx` has no field that
could hold one and there is no constructor meaning "the current row", so it is a **type
error** rather than a guarded runtime path. `bin/main.ml`'s failing `model_id` thunk is
deleted because there is nothing left to guard.

Two things to carry forward.

**The fix was a mislabel, not a rendering bug.** `Trivial` said "the model constraint
itself justifies this", which is simply false of a decision — a decision is an assumption
the search made. Once the reason says that honestly, the doubled `pol` citation cannot be
written: a decision has no constraint id and structurally cannot have one (D-0009), so the
term is weakened out of the row while its bound literal still reaches the trace line.
Dropping that literal would have reproduced the I-P5 failure `int_ne` shipped between
M1-T9 and M1-T17, and the agent kept it for exactly that reason.

**The blind spot is the more valuable half.** Pushing the *wrong* decision literal —
`lit` instead of `Lit.negate lit` — left **the entire suite green**: 30 models, every unit
binary. Nothing read the literal, because the `pol` weakens the term away without it and
the trace fact is computed from the store. That is this project's signature failure mode
again, and it was found only by performing the break. `test_matrix.ml` now walks the trail
on every propagation and checks at each level start that the reason names the variable
that moved, in the direction it moved, with the recorded bound entailing it — `>=`/`<=`
not `=`, because a settle can strengthen it (I-X9). The same break now reddens 13 checks.

**Where the honesty was needed and given**: `Justify.emit` on a `Decision` still *raises*.
The fully type-level form needs a trail-reason / emittable-derivation split, and all three
routes to it leave the task's file set — `Store.outcome`'s `Conflict of Explanation.t`
alone drags in ~74 test call sites. The agent said so instead of describing a raise as a
type error, which is the report I wanted.

I also narrowed **I-X9**, which I had written unconditionally this morning: it holds where
an explanation is emitted as a `pol` at all, and a bound resting on an assumption is
justified by its trace line instead. D-0018 point 2's per-push `pol` path and M2-T3 both
reach that exception.

### Wave six closed (orchestrator, 2026-09-17)

Five sessions, all merged, gate green at **1431 unit checks / 252 matrix checks / 34 models,
peak RSS 36 MB**. M1 is down to eight open rows, none of which is a known-false statement in
the code. Four things to carry forward.

**The most valuable output of the wave was a premise being wrong, twice.** M1-T51 asked for
a new `e`/`ia`-style rule in the writer; no new rule was needed, because `ia` and `e` exist
in *both* checkers and PROOF-FORMAT §2a had simply never listed them. M1-T56's blocker was
that "no order literal states an interior hole"; a claim never had to *be* a literal. In
both cases the task had been sized against the premise rather than against the problem, and
in both cases the agent that checked the premise finished faster than the brief expected. The
lesson for dispatch: state the premise *as* a premise, and say it may be wrong.

**The standalone-RUP property is gone, and that is D-0039.** A settle line cites the holes
the settle crossed, so it is RUP against the `.opb` *plus earlier trace lines*, not against
the `.opb` alone — measured, six of eight lines standalone-valid on
`trace_settle_holes_sat`, two refused. Not a soundness loss; VeriPB checks each `rup` against
the database as it stands. But it makes deletion order load-bearing (**I-S4**), and I-S4
holds today by an argument about levels that **does not cover M2-T3's learned clauses**.
Whoever starts M2-T3 should read I-S4 first.

**M1-T60 is the row I would read before anything in M4.** Asked to exhibit a
decision-at-a-hole that veripb rejects, agent-search3 could not, and found the reason: every
hole M1 can punch is punched by a disequality whose `.opb` rows unit-propagate the exclusion,
given bounds that are themselves on the page. A whole family of proofs has been verifying
because of a property of the *encoding of the constraints that happen to exist*, stated in no
document — and that is also why M1-T57's false line survived ~111k runs. `all_different`'s
Hall-interval prunings remove values with no disequality row behind them, so M4-T1 ends it.

**Two of the round's corrections were to my own dispatch, not to the agents' work**, and both
were the same mistake: scoping a file set so tightly that the task could not close. The heap
guard landed in two binaries and missed `test_prop.exe`, the one that actually reached
14.9 GB; and `MEM_GUARD_DEMO` installed a guard of its own, so it never tested the installed
one. All fifteen binaries now announce arming under `BAGUETTE_TEST_HEAP_CAP_ANNOUNCE`, which
is checkable in a run rather than argued. When a task's whole point is coverage, the file set
has to include the thing that was uncovered.

### Wave seven closed (orchestrator, 2026-09-17)

Three sessions plus two rows I took myself. Gate green at **1485 unit checks / 252 matrix
checks / 34 models, peak RSS 54 MB**, and `BAGUETTE_DEBUG=1` clean. **M2-T7 is done, so
M2-T8 -> M2-T9 -> M2-T3 is unblocked** — that was the point of the round.

**Both agents that were given a premise found something wrong with it, and that is now the
pattern rather than the exception.** Wave six had two (M1-T51 needed no new rule; M1-T56's
"no order literal states a hole" was false). This round M1-T60's *mechanism* was wrong in
my own framing: I wrote that Hall pruning "removes values with no disequality row behind
it", and bounds-consistent Hall pruning removes nothing — it pushes a bound out of a
saturated interval. An invariant phrased about holes would have let M4-T1 through silently,
which is the exact failure the row existed to prevent. **Dispatch premises as premises.**

**Read D-0040 before starting anything in M4.** It says `all_different` does *not* force
the direct encoding — Hall's reason is a sum of n disequality rows and D-0027 already
permits a cutting-planes justification, so the obligation is an explicit `pol` ahead of the
trace line and no encoding change. M4-T2 and M4-T3 *do* force it, by D-0019 point 3's own
test. M4-T4b breaks it more basically: the `.opb` carries no row for a product at all.
Paying for the direct encoding when a `pol` would do would be expensive in exactly the way
D-0028 measures.

**I-S4 is still unchecked and M2-T7 deliberately did not change that.** `entry.prop` gives
a future check its material, but the gap is about *levels*, not identity. Whoever takes
M2-T3 owes it: a learned clause citing across levels is precisely the case I-S4's
level-discipline argument does not cover, and `Trace` already has `Store.level_of_index`.

**Two process notes, both from being caught out rather than from reading code.** The
stale-binary trap is now in CLAUDE.md because it caught two of us on one day — a broken
attribution read 34/34 green, and my own before/after artefact comparison came back
byte-identical because the `dune` call had failed and both sides ran the same binary. A
comparison whose two sides used one binary is not evidence of no change; it is no evidence.
And M1-T64: `make fmt` auto-promotes, so the gate silently rewrites unformatted files
instead of refusing them — which is how I came to commit another session's formatting debt
inside an unrelated commit, and how two sessions each spent attention reporting the same
two files.

Remaining in M1: eight rows, none a false statement in the code. The next construction is
**M2-T8** (interface v2, D-0026), now unblocked and the precondition for M2-T3, M3-T4 and
M4.

### Post-M2-T8 verification the merge did not include (orchestrator, 2026-09-17)

M2-T8 rewrote justification emission, so I ran the mutation harness against the merged
tree rather than assuming `make check` covered it — the harness is the only thing that
judges whether a derivation is *load-bearing*, and it is not part of the gate's own
argument. **44 mutation checks, 0 FAIL**, and crucially the lanes are asserted to have
fired: `triple_unsat` 6, `lin_unsat` 6, `branch_trace` 4, `chain` 4, each with an explicit
"every lane this instance declares was run" check, plus four meta-checks that the harness
cannot pass vacuously (a mutation with no site reports not-applicable; an unknown mutation
name is an error; a lane whose honest proof does not verify fails on the control).

Two lanes correctly report `xslack` rather than passing: `lin_unsat`'s refutation closes
at `0 >= 2`, one unit wider than a contradiction needs, so a one-unit coefficient
perturbation still closes it. That is measured and registered so the slack is reported on
every run rather than quietly absorbed — the `pol` lanes gate on `triple_unsat`, whose
margin is one.

Worth repeating for whoever lands M2-T3: *"44 ok, 0 FAIL"* would have been true of a
harness in which **no lane ran at all**, which is a failure this project has actually had.
Check the per-instance lane counts, not the total.

### Wave nine closed (orchestrator, 2026-09-17)

Three sessions, all merged. Gate green at **1625 unit checks / 252 matrix checks / 34
models**, `BAGUETTE_DEBUG=1` clean, peak RSS 55 MB. **M1 is down to two open rows**, and
`lib/core` is free. **M2-T3 is the next task and it should get an exclusive run.**

**The wave's shape was chosen to make that possible**, and it worked: M2-T3's three
preconditions are closed rather than pending. M2-T9's index exists; I-S4 is a **measured**
check instead of an argument; and the I-X6 concern on `explain_cross_conflict` turned out
to be stale and is now structurally impossible (the function takes no store).

**Two of the three premises I dispatched were wrong, and the agents corrected them.** That
is now the pattern rather than the exception — five instances this week. `explain_cross_conflict`
read nothing live; M1-T63's `linear.ml` citation had been deleted by M2-T8. I also closed
M1-T62 without dispatching it, because M2-T8 had silently killed both halves of its premise.
**Check the premise before you spend a session on it.**

**M1-T66 is the row to read before M2-T3.** With `Search.bridges` disabled, 34/34 models
pass and exactly **one** unit check reddens — M1-T55's own text assertion. I verified that
myself. It is I-X10's phenomenon again: the proof rests on the encoding's own rows, so the
bridge is correct and its necessity is unobservable. M2-T3 is when that stops being fine,
because a learned clause citing across levels is precisely what I-S4's level argument does
not cover. **Do not delete the bridge on the strength of that row** — the task is to make
its absence observable by something other than a text pin.

**D-0038 is resolved as D-0043**, and how it resolved is worth keeping. I held the record
until M2-T9 reported, because I had asked that session for evidence. Two unrelated
consumers then turned out to need the same missing value — M2-T8's `Reason.fact` already
*is* a bound claim, and M2-T9's index cannot key a `pol` at all, because a `pol`'s content
is computed by the checker. One use is a feature request; two independent ones are a type
that is absent.

**Two reporting traps caught sessions this week and both are now in CLAUDE.md.** `dune
runtest` without `--force` re-runs only what changed, so a session reported "938 ok"
against a 1576-check suite with no failures and nothing that looked like an error. And
`dune runtest` does not build `bin/main.exe`, which produced a byte-identical artefact
comparison for me and a green 34/34 for a deliberately broken change. **Hash the binary
when you compare, and pass `--force` when you report a count.**

---

**2026-09-18 — orchestrator-plan (M2-T3 plan, docs only)**
Split M2-T3 into ten rows, `## M2L` in `docs/ROADMAP.md`, and wrote **D-0044**. The
architecture decision is that the **learned-constraint type is a PB inequality and a clause
is its degree-1 case**, so starting with clauses stages the work without committing to it.
The reason that is free *here* is D-0028: our order encoding is eager, so a clause over
order literals already **is** a PB constraint over the same 0-1 variables — no conversion,
no auxiliary variables, no fallback cliff. Pumpkin's LLG reports the opposite situation as
its largest single cause of failed linear analysis, because it deliberately does not mint
0-1 variables for atomic constraints. **That argument is `argued`, not `measured`**, and
M2-L1's test (b) is the one that converts it: if a degree-1 `Learned.t` does not propagate
exactly as `Bool_clause` does, D-0044's central claim is wrong and the staging in M2-L3
must be revisited. Do not let that test be quietly weakened.

Three things the next session should know before starting M2-L0. **D-0043 is DECIDED and
unimplemented**, and its own record forbids folding it into M2-T3 — so it is M2-L0, its own
row, and it is a precondition of **Phase 3 only** (M2-L5 onward), not of the clause path.
**Division and `roundToOne` are already expressible** with `Weaken` + `Combine (summands,
divisor)`; saturation is not, because `Explanation.t` has no `Saturate` constructor even
though `Writer.Pol.saturate` already emits ` s` — that gap is M2-L7 and needs its own
decision record. And the `## Starting M2-T3` section below is **still current**: nothing in
this plan supersedes its preconditions, its three things-that-will-bite (I-S4, M1-T66,
I-X10/D-0040) or its baseline numbers.

External fact worth not re-deriving: Koops et al., *Practically Feasible Proof Logging for
PB Optimization* (CP 2025) log RoundingSat's and Sat4j's **full** conflict analysis in
VeriPB at median 2.7% logging overhead and median 1.43x checking-to-solving. Read their
§5–6 before designing M2-L6's emission path — partial weakening before a non-normalised
division, and merged adjacent weakening steps on `pol` lines, are both things we will
otherwise rediscover.

Gate at close: `check: ok`, 34/34 models, 252 matrix checks, no FAIL lines. Docs-only
change, so the 1625/102-artefact baseline is unchanged by construction rather than by
measurement.

**2026-09-18 — orchestrator-plan, amendment to the above**
Asked whether 1UIP is right here, and it is not a settled default. The theorem behind it —
first assertive clause gives the highest backjump — is a **SAT** theorem and Le Berre et al.
(arXiv 2107.13085) show it does **not** hold for PB constraints, which propagate by slack
and so can be asserting while carrying several conflict-level literals. M2-L2's test (b) had
written the 1UIP rule as a general invariant of the cut; it is now scoped to the clause path,
and the stopping criterion is a named component like the reduction rule. **The heading below
still says "clause learning (1UIP)" — read it as the clause path only.** Also recorded: the
cut choice is proof-free on the clause path (one `rup`, no intermediate lines) and sets proof
size on the PB path (every step a `pol` operand), so the two paths pull opposite ways and
M2-L8 is what decides it. Gate not re-run; docs-only amendment on a tree whose gate was green
an hour earlier.

## Starting M2-T3: clause learning (1UIP). Read this section first.

Written 2026-09-17 at the close of wave nine, for whoever picks up M2-T3. It is the next
task, it is the largest one left, and **it should have `lib/core` exclusively** — do not
run a second session in there beside it.

### Its preconditions are closed, deliberately and in order

D-0011 said the trail's missing propagator identity "should be closed before M2-T3 starts,
not during it". That principle was applied to all three:

- **M2-T7** — every trail entry names the instance that made it (`entry.prop`, **I-T4**),
  checked always-on by `Engine.check_attribution`, not under `BAGUETTE_DEBUG`.
- **M2-T8** — D-0026's split. One `Reason.justified` per mutator, so I-P4 and I-P5 are one
  obligation. `linear.ml`'s per-pruning trail scan is gone.
- **M2-T9** — `Justify.ctx.stated`, a clause → defining-line index.

### What you have that earlier sessions did not

- `Reason.owners` walks a reason's **variables without materialising a literal**.
- `Store.lo_support` / `hi_sup` resolve the entry that established a bound in **O(1)**,
  maintained by `apply` and restored by `undo_to`.
- `entry.prop` resolves an entry's reason *constraint* — you no longer need to keep
  explanations alive across levels to know what caused a pruning.
- `Reason.justified` holds reason and justification as **one value** across a backtrack.
- `Store.conflict` is the single construction point for a conflict (`c_prop`, `c_why`,
  `c_reason`).
- `Justify.defining_line` / `defining_lit` for a line whose claim `Justify` knows.

### Three things to read before writing code, and why each will bite

1. **I-S4.** A cited hole line must outlive the line citing it. It holds today by an
   argument about the level discipline, and that argument **explicitly does not cover a
   learned clause citing across levels** — which is exactly what 1UIP produces. M2-T9 made
   I-S4 *measured* rather than argued, and left the level half checked on the edge you are
   about to build. **This is the invariant your task is most likely to violate.**
2. **M1-T66.** With `Search.bridges` disabled, 34/34 models pass and **exactly one** unit
   check reddens — M1-T55's own text assertion. Verified twice, independently. So the
   proof's soundness for a hole split currently rests on the encoding's own rows
   (**I-X10**), not on the bridge, and nothing observes the difference. Do not delete the
   bridge on that basis; know that you cannot rely on the suite to tell you if you break it.
3. **I-X10 and D-0040.** Every M1 pruning follows from a **single model constraint**. A
   learned clause does not — it is the first thing in this solver that will rest on several.
   D-0040 is the precedent for what that costs: derive it explicitly with a `pol`/`ia`
   ahead of the line that uses it. The closure gate in `test/unit/test_trace.ml` classifies
   every module in `lib/core/prop/`; if learning introduces a new pruner, that gate fires
   until you classify it, which is deliberate.

### What is NOT available, so you do not go looking

- **`defining_lit` has no caller.** Giving it one needs a *citation* slot in `Combine`/`Cut`
  — D-0009's other, separate missing field. Not done, not decided.
- **D-0043** (the conclusion as a `Reason.fact`) is resolved but **not implemented**, and
  the record says explicitly it is **not a precondition of M2-T3 and must not be folded
  into it**. It pairs with M2-T9's follow-up and M4-T1.
- **The general I-X6 exposure remains** on the justification half: a thunk can still close
  over the store, and only discipline stops it. The reason half is type-safe
  (`Reason.lits` takes no store). `explain_cross_conflict` is settled and now takes no
  store at all.
- **M2-T8's agreement check catches a reason naming the wrong *variable*, not the right
  variable at the wrong *value*.** Do not read a green debug run as more than that.

### Process, from three sessions that lost work this week

- **Commit as soon as it compiles.** One session committed nothing across a long run and
  lost it all; I salvaged its tree by hand into a branch marked DOES NOT BUILD. The one
  that committed frequently lost nothing.
- **`dune runtest` does not build `bin/main.exe`**, and without `--force` it re-runs only
  what changed. Both traps caught someone this week. Hash the binary when you compare
  artefacts; pass `--force` when you report a count.
- The gate is now `fmt-check + build + lint + determinism + test`. It **verifies**
  formatting rather than fixing it, and the determinism check requires two runs of the same
  binary to produce byte-identical `.opb`/`.pbp`/stdout — relevant to you, because a
  learned-clause database iterated in hash order would move bytes run to run.
- **Baseline to beat:** 1625 unit checks, 252 matrix checks, 34/34 models, 102/102
  artefacts byte-identical, peak RSS 55 MB.

### The volume check on M1-T45 is done, and it passed

agent-search4 asked for a heavy fuzzer sweep to confirm the shapes its guard removal
reclaimed survive at volume. Run at the close of wave nine: **120 seeds** of
`test_random.ml`, each 200 cases x 8 branching orders, so roughly **192,000 solver runs**.
**Zero proofs rejected.** So the hole guard's removal is verified beyond the 40 hand-forced
shapes, and M2-T3 can build on it.

Four of the 120 seeds did report a failure, and it is **not** a soundness one — it is
`test_random.ml:969`'s *coverage* assertion, which requires the generator to have reached a
disequality pruning that moves a bound and simply does not on those seeds. Recorded as
**M2-T13**, because a coverage assertion that depends on the seed is flaky by construction:
the gate is green only because the default seed reaches the shape, so anyone setting
`BAGUETTE_RANDOM_SEED` has a ~3% chance of a red that reads like a real rejection — in the
one file whose entire purpose is that a rejection under an unusual seed is a finding.

### After it

**M2-T4** (learned-clause deletion and its matching `del`) follows directly, and
**M1-T29**'s pair spelling is what its deletion will use. M2-T6 and M2-T10 also want
`lib/core` and should queue behind, not beside.

### Worktree cleanup (orchestrator, 2026-09-17)

**All 34 worktrees under `.claude/worktrees/` are removed**, and 20 auto-named
`worktree-agent-<hash>` branches with them — those exist only as worktree scaffolding, so
with the directory gone they name nothing. Every one was verified before removal: merged
into `master`, no unique commits. `git fsck` clean afterwards, gate green.

**Two commits were deliberately preserved and are still reachable.** Neither is merged, and
each is kept on its branch:

| Commit | Branch | What it is |
|---|---|---|
| `474a05f` | `wave8-del` | M1-T29's **deliberate break** — removes the trailing `del id`, leaving the run's last id live, and reddens exactly the three checks that assert the pair. Builds. Evidence, not unfinished work. |
| `97d982e` | `worktree-agent-a5a5eb6cbb5505ceb` | agent-bool's M2-T1/M2-T2 WIP, **DOES NOT BUILD**. Dead work — both rows landed by another route — but it is the only copy, so it is not mine to discard. |

Three files were lost with the directories, all checked first and all genuinely
irrelevant: two scratch helpers in `agent-a28d6d45973af8420` that self-declare "Local
helper for this worktree session. Not for committing" and hardcode paths into their own
worktree, and a `scripts/check_fmt.sh` in `agent-del` that was **my** leftover from testing
the M1-T64 worktree fix, byte-identical to master's.

**What I did NOT do**, so the next session does not think it was an oversight: the twelve
merged `wave6-*`/`wave7-*`/`wave8-iface`/`wave9-*` branches are still there. They are safe
to delete — every commit is in `master` via a `--no-ff` merge that names the task — but I
created them deliberately and with meaningful names, which is a different category from
harness scaffolding, and pruning them was not what was asked. They will accumulate about
three to five per wave, so prune them when it starts to cost something.

**2026-09-18 — M2-T13, agent-flaky.** The five `test_random.ml` coverage checks
(`!deep/!root_conflict/!div/!rem/!ne_bound > 0`) were seed-dependent; fixed by extracting
the per-case solve+check logic into `process_case` so a bounded top-up phase (cap 4000,
same seed's PRNG stream) can keep drawing cases until every shape appears, and by routing
those five assertions through a new `coverage_check` that prints `COVERAGE-GAP (...NOT a
soundness failure)` on failure instead of `FAIL`, so it can never be misread as a proof
rejection. Verified with a 130-seed sweep (`BAGUETTE_RANDOM_SEED=1..130`, default
cases/orders): 0 failures, and the top-up genuinely engaged (not a no-op) on seeds 21, 53,
68, 89 — most likely the four the 2026-09-17 sweep found, though that sweep used
`BAGUETTE_RANDOM_CASES=200 BAGUETTE_RANDOM_ORDERS=8` and this one used the defaults, so
the seed numbers are not a certain match, just the same order of magnitude (4-ish of 120).
**Next session**: if you touch this file's counters or `orders_for`, re-run the same sweep
— the top-up loop is cheap when coverage is already reached (0 extra draws on ~97% of
seeds) so it should not show up in normal runtimes.

### Added 2026-09-18, after the briefing above was written: read D-0045's addendum before M2-L1

The briefing above is still current in every respect. This is one thing it could not
contain, because it was found the day after.

**A learned constraint is deleted by the backjump that follows learning it, automatically.**
`Writer.fresh` (`lib/proof/writer.ml:547`) tags every id it hands out with the writer's
**current** level — `Hashtbl.replace t.tags t.next_id t.level`, with **no `~level`
argument** — and `wipe_level l` (`:764`) deletes every id tagged at level `>= l`.
`set_level` (`:593`) is the only lever that moves `t.level`, and it is also *"the only
thing that writes a level marker"*, so reaching for it mid-derivation puts a `% level 0`
in the middle of the derivation.

That collides head-on with **M2-L3's own emission rule**, which says to emit the learned
clause's derivation *while the trace lines supporting it are still live* — i.e. before the
wipe, which is exactly where `fresh` will tag it for deletion. The two cannot both hold
through the current API, so **M2-L1 most likely owes `lib/proof/writer.ml` a new entry
point** (an id allocated at a chosen level) rather than a call-ordering trick in
`lib/core`. Cheap in M2-L1; expensive once three rows have each worked around it.

**It must hold under both formats.** Under 2.0 `t.tags` is not maintained at all (`:876`)
— the checker holds the level stack and `w l` retires against it — so a fix that only
adjusts the 3.0 table would be green under 3.0 and wrong under 2.0. That is the M1-T46
discipline applied to a data structure instead of a message.

Read off the code, **not measured**: no learned constraint has ever been emitted. The
prediction to falsify is stated in D-0045 — emit one at the conflict level and the
backjump deletes it.

### M2-T13 verified independently by the orchestrator, 2026-09-18

agent-flaky reported the four top-up seeds as *likely* analogues of the four the
2026-09-17 sweep found, because the two sweeps used different case/order counts. That
hedge was correct to make and it is now unnecessary — measured rather than argued:

| seed | pre-fix binary (`62962b8`) | post-fix binary | top-up draws |
|---|---|---|---|
| 21 | **FAIL** | pass | 9 |
| 53 | **FAIL** | pass | 5 |
| 68 | **FAIL** | pass | 27 |
| 89 | **FAIL** | pass | 14 |
| 3 (control) | pass | pass | 0 |

The pre-fix binary was built from `62962b8` in a throwaway worktree and **checked to be
md5-distinct** from the fixed one before either was run — CLAUDE.md's rule that a
before/after whose two sides used the same binary is not weak evidence but *no* evidence,
which has caught this project twice. The control seed matters as much as the four: it
passes on both binaries, so the old one was not simply always-red.

**The defect, in the old binary's own words**: `FAIL the generator reaches a disequality
pruning that moves a bound`. A bare `FAIL`, in the one file whose whole purpose is that a
red is a soundness finding worth chasing. That is what the new `coverage_check`'s
`COVERAGE-GAP (generator problem, NOT a proof rejection, NOT a soundness failure)` replaces
— and it still increments `failures`, so the check was re-worded, **not weakened**, which
was the thing to get wrong here and was checked rather than assumed.

## Wave ten handoff, 2026-09-18 (orchestrator)

Three sessions, all merged. Gate green: **1723 unit checks** (1625 + 34 + 64, and the two
agents' reported additions reconcile exactly), 252 matrix, 44 mutation, **34/34 models**,
determinism byte-identical, peak RSS ~36 MB against a 55 MB baseline. Everything is pushed
to `origin` (`git@github.com:ArthurGontierPro/baguetteCP.git`) — see "Pushing" below.

### What the wave actually bought

**M2-L0 closed M1-T51's adoption gap.** `Writer.pol_concluding` and `Writer.implied` sat
with no caller in `lib/` since M1-T51; they have one now. The defect M1-T51 *measured* but
could not *fix* is pinned in both polarities: a `pol` truncated to derive something
strictly weaker is **ACCEPTED** bare and **REJECTED** once the conclusion is stated.

**M2-L2 produced the cut without learning anything**, which was the point of splitting it.
Its criterion is a record carrying its own postcondition, so the 1UIP rule is asserted
**about the criterion** and never about the cut — D-0044's amendment made that call and
this row honoured it. There is an explicit check that `one_uip`'s postcondition is *false*
of `conflict_side`'s two-conflict-level cut, which is the assertion that would have
reddened for M2-L6 had it been written one altitude up.

### Three findings to carry forward

1. **The derived bound and the trail bound are different honest numbers.** `Domain.set_lo`
   settles over holes (I-D2), so a propagator told `x >= 2` over `0..9 \ {2}` lands the
   trail at 3. A conclusion check demanding "exactly the new bound" reddens three *real*
   scenes. `conclusion_holds` admits exactly that window and checks it value by value.
2. **`Store.lo_support`/`hi_support` is not always the right edge**, and M2-L3 must know
   this. A reason's facts are frozen at older values, so if the bound moved again the O(1)
   array names a *later* entry and a naive walk runs up the trail instead of terminating.
   `Analysis.support_of ~before` tries O(1) and falls back to a downward scan;
   `o1_supports`/`scanned_supports` expose the split so a regression is visible.
3. **A break that reddens nothing is still a result.** M2-L2's second `entry.prop` break
   changed nothing, because stamping one high can land on another instance that *does*
   watch the variable — the identical blind spot `Engine.check_attribution` has. It is not
   invisible: `antecedents` then names the wrong instance twice, and that difference is
   asserted. Reported rather than smoothed over, which is the behaviour to keep.

### I got two premises wrong, and both were caught by the agent, not by me

The wave-nine handoff says "check the premise before you spend a session on it" and counts
five instances that week. Add two:

- I marked `lib/core/search.ml` and `lib/core/store.ml` **read-only** for agent-concl, when
  both hold `Reason.because` call sites — so the required-field route could not compile.
  Caught by me minutes after dispatch and amended in flight.
- I briefed agent-cut that `Store.remove`/`fix` "silently record `no_facts`". **False since
  M2-T8**, and the wave-nine handoff already said so — but the *cross-session request row*
  still carried the dead claim, and the row is what I read. That row is now marked STALE.

The lesson is narrower than "check premises": **a superseded claim that lives in a request
row outlives the handoff note that superseded it**, because briefs get written from the
request table. When you kill a premise, strike the row, not just the note.

### Pushing (new, 2026-09-18, at the user's instruction)

A remote was added mid-session and **everything is now pushed to it**: `main`, all three
`wave10-*` branches, the twelve merged `wave6`–`wave9` branches, and — most importantly —
the two branches that are the **only copies** of their work, `wave8-del` (`474a05f`, M1-T29's
deliberate break) and `worktree-agent-a5a5eb6cbb5505ceb` (`97d982e`, DOES NOT BUILD).
**Keep pushing.** The standing instruction is to commit *and push*, so that a dead machine
costs nothing. Push agent branches too, not just `main` — in-flight branch work is exactly
what this project has lost three times.

This also explains the `master` -> `main` rename recorded above: the remote is `origin/main`,
so the local branch was renamed to agree with it. Not a session doing something odd.

### Next

**M2-L1** is the critical path and it does **not** start clean — read **D-0045's addendum**
first. `Writer.fresh` tags every id with the writer's current level and has no override, so
a learned constraint is deleted by the backjump that follows learning it, automatically,
and that collides head-on with M2-L3's rule to derive the clause while its supports are
still live. M2-L1 is where that is cheapest to fix, and the fix must hold under **both**
proof formats. **M2-L5** is unblocked now that M2-L0 is done. **M2-L3** wants `lib/core`
and should queue behind M2-L1, not beside it.

## M1-T66 handoff, 2026-09-18 (agent-bridge)

**What changed.** `Search.bridges` now leaves its derivation behind as data instead of only
as a line in the `.pbp`: a `Search.bridge` record per settle on `stats` (which decision,
which literal assumed, which bound settled onto, which holes the push crossed, and for each
hole the id and level of the line that states it), plus a `Trace.record_citation` per named
hole. `test/unit/test_matrix.ml` gains `bridge_derivation` (the M1-T55 hole split) and
`bridge_across_levels` (the ancestor arm, on a SAT model). Nothing in any emitted proof
changed — the M1-T55 byte pin in `test_engine.ml` is still green and unmodified.

**The honest verdict, and the thing M2-L3 needs to know.** Route 1 — a scene where removing
the bridge makes a checker *reject* — is **not reachable in M1**, and the reason is
structural rather than a failure of imagination. When veripb checks the nogood it asserts
the decisions and unit-propagates, and it reaches the settled bound by two routes the bridge
cannot take away: (1) the hole's own trace line, the clause `x <= v-1 \/ x >= v+1` that
M1-T56 made every interior hole get and that `Trace.emit` puts on the page *before*
`bridges` runs (D-0021 fixes that order); and failing that (2) `int_lin_ne`'s two big-M rows
in the `.opb`, which are in the model file and which no `w` can ever retire — I-X10, and
`Ne` is the only thing in M1 that punches a hole. Measured, not just argued: with `bridges`
made a no-op, `bridge_derivation` reddens *at the derivation* and **veripb still accepts the
proof**. `br_unnamed` was empty in both scenes, i.e. route (1) was available every time.

**So the row stays open**, and what it now owes M2-L3 is one sentence: the bridge becomes
load-bearing the moment a line cites the settle across levels, because route (1)'s support
is level-tagged and route (2) is not a *citation* at all. `bridge_across_levels` is where
that already half-happens today — the bridge is written at the nogood's level, deeper than
the decision it bridges, citing a level-0 hole line — and it is the first I-S4 edge of that
shape the audit has ever recorded. `Trace.i_s4_violations` is asserted empty in both scenes;
when M2-L3's learned clause starts citing across levels, that is the assertion that reports
it rather than the checker several inferences away.

`docs/ROADMAP.md` M1-T66's row still says TODO and should be updated by whoever merges this;
the file was read-only for this session.

### M1-T66 verified independently by the orchestrator, 2026-09-18

agent-bridge's verdict is half positive and half negative, so both halves were checked in a
throwaway worktree off `main` with `bridges` disabled at **all three** call sites (`ignore
(bridges, ...)`, which keeps the build warning-clean without touching the function body):

| with `bridges` disabled | result |
|---|---|
| `test_matrix.exe` | **exit 1, 2 FAILs** — `bridge` and `bridge/ancestor` |
| model suite (binary rebuilt first) | **34/34 pass, exit 0** — veripb accepts every proof |

So the positive half is real: the absence is now caught, and the failure text says what it
is — *"…which is the M1-T66 defect and is NOT a formatting change: the nogood then negates
`x >= 1` having explored only `x >= 2`, and nothing on the page says the one implies the
other."* That is a message the next person can act on, which the old byte pin was not.

And the negative half is real too, which is why the row stays open: **the checker still
accepts.** That is now the fourth independent confirmation (M1-T45, the wave-nine
orchestrator, agent-bridge, me). It is not a gap in anyone's testing — it is I-X10, and
the remaining half of M1-T66 belongs to M2-L3, where a clause first cites across levels.

Note it reddens **two** checks, not the one the agent named; `bridge/ancestor` is the
cross-level one and is the more interesting of the pair for M2-L3.
## M2-L1 handoff, 2026-09-18 (agent-learned)

**The collision was measured before it was fixed**, which is what D-0045's addendum asked
for. One scenario, four runs (broken/fixed x 3.0/2.0), through the resolved checker, in
`test/unit/test_proof.ml`'s `test_learned_survives_the_backjump`:

| | minted at the conflict level | minted inside `Writer.with_level w 0` |
|---|---|---|
| 3.0 (Rust 3.0.2) | **REJECTED** -- "Trying to access constraint with ID 3 that has already been deleted" | accepted |
| 2.0 (Python 2.2.2) | **REJECTED** -- "Rule 6 is trying to access constraint (constraintId 3), that was marked as safe to delete" | accepted |

So the prediction holds exactly as written. The entry point added is **`Writer.with_level
t l f`**, not the `fresh ~level` the record guessed at: under 2.0 `t.tags` is not
maintained and nothing we write to our own table reaches the checker, so the level has to
move *in the proof*. The bracket emits `# 0` / `# 1` under 2.0 and a `% level 0` comment
under 3.0, costs two marker lines per learned constraint, and restores the level even if
the body raises. `Justify.with_level` is the wrapper `lib/core` should call -- the memo and
the M2-T9 claim index both stamp `Writer.current_level`, so they follow for free.

### For M2-L3, the two things worth knowing before you start

1. **D-0044's central claim is converted, and the bet paid off.** A degree-1
   unit-coefficient `Learned.t` over order literals propagates *exactly* as `Bool_clause`
   does on all 27 scenes of a three-Boolean clause -- same conflicts, same domains, with a
   negative control proving the comparison separates a different clause. A learned row is
   instantiated as a **`Linear` instance**; **no module was added to `lib/core/prop/`**, so
   `test_trace.ml`'s I-X10 closure gate correctly never fired. That silence is the bet
   paying off, not a missed check, and `test_learned.ml`'s section (f) records it as a
   measurement.

2. **The boundary, which the roadmap row did not anticipate.** D-0044 is right without
   qualification *in the proof* -- the order literals are real 0-1 variables of the .opb.
   But in the **solver's store** they are not variables at all, so a learned constraint has
   a runtime instance only where its PB row reads back as a linear row over the integer
   variables. `Learned.to_linear_row` is exactly that predicate. It succeeds on a clause
   over `var bool`s (one-rung ladder), on a model row's own expansion (uniform coefficient
   over a whole ladder), and on out-of-range thresholds; it returns **`None` on a threshold
   strictly inside an integer variable's ladder** -- `[x >= 3]` for `x` declared 0..4 is not
   any linear function of x. **A 1UIP cut over integer variables produces exactly those
   literals**, so M2-L3 must expect `None` from its own output and decide what to do: either
   restrict the cut to the representable shapes, or accept that such a learned constraint is
   proof-only until something can propagate it. This is a finding, not a defect in the type.

### Other notes

- `Engine.add` registers an instance after `create`. It requires `inst.id = Engine.next_id
  engine` and says why: `Engine.propagate` indexes its instance array **by id**.
- I-X2 for a learned constraint is **not** discharged by a backjump any more -- that is the
  whole point -- so `Learned.retire` must be called. M2-L4's retention policy owns this;
  until it exists, whoever called `introduce` does. The audit sees a missing delete; it
  cannot see a *double* delete (the second `forget` is a no-op), so `test_learned.ml` counts
  the `del`s in the proof text instead and says so.
- `Learned` builds its `Linear.t` record directly rather than through `Linear.make`, because
  `make` freezes the *current* domains as declared and a learned constraint is born
  mid-search. The declared bounds come from `Encoding.domain`. Confined to `to_linear`.
- Numbers: **1766 unit checks** (baseline 1723), **34/34 models**, determinism clean, fmt
  clean, width lint clean, peak RSS **21 MB** (`test_proof`, the heaviest binary).

## Wave eleven handoff, 2026-09-18 (orchestrator)

Two sessions, both merged and pushed. Gate green: **1781 unit checks** (1723 + 15 + 43),
267 matrix, 44 mutation, **34/34 models**, determinism byte-identical.

**M2-L1 did the thing this project keeps asking for and rarely gets: it measured the bug
before fixing it.** D-0045 predicted that a learned constraint minted at the conflict level
is deleted by the following backjump. It is, in both formats, and the two checkers' exact
rejections are now in the record. The fix — `Writer.with_level`, a bracket — is *better
than the one I proposed*, and for a reason I had already written down and then failed to
follow: under 2.0 `t.tags` is not maintained, so the level must move **in the proof**, not
in our table. A `fresh ~level` would have been green under 3.0 and wrong under 2.0.

**M1-T66 is half done and correctly left open.** The bridge's absence is now observable at
its *derivation*; it is still invisible to the *checker*, and that is structural in M1
rather than a gap in anyone's testing. I confirmed both halves myself.

### The one thing to read before M2-L3

**`Learned.to_linear_row` returns `None` on a threshold strictly inside an integer
variable's ladder — which is exactly what a 1UIP cut over integer variables produces.**
D-0044 is confirmed in the *proof* and bounded in the *store*: order literals are variables
in the `.opb` but not in the store, where `x >= 3` is a question about a domain rather than
a handle. So M2-L3 must choose, deliberately and up front, between restricting the cut to
the shapes that convert and accepting a **proof-only** learned constraint until a
propagator exists. Both are sound. Discovering this halfway through would be expensive.

See D-0044's 2026-09-18 amendment and D-0045's resolution section.

### Two guards that are weaker than they look

- **The `BAGUETTE_PROOF_AUDIT=1` live-set audit cannot see a double delete** — a second
  `forget` is a no-op, so the set is already clean. It witnesses the "at least once" half
  of I-X2 and not the "exactly once" half. **M2-L4 must not rely on it**, since its whole
  subject is a retention policy that may want to delete what a backjump also deletes.
- **`Engine.check_attribution`'s watcher arm does not catch a mis-stamp** that lands on
  another instance which also watches the variable. M2-L2 found it, M2-L1 confirmed it: the
  break is caught by the stamp-vs-runner arm instead. Two rows have now measured this; it
  is a known hole, not a surprise.

### A note on my own dispatches

Three premises of mine have now been wrong in two waves, all caught by agents. The pattern
is not carelessness about the code — it is **briefing from rows that a later note had
already superseded**. When you kill a premise, strike the request row, not just the note.


## M2-L3 handoff, 2026-09-18 (agent-learn3)

Merged as `08cfa83` on `wave12-learn3`. 1833 unit checks (was 1781), 267 matrix, 44
mutation, **35/35** models (was 34 — `backjump_unsat.fzn` is new), determinism green
across 35 models, `check_fmt.sh` clean, peak RSS 10.6 MB (`test_matrix.exe`, the
heaviest). The whole suite was also run green under `BAGUETTE_PROOF_FORMAT=2.0` with
`VERIPB=~/.local/bin/veripb`, i.e. against the Python 2.2.2 as well as the 3.0.2 of
record.

**Read `lib/core/learn.ml`'s header before touching any of this.** The five decisions
below are all argued there at length and none of them is obvious.

1. **D-0044's fork went (ii), proof-only, and it was not a convenience.** (i) would make
   the learned clause a runtime propagator, which is what a 1UIP *asserting* backjump
   needs; with nothing propagating it, a resume at the backjump level re-reaches the same
   fixpoint and re-derives the same conflict, which is a loop. `stats.convertible` counts
   how often `Learned.to_linear_row` would have accepted the cut: **0 of 4** on
   `offset_unsat`, 0 on every integer model. Restricting the cut to shapes that convert
   would have meant learning nothing at all outside Boolean models. M2-L4 has the number.

2. **The backjump does NOT rest on the 1UIP cut.** The levels a 1UIP cut names are not a
   dependency set — a non-root node at level j rests on further facts at levels the cut
   never names — so `Analysis.backjump_level` is the wrong thing to skip a branch on and
   would answer UNSAT on a satisfiable model. `Analysis.analyse` gained `?scope`, and the
   new `decision_closure` criterion resolves every non-root node away at *every* level; the
   levels of THAT cut are sound. The skip rule is then one line and needs no CDCL progress
   argument: a nogood naming no literal of level `lvl` is already false under the decisions
   above `lvl`, so it refutes the sibling too.

3. **M2-L1 did give the entry point the row asks about.** The tension — emit while the
   supports are live, but `Writer.fresh` tags at the current level — is resolved by filing
   every branch nogood at the deepest decision level it names (`Search.filed_at`, through
   `Justify.with_level`) and the learned clause at level 0 (`Learned.introduce`). Nothing
   had to be worked around locally.

4. **I-S4 is discharged, and narrowing it to hole lines would have been a vacuous check.**
   `Learn.supports` reports every line the derivation rests on — the trace line behind
   every entry the cut resolved, not only the folded hole lines — and `Learn.support_check`
   asserts each is live at the moment the `rup` is written. With the break applied
   (derivation after the `w`) the hole-lines-only version reported **nothing**: the hole
   line sits at level 0 and what the `w` takes is the conflict-level bound lines. The
   *outlives* half is argued away rather than waived — a `rup` names no id, so nothing can
   dangle — and `Learn.crossings` reports the crossings as data (1 per learned clause on
   `trace_settle_sat`) because M2-L6's `pol` is the first thing for which they WOULD be a
   violation.

5. **M1-T66 is still open, and this row was the predicted closer.** Re-measured today with
   `Search.bridges` disabled and the binary hashed on both sides: **35/35 models pass and
   no checker rejects anything.** The only reddening is M1-T55's text pin plus M1-T66's own
   two derivation-level assertions in `test_matrix.ml`. A learned clause citing across
   levels did not make the bridge observable to the checker, for the reason M1-T66 already
   recorded: the settle is re-derivable from the hole's own trace line and `int_lin_ne`'s
   big-M rows, and a `rup` is checked against exactly that database. Do not dispatch M1-T66
   again expecting learning to close it.

### Two findings the next session should not rediscover

- **Semantic minimisation fires on NONE of the 35 shipped models** under the normative
  order (`stats.n_min_dropped` is 0 on every one), because `Analysis.add_node`'s
  strongest-per-slot merge has already done it one layer up, on the closure the nogood is
  built from. It does fire under other branching orders — the (a2) break lane is
  `random_order` at a pinned seed, where the Strongest proof verifies and the Weakest one
  is rejected. `test_learn.ml` asserts the idleness too, so the sentence cannot rot.
- **M1-T46's "the two checkers share no substring" does not hold for a RUP failure.** It is
  true of the wordings M1-T46 measured (a non-contradiction; a deleted id). Both checkers
  say "reverse unit propagation" when a `rup` fails. `test_learn.ml` matches
  `is not implied by reverse unit propagation` (3.0.2) and `Failed to show` (2.2.2) rather
  than the shared phrase, which is the least specific thing either says.

### What M2-L4 inherits

`Search.stats.learned_rev` holds every level-0 learned id and `Search.solve` retires them
all, on every path, immediately before the conclusion — that is the whole retention policy
today and it is deliberately the dumbest one. They are NOT retired at the backjump: a
learned clause whose lifetime is a level's has learned nothing. The `BAGUETTE_PROOF_AUDIT`
live-set check still cannot see a double delete, so if M2-L4 adds a policy that may delete
what something else deletes, count `del` lines rather than trusting the audit.

## Wave twelve handoff, 2026-09-18 (orchestrator): M2-L3, and two numbers to keep

One session, merged and pushed. Gate green: **1835 unit checks**, 267 matrix, 44 mutation,
**35/35 models** (one added), determinism byte-identical, peak RSS 10.6 MB. Also green under
`BAGUETTE_PROOF_FORMAT=2.0` against Python 2.2.2.

**The row's own finding is the valuable part**, and it was not in the brief: *the backjump
cannot rest on the 1UIP cut*. The levels a 1UIP cut names are **not a dependency set** — a
non-root node at level j rests on facts at levels the cut never names — so backjumping to
`Analysis.backjump_level` would skip a subtree that nothing had refuted. `Analysis.analyse`
gained `?scope` and a `decision_closure` criterion whose level set is sound. The skip rule
needs no CDCL progress argument: a nogood naming no literal of level `lvl` is already false
under the decisions above it, so it refutes the sibling too.

### I measured the whole suite, and it corrects two claims — one of mine, one of the agent's

Ran `--stats` over all 35 models:

| | |
|---|---|
| models that learn a clause | **18 of 35** (77 clauses total) |
| models where a backjump **skips** a sibling | **1 of 35** — `backjump_unsat`, the model this row added. 2 skips in the whole suite |
| clauses `to_linear_row` would accept | **11 of 77 (14%)**, concentrated in the `bool_*` models, `bool_reif_unsat`, `ne_eq_unsat`, `trace_settle_sat` |

**Correction to the agent's report.** It said `to_linear_row` accepts *"0 on every integer
model"*. That is too strong: `ne_eq_unsat` converts 2 of 2 and `trace_settle_sat` 1 of 1.
The honest statement is that convertibility is **model-dependent and unpredictable at 14%
suite-wide** — which is a *better* argument for fork (ii) than "always zero", because a
feature you cannot predict the availability of is exactly one you must not depend on.

**The coverage caveat, and it is the one to carry.** Exactly **one model in thirty-five**
exercises a backjump skip, and it is the one this row added. Clauses are learned on 18
models, so the *derivation* path is well covered; the *skipping* path rests on a single
instance. That is a thin base for:

- **M2-L4** (deletion policy) — a policy tuned against a suite that backjumps twice in
  total is tuned against nothing. It needs instances first, or it needs to say plainly that
  its measurement is not yet a measurement.
- **M2-L6** (PB analysis) — its fallback-rate instrumentation has the same problem.
- **M2-L8** (benchmark) — same again, and it is the row that would notice.

Adding backjump-exercising models is cheap and is probably the highest-value small task
available right now.

### Still open, deliberately

**M1-T66 is still open and the answer is still NO.** A learned clause citing across levels
was predicted to make the bridge load-bearing. Re-measured with `Search.bridges` disabled
and binaries hashed on both sides: **35/35 models pass, no checker rejects**; only M1-T55's
text pin and M1-T66's own two derivation assertions redden. That is now four independent
measurements of the same negative, two of them mine. The reason is I-X10 and is recorded in
the row.

### A gate failure I caused, and the fix

The merge was pushed before the gate finished — deliberate, since the point of pushing is
not to sit on unpushed work — and the gate then failed. **It was not M2-L3's code**: the
width lint's argument regex had a **space** in its bare-token character class, so in
`agree_on ~name:"x" ~lo:(-1) ~hi:5 l (Learn.minimise l)` the `~hi:` argument matched `"5 l"`
rather than `"5"`, and a width-6 domain was reported as unbounded. Fixed in
`scripts/check_test_widths.py`: an argument is now either a parenthesised expression (which
may contain spaces) or a bare token (which may not). **The self-test was extended in both
directions** — the false-positive shape is a `must_pass`, and the *same shape with a
genuinely wide bound* is a `must_flag`, so the fix cannot have bought its silence by
matching less.

Note what this says about the agent's report: it listed `check_fmt`, determinism and the
suites, and **did not run the width lint**. `make` does not work in a worktree, so the gate
is run piecewise there and a piece can be missed. Worth asking for explicitly next time.

**2026-09-18 — agent-cover, M2-L10**
Added 3 models (`backjump_deep_unsat`, `backjump_bool_unsat`, `backjump_lineq_unsat`) to
cover the multi-level, convertible and non-convertible-via-a-third-propagator-family shapes
a backjump can take; `test_m2l10_coverage` in `test_learn.ml` asserts `skipped > 0` on all
three plus the exact skip count for the 3-level one. All three verified under both proof
formats and both veripb binaries by hand (`scripts/verify_proof.sh`), not just the default
3.0/cargo path the in-process test exercises — worth doing explicitly for any new model,
since nothing in the automated suite checks format 2.0. Next session (M2-L4/L6/L8): you now
have 4 skipping models / 10 skips to tune against instead of 1/2, still thin for a real
retention-policy or fallback-rate measurement — more instances would still help.
## M2-L5 handoff, 2026-09-18 (agent-reduce)

`lib/core/reduce.ml` is new and is the whole of M2-L5. Three things the next session
should know.

**The signature, and what M2-L6 must not do to it.** A reduction is
`{ name; reduce : view -> outcome option; postcondition : view -> outcome -> bool }`;
`view` is `{ row : Learned.t; pivot : Lit.t; falsified : Lit.t -> bool }` and `outcome`
is `{ reduced : Learned.t; weakened; divisor; derive : Explanation.t -> Explanation.t }`.
`derive` is the load-bearing field: it maps the explanation that derives the ORIGINAL row
to the one that derives the REDUCED row, so **M2-L7's saturation plugs in as another
value in `reductions` with `weakened = []`, `divisor = 1` and
`derive = fun e -> Saturate e`, and `analysis.ml` never learns which rule it is holding.**
Do not let M2-L6 pattern-match on `weakened`/`divisor` to rebuild the proof step — those
fields are there to be *inspected* by tests, not to be the emission path. Call `derive`.

**`falsified` is a predicate and this module reads no store**, the same line
`analysis.ml`'s `view` draws, for the same I-X6 reason. M2-L6 owns freezing it at the
moment of the propagation; `reduce.ml` cannot un-freeze it.

**Nothing in `justify.ml` needed to change.** D-0044's table is right: both rules are
`Weaken lits` then `Combine (summands, divisor)`, which `Justify.emit` and
`Justify.emit_concluding` already render. `explanation.ml` was not touched and no
constructor was wanted.

### Two measurements worth keeping

**`Justify.emit_concluding` still has no live caller, and M2-L5 did not give it one.**
Wiring `search.ml` to it would move every proof artefact, which is the orchestrator's
call. But M2-L5's test (c) is now a second independent demonstration that the `ia` is
what makes a *silently weakened derivation* visible: a reduction truncated to a bare
division of an unweakened row derives `v+u+w >= 2` where roundToOne derives `v+u >= 2`,
and it is **ACCEPTED bare / REJECTED stated**, under both checkers. The case for wiring
it is now two rows strong, not one.

**`test_justify.ml` is not green under `BAGUETTE_PROOF_FORMAT=2.0`, and was not before
this row either.** `writer.ml`'s header claims "the whole suite is green" under 2.0.
Measured 2026-09-18: M2-L0's `conclusion_break_opb` (line ~854) hardcodes
`Encoding.write_opb ~labels:true`, so its `.opb` carries 3.0 labels that veripb 2.2.2
rejects at `:2:1: Expected number` — four of its lanes fail for a reason that has nothing
to do with what they test, and its "REJECTED" lane passes vacuously because *everything*
is rejected. M2-L5's own (c) avoids this by using `Encoding.write_opb_for`, which ties
the `.opb`'s labelling to the writer's format, and by running each checker at the format
it can read. **The one-line fix for M2-L0's test is the same call**; it was left alone
because it is M2-L0's row, not this one. Raised here rather than fixed silently.

## Wave thirteen handoff, 2026-09-18 (orchestrator): M2-L5 and M2-L10

Two sessions, both merged and pushed. Gate green on `main` after both:
**38/38 models**, determinism byte-identical, width lint and fmt clean.

**M2-L10 was the point of the wave** and it did what it was for. Skip coverage, which I
re-measured myself across all 38 models rather than taking the report:

| | before | after |
|---|---|---|
| models with a backjump skip | 1 | **4** |
| total skips | 2 | **9** |
| learned clauses | 77 | 86 |
| convertible | 11 | 13 |

Three shapes, three propagator families, both sides of D-0044's fork. **M2-L4, M2-L6 and
M2-L8 are unblocked.** (The agent's report said 10 total skips; its own table sums to 9 and
9 is what `--stats` gives. Corrected at the source, because these are the numbers the three
measurement rows will quote.)

**M2-L5 needed nothing from `explanation.ml` — or from `justify.ml`.** D-0044's table held
exactly. That is the second row in a row to confirm a D-0044 prediction rather than bend it.

### A vacuous pass, found and closed

agent-reduce reported, out of scope and unprompted, that `test_justify.ml` was not green
under `BAGUETTE_PROOF_FORMAT=2.0`. I verified it and it was worse than "not green":

`conclusion_break_opb` wrote its `.opb` with `~labels:true`. Labelling belongs to the 3.0
grammar, so under format 2.0 with the Python 2.2.2 checker **the `.opb` did not parse at
all** — measured directly, `:3:1: Expected number`. The three lanes asserting ACCEPTED
failed, and **the lane asserting REJECTED passed, on the parse error, without the checker
ever judging the derivation.** That is D-0020/D-0030's rule verbatim: a lane rejected
without the checker judging an inference is not a pass.

Fixed by removing the argument, so `Writer.default_format ()` decides — the same thing
`Writer.create` decides three lines later, so the two files cannot disagree. Measured in
that configuration: **5 FAIL → 1 FAIL**, and all five D-0043 lanes now pass *genuinely*,
including the one asserting the rejection is the implication check in whichever checker's
words. That last lane is what proves it is no longer vacuous. Default 3.0 path unchanged at
108 ok / 0 FAIL.

### Read this before running the suite under format 2.0

**A `BAGUETTE_PROOF_FORMAT=2.0` run of `test_justify` has exactly ONE expected FAIL**, and
it is deliberate, not a regression:

```
FAIL index: the reused id labels the line that states the clause
     (2.0 has no labels, so this lane is not checked here)
```

`test_justify.ml:693-700` asserts `false` on purpose under 2.0, because the check it wants
— that the reused id labels the line *stating the clause* — is made by reading the label,
and 2.0 has none. **I deliberately did not turn it into a pass**: announcing a hole loudly
is this project's rule, and quietly flipping it would be weakening a test. But it does mean
a 2.0 run is permanently red by one check, which trains people to ignore red. The real fix
is to make that check by content rather than by label, and it is small — **taking it is a
good first task for whoever wants one**, and it is the kind of thing M2-L8 will want when
it measures both formats.

The gate itself runs under 3.0, so `make check` is unaffected.

## M2-T14 handoff, 2026-09-18 (agent-fmt2)

The format-2.0 vacuity sweep. The row existed to answer one question: was the M2-L0 break
lane fixed in `92e03a1` the only lane passing for a reason other than the one it claimed?

**No. Three more, all the same defect.** In every case an artefact pair disagreed about
format, the checker refused the file on the GRAMMAR, and a lane asserting a REJECTION took
that as its evidence — D-0020/D-0030's rule exactly.

1. **`test_proof.ml`, the 3.0-only blocks.** `del range`, the pair spelling, `wipe_level`,
   the D-0023 one-way door, M1-T51 and M2-L1 all emit `version 3.0` and a labelled `.opb`
   unconditionally, but resolved their checker through `Checker.find`, which honours
   `$VERIPB`. Under `VERIPB=~/.local/bin/veripb` those went to the Python 2.2.2, which
   cannot parse a labelled `.opb`: `3.0_broken.opb:2:1: Expected number.` 18 lanes asserting
   ACCEPTED failed loudly; the lanes asserting REJECTED passed on the parse error. Fixed by
   `veripb_v3`, which pairs a format with a binary that can read it — the same shape as
   `test_justify.ml`'s `reduce_break_checkers`.
2. **`test_mutation.ml`, `rows_that_refute_alone` — the worst of the three.** This is
   D-0030's certification that an instance is not hollow. It wrote the `.opb` with a bare
   `write_opb` (env format) and the proof as literal 3.0 text citing `@c<i>`. Under 2.0 that
   is an unlabelled `.opb` cited by label, so every row was refused on the grammar and the
   procedure reported "no row refutes alone" for every instance — the guard against a hollow
   instance, hollow itself. **`certification_finds_root_unsat` caught it.** That control is
   the only reason this was visible; do not let anyone tidy it away. Both files now go
   through `Writer` / `write_opb_for`.
3. **20 blanked-trace negative controls** (7 in `test_trace.ml`, 13 in `test_matrix.ml`).
   These were passing for the right reason, but they asserted off the exit code alone and
   `test_trace.ml` did not even keep the checker's output — so they would have gone green the
   moment the blanked proof stopped parsing. They now assert the RUP wording.

**Test (c) is done.** `test_justify.ml`'s claim-index lane resolved the reused id by reading
its 3.0 `@c` label, so under 2.0 it asserted `false` on purpose. It now resolves the id by
CONTENT — walking the file counting id-minting rules, which is how the checker numbers them
— so the property is checked in both formats. The 3.0 label check is kept alongside, where
it cross-validates the counter. **A 2.0 run is no longer permanently red.**

**Both checker wordings, and a correction worth keeping.** The blanked-trace rejection is a
RUP failure, and both binaries say *"reverse unit propagation"* — so for this rejection the
usual "they share no substring" reasoning is false, exactly as the environment note now
says. Both are listed at full strength and either is accepted; the shared fragment is
deliberately not matched, being the least specific thing either prints.

**One finding left deliberately red, NOT adjusted.** Under 2.0 + 2.2.2, `test_mutation.ml`'s
`triple_unsat/drop-line` and `lin_unsat/drop-line` report that the checker judged the
DERIVATION where the lane is registered as rejecting on the grammar. Under 3.0 dropping a
line un-defines a label and the citation cannot parse; under 2.0 ids are positional, so the
drop renumbers and the checker judges a real (wrong) derivation. That is a lane finding
something and saying so, and its own message says not to re-register it to match. **Left
alone on purpose** — whoever picks this up should decide whether `expect` should be
format-dependent, and record it, rather than making the red go away.

**No soundness problem found.** Nothing accepted a proof that should have been rejected, in
either format.

Final: all seven suites 0 FAIL under 3.0 (`dune runtest --root . --force` green repo-wide),
and 0 FAIL under `BAGUETTE_PROOF_FORMAT=2.0 VERIPB=~/.local/bin/veripb` except the two
`drop-line` findings above. `test_proof` went 18 FAIL → 0, `test_mutation` 3 → 2,
`test_justify` 1 → 0. Peak RSS 22 MB (`test_justify`); nothing came near the cap. fmt clean,
width lint clean.

**The gate still runs under 3.0 only**, so none of this is exercised routinely. If M2-L8 or
anyone else wants the 2.0 path defended rather than merely swept once, the configuration to
add is the one in the row: both `BAGUETTE_PROOF_FORMAT=2.0` and `VERIPB` pointing at the
Python build. Setting only the first checks a 2.0 proof with the 3.0 checker and finds none
of this.
### M2-L6 — PB conflict analysis (agent-pb, wave fourteen)

**Done and green**: 1963 unit checks (baseline 1895 on `main`, +68), 38/38 models with
proofs verified, determinism / width lint / fmt clean, peak RSS 10.6 MB.

**The row works and its fallback is honest.** Suite-wide: **86 conflicts analysed, 36 PB
rows learned, 50 fallbacks — rate 0.581**, across 21 of the 38 models. Neither degenerate
end. `--stats` prints `pb-tried / pb-learned / pb-fallback (rate) / pb-why / pb-steps /
pb-convert / pb-stronger` on stderr. Fallback breakdown: `no PB row` dominates (12 of the
distinct first-reasons — `int_ne`, `bool_clause`, `array_bool_or`, `bool_not`, `bool_eq`
expose none, deliberately), then `no pivot left`, then two `postcondition failed`.

**Two findings the next session needs.**

1. **Our integer propagator is STRONGER than PB propagation on the same row**, and this is
   the dominant non-`No_row` fallback. `3a + 2b <= 14` with `lo(b) = 4` lets `Linear`
   deduce `a <= 2`, but the row's PB form has slack 6 against a pivot coefficient of 3, so
   it does not PB-propagate the pivot and `Reduce`'s postcondition correctly refuses. The
   missing information is the **ladder** implications, which are separate .opb rows.
   `Linear` already builds exactly the right thing as an `Explanation`
   (`Order_reason.weaken_declared`, D-0010) but not as a **row**. Resolving against the
   derived row rather than the model row is the next step and is the single biggest
   available gain; it is bigger than this row was. Written up in `pb_analysis.ml`'s
   "MEASURED" section.
2. **Where the PB path succeeds it derives the EMPTY CONTRADICTION**, not a non-trivial
   inequality. On `backjump_lineq_unsat` the two halves of the `int_lin_eq` give
   `sum >= 3` and `sum <= 2` after a Chvátal–Gomory division and add to `0 >= k/2`, in one
   elimination, and veripb checks it. That is strictly stronger than the clause (it
   entails it) and the clause path has no route to it — but it is **degenerate as a
   propagation result**, and a scene where a non-trivial learned inequality outpropagates
   its clause was looked for and **not found**. Test (a) asserts the truth rather than the
   hoped-for shape. Finding (1) is why.

**Design notes.** `Propagator.pb_row` is new: the inequality an instance *is*, as the .opb
contains it, with the id that names it, defaulting to `None` so an untaught family is not
silently credited with one. `Linear.pb_row` builds it from the **declared** ladder (I-X6).
`Learned.combine` is the `pol` addition and its third stage **cancels complementary
literals**, which `make` deliberately does not — both checkers normalise `l + ~l` away, so
skipping it would leave our copy of the row disagreeing with theirs.
`Justify.emit_stating` makes the learned row's `pol` **state what it derives**, so veripb's
`ia` compares our arithmetic against its own; that is the strongest check on this row and
it is why (c) is worth more than "the proof is accepted".

`falsified` is frozen **at the propagation**, not at the conflict, reconstructed from the
trail's own `old`/`now` pair. The conflict-time predicate would have made every reduction
fail its own postcondition — a 100% fallback rate, not an unsound proof. That is the I-X6
obligation `reduce.ml` left to its caller.

**`explanation.ml` needed nothing.** D-0044's table has now held three times.

The PB row goes on the page **alongside** the M2-L3 clause, not instead of it: the
backjump rests on the decision closure either way, and M2-L3 owns assertions about the
clause. `Search.no_pb` turns the path off for a comparison against M2-L3's numbers.

**I-S4 for a `pol` is discharged** — `learn.ml` explicitly left this here. Every leaf of a
derivation is a `Model_row` of the .opb; no hole line, trace line or conflict-level id is
ever cited. `Pb_analysis.cited_ids` returns the set so it is checked, not argued.

## Wave fourteen handoff, 2026-09-18 (orchestrator): M2-L6 and M2-T14

Two sessions, both merged and pushed. Gate green: **1986 unit checks**, 280 matrix, 44
mutation, **38/38 models**, determinism byte-identical, width lint and fmt clean.

**With M2-L6 in, the learning sequence is complete except M2-L4, M2-L7 and M2-L8.**

### M2-L6's result is a negative, and it must not be read past

The row existed to show a learned PB inequality is *strictly stronger* than the clause it
replaces. It is — and it is also **degenerate**. Where the PB path succeeds it derives the
**empty contradiction**, never a non-trivial inequality. **A scene where a non-trivial
learned inequality outpropagates its clause was looked for and not found.** I re-measured:
`pb-stronger` is **36 of 36** learned rows, and all 36 are that degenerate case.

Fallback rate, independently re-measured and matching the report exactly: **0.581** — 86
attempts, 36 learned, 50 fallbacks, 21 of 38 models, with `attempts = learned + fallbacks`
holding. 0.00 on the lineq model, 1.00 on the bool ones.

**Why, and this is the valuable part — now M2-L11.** *Our integer propagator is stronger
than PB propagation on the same row.* `3a + 2b <= 14` with `lo(b) = 4` lets `Linear` deduce
`a <= 2`; the row alone has slack 6 against pivot coefficient 3. The strength lives in the
**ladder implications, which are separate `.opb` rows**. So the real reason for a `Linear`
pruning is *model row + ladder chain* — something `Linear` already builds as an
`Explanation` but never as a **row**, so the PB analysis cannot see it. Until it can,
eliminating a pivot can only ever reach the contradiction. M2-L11 is that row, and its test
(b) is deliberately a **number**: `pb-stronger` counting a non-degenerate learned row, so
the improvement cannot be claimed without being measured.

**Koops et al. was read properly and corrected two things in my brief.** Merging adjacent
weakening steps on `pol` lines is **CakePB's own pass** (§5.4), not an emitter obligation —
so M2-L5 needed no change. And "partial weakening before a non-normalised division" is §3's
**MIR**, which is strictly stronger than both `Reduce` rules and belongs as a **third
`Reduce.t`**, not inside this row. Both recorded rather than acted on, correctly.

`explanation.ml` needed nothing again: **D-0044's table has now held three times** — M2-L5,
M2-L6, and M2-L1 before them.

### M2-T14 found three more vacuous lanes, and one of them was a guard

Detailed in that row and in D-0030's amendment. The one to remember: **`test_mutation.ml`'s
`rows_that_refute_alone` — D-0030's own certification that an instance is not hollow — was
itself hollow under 2.0**, reporting "no row refutes alone" for *every* instance because an
unlabelled `.opb` was cited by label. Only its own control made it visible.

Verified by me under both configurations: `test_proof` **18 FAIL → 0**, `test_justify`
**1 → 0**, `test_mutation` **3 → 2**, the survivors deliberate (**M2-T15**).

### Two habits from this wave worth keeping

- **Both agents reported a negative prominently rather than burying it** — agent-pb's "not
  found", agent-fmt2's "two left deliberately red". Two sessions also converted *their own*
  vacuous tests into reported facts rather than leaving them green. That is the behaviour
  this project's rules exist to produce, and it is now the norm rather than the exception.
- **Setting only `BAGUETTE_PROOF_FORMAT=2.0` exercises nothing**, because `Checker.find`
  prefers the Rust 3.0.2 and never reaches the Python checker. **Both** variables are
  required: `BAGUETTE_PROOF_FORMAT=2.0 VERIPB=$HOME/.local/bin/veripb`. The gate runs 3.0
  only, so nothing routinely covers that path.

### Next

**M2-L4** (deletion policy, absorbs M2-T4) and **M2-L8** (benchmark) are both unblocked and
both were held back for M2-L10's instances, which now exist — 4 models, 9 skips. **M2-L7**
(saturation) still needs its own decision record before any code. **M2-L11** is the row that
would make M2-L6 pay off, and **M2-T15** is a question, not work.

---

## M2-L8 handoff, 2026-09-18 (agent-bench)

**Released.** Files touched: `bench/run_bench.sh`, `bench/README.md`, `bench/control/**`
(new), and these two WORKLOG rows. Nothing outside `bench/` was edited; `lib/` and `test/`
were read-only throughout, as the wave-fifteen split required.

**The numbers, and which of them may be quoted.** 38 models, all measured, none refused,
none rejected, every proof accepted by VeriPB 3.0.2 before its row was printed. The
learning counters are **exact**: 86 clauses over 21 of 38 models, 13 convertible (15%),
9 skips over 4 models, PB 86 tried / 36 learned / 50 fallback = **58%**. They reproduce
M2-L6's 0.581 on a suite that has grown since, and `pb-stronger` is still 36 of 36
**degenerate** — M2-L6's honest negative is unchanged and M2-L11 still has everything to
prove. The byte columns are exact at every row. **The timing columns mostly are not**:
23 of 38 rows spend ≥90% of their wall-clock `solve ms` outside the solver's own work,
and only `width_sat_depth` (5%) and `width_root_unsat` (27%) are below half. No count in
this report is divided by a time, and `bench/README.md` §3c says why in those words.

**The verdict rule changed, and the next session should know it.** M1-T36 keyed `CHANGED`
on the node count alone. That was correct when written and went stale when backjumping
landed: `nodes = 2 * decisions + 1 - skipped` lets a tree gain a decision, skip two more
siblings and land back on the node count it started from. `bench/control/ctl_samenodes`
is exactly that shape — nodes 9 = 9, decisions 5→4, skipped 2→0 — and under the old rule
it came out `proof-only`, i.e. an invitation to compare the bytes and seconds of two
different searches. All four tree counters now decide `CHANGED`.

**`bench/run_bench.sh -c` asserts and exits non-zero.** It is not in `make check` and must
not go in — `make bench` is measurement and a benchmark that gates a commit becomes a
flaky test — but it is the one part of `bench/` that can fail, and anyone changing the
comparison logic should run it. It was verified by breaking the classifier three ways
(nodes-alone, hard-wired `proof-only`, hard-wired `CHANGED`); each break exits 1 and names
the scene it got wrong. §7 of `bench/README.md` has the table.

**Two things left for someone else.** (a) `Makefile` line 106 still documents
`make bench ARGS="-F 2.0"`, a flag that no longer exists — raised under Cross-session
requests; the target body is fine. (b) The proof-only control is a pair of *models*, not
a pair of solver configurations, because after D-0046 there is no CLI knob that moves the
proof without moving the tree: `--proof-comments` is a documented no-op on every shipped
model (M1-T48's other half, already open). If M4's direct encoding ever makes that flag
reachable, it becomes the better proof-only scene and `ctl_proof` can retire.

**Peak RSS**: 10.4 MB for the control run; across the full suite, 9.7 MB solve and 18.6 MB
verify. Nothing came near the cap, nothing timed out, and every run was under
`ulimit -v 4000000`.

**2026-09-18 — M2-T16 (agent-drop): format 2.0 is gone, and three things to know**

**Artefact bytes did not move.** All 38 models' `.opb`, `.pbp` and stdout are byte-identical
before and after, with `bin/main.exe` hashed on both sides and different (`8223711a` →
`0011dc99`). That is what D-0046 predicted — labels were already unconditional under the
default — and it is worth stating as a *result*, because a byte comparison whose two sides
used the same binary is no evidence at all.

**The unit count dropped 1986 → 1972, and every one of the 14 is a second leg, not lost
coverage.** Ten were format matrices collapsing (`test_learned_survives_the_backjump` ×4,
`test_reduction_truncation_is_rejected` ×6). Four were lanes whose 3.0 twin asserts strictly
more and which are now absorbed rather than duplicated: `test_writer_rules`,
`test_veripb_accepts`, one of `test_writer_levels`' three assertions, and the 2.2.2
one-way-door probe. If you are chasing the number, that is the whole of it.

**M1-T46's rule is REPLACED, not deleted, and the replacement is the part that matters.**
"Never match on one checker's wording alone" existed because there were two checkers; with
one, matching its wording *is* correct, and 14 sites were simplified accordingly. What
survives, and is now in `CLAUDE.md` and `PROOF-FORMAT.md` §2a: **a lane asserting a
rejection must assert the checker's wording at full strength**, because an exit status
cannot tell a judgement from a parse error — which is exactly what M2-T14 found four lanes
doing. If you write a negative control, assert the sentence.

Also: `veripb 3.0.2 is now the sole oracle`, stated in `scripts/checker.sh`,
`Checker.not_found_message`, `SPEC.md` §1 and `PROOF-FORMAT.md` §1. A bug in it is a bug
nothing here can see. D-0046 weighed that and accepted it; do not rediscover it as news.

**2026-09-18 — M2-T17 (agent-size): explanation size is now a tracked number, and the
control is the part to read**

`bench/explanation_size.sh` reports two metrics per model, separately because they move
independently: `rup_lits` (literals per derived `rup` constraint) and `pol_prems` (premises
per `pol` chain). Both come off the emitted `.pbp`, so this added **no `lib/` change and no
solver counter** — that scoping is why it could run beside the M2L sequence at all, and it
is the same shape as M2-L8. Baseline is `bench/README.md` §3d. Not in `make check`, per the
row and per the `make bench` rule.

**Nothing looks verbose today, and that is the expected answer.** `pol_prems`' only large
figures are the two known D-0028 width fixtures (1999.0, 19.0); the largest non-width figure
is 5.0. While every propagator is linear the derivation is forced, so there is no room for a
weak explanation to hide. **The metric's job starts at M4-T1**, where the choice of Hall set
is the whole game — which is exactly why the row was scheduled before it rather than after.

**The lesson from this one is about the control, not the metric.** As first delivered it
passed, and the session *volunteered* that one of its three deliberate breaks — counting only
`@c`-prefixed `pol` premises — was not caught by its fixture, calling it a small follow-up.
It was not small: `width_root_unsat`'s `pol` line is essentially all bare literals, so
`pol_prems=1999`, the largest figure in the whole baseline, is produced by precisely the
token class the control did not protect. And the suite-wide run only *reports* — nothing
asserts on it — so that regression would have changed the headline number with no lane going
red. That is the "green for the wrong reason" shape M2-T14 and M1-T51 both found, arriving
from a new direction: **not a lane that passes vacuously, but a metric whose largest value is
unprotected.** If you add a benchmark figure, ask which of its numbers a control would catch
being wrong.

Fixture widened, `@c`-id count pinned at 4 on both sides so the growth is attributable.
**Verified independently rather than read off the report**: honest script exits 0; flattening
the variant fixture exits 1; break (3) re-applied by hand exits 1 on `pol_prems did not grow
(4.0000 -> 4.0000)`. Gate after the merge is **1972 ok / 0 FAIL**, 280 matrix, 44 mutation,
12 random, 38/38 models, determinism green — identical to the pre-merge baseline, as a
`bench/`-only change should be. Peak RSS 9.6 MB.

**2026-09-18 — M2-L11 (agent-ladder): the lift works, and it corrected the number it was
built on**

**Read this before you trust any `pb-*` figure you remember.** M2-L6's headline —
`pb-stronger` **36 of 36** learned rows, every one degenerate — is **wrong**. Re-measured
independently on `main` *before* M2-L11 merged, by counting emitted `ia` rows instead of
reading a counter: **36 learned rows, 26 carrying terms, 10 degenerate.** The 10 are exactly
the `int_lin_eq` family (`backjump_lineq_unsat` 3, `near_limit_unsat` 3, `offset_unsat` 4) —
the family M2-L6's own test (a) inspected — and `width_sat_depth` **alone** contributes 24
non-degenerate rows. The conclusion was true of what was looked at, then stated of the suite,
and **nothing counted**, so nothing contradicted it. `pb-nondeg` is now that counter.

**D-0047 was written on that wrong figure, by me, hours earlier, and is amended rather than
deleted** — the amendment is the useful part. What is withdrawn: "PB learning keeps producing
degenerate rows" as a suite-wide claim. What survives and is now measured: the *mechanism* —
where the reason is the model row **without** its ladder chain, certain conflicts yield no row
at all and fall back. The general lesson, which is why it is in a record and not just here:
**a headline figure with no counter behind it is a claim, not a measurement**, and a decision
record inherits the confidence of whatever it cites. That number was checkable in two minutes
with `grep` over emitted proofs.

**What the row delivered.** `lib/core/ladder.ml` lifts a `Linear` reason onto the ladder rungs
that carry its strength (D-0028). On its fixture: 2 conflicts → 2 rows learned, 0 fallbacks,
both non-degenerate, 2 rungs cited; with the lift off, 0 learned and 2 fallbacks. **Suite-wide
it fires on one model of 39.** That is small, and D-0049 records it as small — the large claim
it was expected to support was the mis-measurement above.

**Three things a later session will want to undo, and should not.** All in D-0049:
(1) the lift takes only **non-falsified** terms — lifting a falsified term adds the same
amount to slack as to the pivot coefficient, so it buys nothing; it looks like a missing case
and is actually the argument. (2) **Retry, not replace** — the bare row is tried first, so
every conflict M2-L6 handled keeps M2-L6's derivation and the lift can never make a proof
worse. (3) I-S4 is discharged **structurally**: ladder cids are level-0 `.opb` rows retired by
nothing.

**Test (d) was asserted for the first time, and `Linear` could not have asserted it.** The
`Order_reason.weaken_declared` / `Encoding.expand_int_lin_le` coupling is checked in both
currencies now; `summands_of_snap` discards the constant (`let lits, _ = …`), so a drift would
have been **silent** until `Ladder` used it. The standing hazard entry for that coupling can
now say it is covered.

**Both module maps were missing six modules, not one.** `CLAUDE.md` and `ARCHITECTURE.md` §1
both lacked the entire M2L learning vertical — `learned`, `learn`, `analysis`, `reduce`,
`pb_analysis` — as well as `ladder`. §1 said "verified against the tree on 2026-09-18"; that
verification checked the propagators and not `lib/core`'s root. Both maps are now correct and
say so. Test binaries are **19** (was listed as 15), models **39** (was listed as 34).

**Next**, in the order I would take them: **M2-L4** (deletion + retention policy, absorbs
M2-T4) and **M2-L7** (`Saturate`, still needs its own decision record) are the open learning
rows. But D-0049 ends on a better-posed question than either: the lifted rows are
non-degenerate and still **do not convert** (`pb-convert 0` on the fixture), so the thing
actually worth knowing is **what a learned PB row must look like before
`Learned.to_linear_row` accepts it**. Someone should scope that before M2-L7.

**Final gate on `main` after both merges**: **2064 ok / 0 FAIL**, 280 matrix, 44 mutation,
12 random, **39/39 models**, determinism green, fmt and width lint clean, `check: ok`. Peak
RSS 37.7 MB unit, 18.5 MB models. Nothing came near the cap.

**2026-09-18 — wave seventeen, the read-only half (agent-convert): D-0050, and a premise of
mine that was wrong**

**`pb-convert` is 36 of 38 suite-wide, not 0.** D-0049 reported `pb-convert 0` *on M2-L11's
own fixture* and said so carefully. **I generalised it** — into this wave's briefing and into
what I told the user — as though learned rows do not convert in general. They mostly do. The
only two rows in the whole suite that `to_linear_row` refuses are the two M2-L11's lift
produced, and that is structural: the lift substitutes rungs and accumulates multipliers, so
it necessarily leaves a variable incomplete or non-uniform. **"Lift more" moves rows OUT of
the convertible class.**

**This is the second time in two waves** that a figure true of one model or one family was
restated as a property of the suite — M2-L6's "36 of 36 degenerate" was the first. **The
pattern is the finding**, and it is in D-0050: counters here are per-run and summed by hand,
so a number read off one model is typographically indistinguishable from one read off the
suite. **Say which you have.**

**Three live figures are wrong and are routed to agent-del** (it owns those files this wave):
`pb-convert`'s gloss in `bin/main.ml:496` says "could propagate" while 10 of the 36 it counts
are the empty contradiction converting to a zero-term `Linear`; `bin/main.ml:503` says "38
models" and "26 of 36" against an actual 39 and 28 of 38; `pb_analysis.ml:125-126` says "13 of
86" against 13 of **88**. All three re-measured by me on `main` before routing.

**`docs/DECISIONS.md` D-0044's amendment was substantively wrong** and is corrected in place:
it said `to_linear_row` succeeds "on a clause over `var bool`s". The real condition is
**declared width 1**, which is broader — `ne_eq_unsat` (`1..2`) and `trace_settle_sat`
(`2..3`, `0..1`) convert with no Boolean present, and 3 of the 13 converting clauses are
non-Boolean. Restricting a cut "to Boolean shapes" on that sentence would restrict it too far.

**M2-L7 is demoted, not scheduled.** Its promotion was conditional on M2-L11 failing, and
M2-L11 succeeded. Saturation is uniformity-preserving and cannot rescue a refused row.

**The open question D-0050 leaves**, and it is the real one: the clause path is blocked at
declared width ≥ 2 because `Learn.minimise` keeps one threshold per variable per direction —
a strengthening step that is simultaneously a convertibility-destroyer. Fixing it means giving
the clause path a clause instance over order literals, **which spends D-0044's "no new
propagator family" bet**. `bool_clause.ml` already is a clause propagator, so it may be a
widening rather than a new family — but that argument must be made in a record, not assumed.
**75 of 88 learned clauses are proof-only today**, and the backjump they justify re-derives
the conflict they came from, which is M2-L3's own stated regret.

**2026-09-18 — wave seventeen closed: one row merged, three questions answered**

**M2-L4 is in** (D-0051). `Retention` owns a learned constraint's lifetime alone, enforced by
`Writer.wipe_level` refusing level 0 rather than audited. **D-0045 predicted the wrong
collision**: it warned of two owners; the real shape was one owner, `Search.solve` sweeping
every id ever introduced. The I-X2 audit **cannot witness that** — a second `forget` is a
no-op — which is now written on I-X2 itself. Policy is `keep_all` **by measurement**: nothing
propagates a learned constraint, so activity is the constant zero, and eviction monotonically
*increases* proof bytes and `del` rules. Cite D-0051 as *"retention does not help while
nothing propagates a learned constraint"*, never as *"retention does not help"*.

**M4-T5's gate is evaluated and the answer is no.** Both its dependencies had been DONE for
some time and nobody had checked. Decisive: **`width_root_unsat`, the largest proof in the
suite, has ZERO `rup` lines** — its cost is one 1999-premise `pol` chain — so the biggest
artefact here is not evidence about RUP hints at all. 36 of 37 non-width models are at the
process floor. Revisit only when a real non-synthetic model enters the suite.

**D-0052 settles D-0050's open question: the clause instance is a WIDENING of `bool_clause`,
so D-0044's bet is NOT spent.** `Explanation.Clause` is already `Lit.t list`; the Boolean
sites are constant substitutions. Two refinements worth carrying: **watched literals are a
separate question and should be dropped** (they would be the first mutable propagator state
outside `Store`'s trail, and max clause width here is 4), and **the declared level must drop to
`Bounds`** because order literals have an interior — `x≤1 ∨ x≥3` is a hole, not a tautology.
That is the honest counter-argument to the verdict and D-0052 states it rather than burying it.

**New row M2-L12** carries the implementation, in two steps, with the `Retention` coupling
named as part of the same change.

**The standing rule earned its keep three times this wave.** Do not relay a figure you did not
re-measure. M2-L4's report, the hints study and the clause study were each checked; the clause
study's one unverified aside (that `CLAUDE.md` said "34 models") was **wrong** — its own base
commit said 39. Its headline argument was sound, which is the point: the discipline is cheap
and it is not an accusation.

**Provisional figure, flagged**: "~70 of 88 learned clauses are unit" is ±5, from proof-text
parsing. An orchestrator re-parse measured a *different* population and settles nothing.
Re-derive it from instrumentation before M2-L12 step (1)'s priority rests on it.

**Gate on `main`**: **2129 ok / 0 FAIL**, 280 matrix, 44 mutation, 12 random, **39/39 models**,
determinism + fmt + width lint clean, `check: ok`. Peak RSS 37.8 MB unit, 18.6 MB models.

**2026-09-18 — wave nineteen: learning works, and it is worth 18.7× on the right model**

**Read this before you trust any node count you remember.** The suite is **44 models** and the
numbers moved twice in one wave.

| | learning off | clause propagation | **PB propagation** |
|---|---|---|---|
| all 44 models | 2265 | 847 | **479** |
| the old 39 | 231 | 231 | **179** |
| `php_wide_unsat` | 1439 | 297 | **77** |
| `width_sat_depth` | 99 | 99 | **53** |

**Two corrections to things this project believed a day ago.**

1. **"Learned-constraint propagation is worth nothing" was the instrument.** The old 39 models
   had a largest search of 99 nodes — a width *spine* — and everything else at ≤ 10. A ten-node
   tree has no second subtree, and learning pays when the same conflict recurs in one. Five
   models later (all variables `0..1`, hardness combinatorial not width) the same ablation is
   **4.85×**. The user asked whether the examples were hard enough; they were not.
2. **"The old 39 are inert" was also wrong** — they were inert *to clauses*. PB propagation
   moves them 231 → 179, on the `int_lin_eq` models where the empty contradiction finally has a
   consumer.

**D-0044's "no new propagator family" bet is deliberately LOST** (D-0055). `lib/core/prop/pb.ml`
is a new family, and `clause.ml` is now literally `type t = Pb.t` — the degree-1 face, which is
the relationship D-0044 asserted all along. The bet was worth keeping while the gate on
propagation was `to_linear_row`; D-0054 showed that gate was a proof-side test doing a
solving-side job, and removing it means propagating the PB row **as a PB row**.

**The finding to carry into M4**: the textbook slack rule prunes **0 times on integer variables**
— it is **ladder-blind**. Falsifying `[x≥3]` falsifies `[x≥5]` with it, so a rung's effective
coefficient is the **suffix** of its variable's rungs, not its own. That is where
`width_sat_depth` 99 → 53 comes from, and it costs nothing in the proof: still one `rup`,
because the extra inference is the checker's own unit propagation over ladder rows. This is
M2-L11's ladder insight arriving on the **solving** side.

**Evidence discipline that made all of this readable**: with propagation **off**, all 44 models
are byte-identical to the previous `main` with the two binaries genuinely different
(`78e1f187` → `dc78e99a`). Every headline figure here was re-measured by the orchestrator, not
relayed.

**Two things now spent — do not cite them again.** `Retention`'s "activity is the constant zero"
argument (twice over now), and `cfg.pb = off` as a proof-side-only switch: turning the PB path
off now changes the search.

**The natural successor row**: backjumping still rests on the clause's decision closure
(`pb_analysis.ml:757`), whose own note said "a PB row that propagates at runtime would change
that calculation". It does now, and nobody has redone that calculation.

**Gate on `main`**: 2256 ok / 0 FAIL, 280 matrix, 44 mutation, 12 random, 44/44 models verified
by veripb 3.0.2, determinism + fmt + width lint clean. Peak RSS 38.7 MB.

**2026-09-21 — wave twenty: the backjump answered, and M3 opened**

**M2-L15 (D-0056): the decision closure is RIGHT, not merely safe.** The backjump here is a
**filter on the nogood**, not an undo-to-level — a sibling is skipped exactly when the branch
nogood does not name that level, and that nogood is a clause over **decision** literals veripb
RUP-verifies. `Pb_analysis.levels` and `asserting_level` answer different questions. The levels
**do** differ: over 44 models, 103 conflicts compared, 26 equal, **76 where the PB set is a
strict SUBSET**, 1 wider, 3 empty-contradiction (level set `{}`, filtering by which leaves the
empty clause). Narrower is the unsound direction. **The break reddens**: `backjump_on_pb` gives
a *smaller* tree with the right answer and plausible counters — and veripb rejects. **Do not
reopen this** by observing that a PB row "knows" its levels: it knows where its literals were
*falsified*, which is the narrower set.

**M3-T2 + M3-T4 (D-0057): all four reified builtins, through one dispatcher.** An author
supplies three closures of type `Store.t -> Propagator.result` — the signature of `propagate`
itself — so the author's piece is an existing propagator over an existing row. Second builtin
costs **21–22 lines**; `int_ne_reif` is `int_eq_reif` with one argument. Both things D-0053 left
open are closed: the `<=` rows are pinned as identical to `Encoding.reif_rows`, and
`int_eq_reif` needs **no `p ∧ q`**.

**The finding to carry, and it is not about reification.** Two deliberate breaks — a
justification citing the wrong row, a big-M one too small — **reddened NOTHING**. With the
reifier forced by a `bool_clause`, `Search.rests_on_a_clause` closes the refutation the D-0022
way and **every `pol` in the file is decorative**, because veripb accepts a `pol` whatever it
derives. **When you add a propagator and its justification, check that some model actually
CITES it — a green suite does not.** The four models were rewritten to force the reifier with a
unit linear row.

**A real bug fell out of it**: `reif_eq_branch_unsat` is the first model where a reifier is
decided by *branching*, and it caught a reason copying `Ne`'s `Reason.none` without `Ne`'s
licence for it. veripb rejected the trace line.

**Gate on `main` after both merges**: **2332 ok / 0 FAIL**, 280 matrix, 44 mutation, 12 random,
**57/57 models**, determinism + fmt + width lint clean, `check: ok`.

**2026-09-21 — M6-T6 handoff (agent-bisect)**

**Bisected, not hypothesised, per the row's instruction.** `width_sat_depth`'s "43 ms end to
end" comment (`83cc658`) was essentially true when written (18.6-23.4 ms best of 5, measured
directly at that commit in a worktree; the model itself never changed after that commit). The
whole ~14x regression is **one commit**: `aacbc8d` ("M2-L6: wire PB analysis into the search,
with the fallback rate on `--stats`") — its parent `f93ecd1` (PB analysis machinery added but
not yet called) times at 18.6 ms, `aacbc8d` itself (wired into `Search` unconditionally) times
at 258.7 ms. `git bisect run` over `83cc658..main`, 7 steps, 0 commits skipped (every commit
built). Everything after `aacbc8d`, including M2-L12's flag and M2-L13's later ladder-suffix
work (§3f), is refinement in both directions, not a second regression of the same size.

**Recommendation: accept, don't chase.** M2-L6's PB analysis is finding real value on this
exact model (`pb-learned 24/49`, `pb-stronger 24`) and M2-L13 already claws most of the cost
back for the shipped (`BAGUETTE_PROPAGATE_LEARNED=on`) configuration. Full writeup, method and
numbers: `bench/README.md` §3g. New script: `bench/width_sat_depth_bisect.sh`. Only `bench/**`
touched — `git status` in the worktree clean otherwise, worktree left on `wave23-bisect`.

**One loose thread for whoever owns `test/models/`**: `width_sat_depth.fzn`'s own header
comment ("at 99 it is 43 ms end to end") is stale post-M2-L6/M2-L13 and should be updated or
removed; that file is outside `bench/**` so this row did not touch it.

**2026-09-22 — wave twenty-six: the solver meets input it did not author**

**All three M7 rows landed.** Gate on `main`: **2832 ok / 0 FAIL, 280 matrix, 44 mutation,
85 passed + 1 expected-fail, `check: ok`**.

**M7-T1 (D-0065)**: the hardware limits are options, defaulting off. A width-20 000 model now
solves and **veripb accepts its proof**; 425 artefacts across 85 models unchanged. It amended
D-0041's normative MUST *by answering its objection* — the default being unlimited makes the
accepted language fixed and maximal, so the knob can only restrict. **A third category of limit
was found that my brief missed**: representability. *A limit that exists because the machine is
small is an option; a limit that exists because the arithmetic does not exist is not.*

**M7-T2 (D-0066)**: **70% of the corpus runs past the front end.** The census says the next best
buy is `smallest` + `indomain_split` **together, +71 instances to 94%** — and that `dom_w_deg`
occurs 4 times in source and **zero** times after flattening. SPEC was right and the code was
wrong. A pre-existing silence closed: unrecognised annotations were being **dropped** and the
model searched by the default.

**M7-T3 (D-0067)**: **112 → 300 instances flatten into the subset**, `all_different_int` survives
in 66, and the Hall path is shown working end to end.

**THE THREE FINDINGS THAT OUTLIVE THIS WAVE:**

1. **`rup` is vacuous over a contradictory database (D-0066).** A literal removed, and a
   polarity flipped, are **both accepted** on an UNSAT model's proof. **26 lanes across 9 files
   assert a RUP rejection** and those files are dominated by UNSAT models. How many are testing
   nothing is **unknown** — that audit is **M7-T5**. This is D-0053's `red` finding one rule
   over, and the more consequential one.
2. **A correct answer whose proof is rejected (M7-T6).** Nine variables, five constraints, **no
   global**. Shown **pre-existing** by rerunning the same 2001 fuzz seeds with the global
   decomposed — 3 failures native, 5 decomposed, overlapping but different. Shipped as a
   `PENDING` model so it is visible on every run. **M1-T44's shape**, and note it can only be
   *seen* on a satisfiable model because of finding 1.
3. **The blocker is no longer width — it is set-literal domains**, which no `mznlib` can reach.
   And the width that remains is mostly **the objective variable**, wide by construction on any
   optimisation model, which deserves its own answer rather than a bigger limit.

**A process note worth keeping.** Two branches were granted scoped edits in each other's files,
in both directions, because routing through the owner would have left a branch whose gate is red
— and a red-gated branch is one the orchestrator merges **on trust**. Both merged with **no
conflicts**. The precision made it work: each agent reported exact line ranges, and I diffed them
before merging.

**Stale figures to re-measure, not quote**: M7-T3's 78-refusal breakdown predates M7-T1's merge,
so its width refusals are already gone.

**2026-09-23 — agent-search (M7-T7)**
The refusal on a constant in a search array is gone: `lib/flatzinc/builder.ml` filters
constants out of the index list instead of failing. Nothing downstream needed a change —
`compile.ml`'s `phases_of_search` already builds a phase from whatever list it gets, and
`Search.sequence` already skips a phase with no unfixed candidate, so an ALL-constant array
is a legal empty phase that `seq_search` falls through. That is the right reading of SPEC
§3.4: the annotation asks for a search over that array, and a search over that array never
branches on a fixed element, so skipping honours it.
Two things for whoever picks this up. (1) **I could not ship a literal corpus instance for
obligation (d).** `/scratch/arthur/corpus-out/` is on `fataepyc-07` and does not exist in this
checkout, and no `minizinc` binary is on this machine either, so `test/models/search_const_in_array_sat.fzn`
is a HAND-SHRUNK reconstruction of the roster/scheduling shape at width 5 — the model header
says so in full. If someone re-runs the corpus, replacing it with a real (shrunk) instance is
worth doing and the assertions will not change. (2) Both new models are SAT on purpose, so the
proof check is over a satisfiable model rather than a contradictory database (D-0053).
`docs/ROADMAP.md`'s M7-T7 row is still marked TODO — it is a contention hotspot and not in my
claimed file set, so the orchestrator should flip it on merge.
## M7-T6 handoff

**The level-0 nogood RUP defect is FIXED, and it was neither the nogood machinery nor the
checker.** `docs/DECISIONS.md` **D-0070** has the full account; the three sentences that
matter here:

- **The cause is a decision push that SETTLES past a hole.** The trail lands on a bound
  strictly stronger than the literal the branch assumed (`x7 >= 2` assumed, `x7 >= 3`
  recorded, because `int_ne` punched a hole at 2). `Search.bridges` already wrote that
  step down — conditioned on *every* ancestor decision, which its own `rup` needs — but
  **the implication graph has no edge for a settle**, so `Learn.levels` never named those
  ancestors' levels and M2-L3's nogood filter dropped exactly the literals the bridge
  rests on. `bridges` now returns those literals and the filter keeps them.
- **Proof-only, never a wrong answer.** `bridges` is pure emission, and a nogood carrying
  more literals mentions more levels, so the repaired build skips *fewer* siblings. The
  break lane asserts the returned assignment is identical with the break on and off.
- **The empty-model rejection was a DIFFERENT bug** — `lib/proof/writer.ml`'s `conclusion`
  guarded the `sol` line on the literal list being non-empty, a mechanical carry-over from
  M1-T18 (26d3ab2). Fixed; `test/models/empty_model_sat.fzn` is the model test.

**What the next session should know.**

1. **`test/models/PENDING` now lists no models.** `rup_level0_nogood_sat` passes with its
   proof verified. 87 models, 0 pending. Keep it that way.
2. **D-0066 is still the trap, and it is now the most important thing on this page.** This
   defect survived to M7 only because `rup` is vacuous over a contradictory database, so
   every UNSAT instance of it was accepted silently. D-0068's "1 substantive rejection in
   11 proofs" was never the true rate. **The next nogood rejection you see: look for a
   settle past a hole first.** It is invisible in the answer, invisible on UNSAT models,
   and its symptom appears several inferences downstream of its cause.
3. **`break_bridge_levels` is the new break knob** on `Search.config` (off, not
   CLI-reachable). It restores the old filter. Measured with it flipped: **exactly one of
   87 model proofs differs** and it is the reproducer — so the fix costs nothing on the
   other 86, byte-for-byte.
4. **The deeper repair is still open and is worth a row.** The right fix would make the
   settle a real edge in the implication graph (`lib/core/analysis.ml`), so
   `Learn.levels` reports the ancestors itself instead of the nogood filter being told to
   hold them back. What shipped is correct and cheap; it is not that.

Gate at `8afbcc1`: **2824 unit checks ok, 0 FAIL** (`dune runtest --root . --force`),
**87/87 models, 0 failed, 0 expected-fail**, `fmt: clean`. Peak RSS of the model run
**18.5 MB**.
## M7-T8 handoff

**What landed** (branch `wave27-guard`, commits `353d69e`, `5151f2f`; NOT merged to main).
`lib/proof/encoding.ml` gains a resource guard, `bin/main.ml` exposes it and maps it to a new
exit status, `test/unit/test_proof.ml` gains 22 lanes, `docs/DECISIONS.md` gains **D-0071**.
Nothing else was touched; `lib/flatzinc/builder.ml` and `lib/core/**` were never needed.

**The shape, in one line each.** `--max-encoding-clauses N` (default `none`) bounds the
aggregate `ladder_clauses + direct_values`, checked in `declare_int` and `ensure_direct`
*before* the loop that allocates, so a refusal leaves the encoding byte-identical.
`--max-heap-mb N` (default `none`) is a `Gc` alarm in `mem_guard.ml`'s shape plus a
synchronous read at each declaration. Both are diagnosed and both end in **exit 5**.

**Three things the next session should know.**

1. **`Gc.quick_stat ().heap_words` is 0 until the first major cycle completes** on this
   switch (OCaml 5.1.1, native, measured 2026-09-23). `Gc.stat` is exact but walks the heap.
   That is why the *alarm* is the reliable half of the reactive guard and the synchronous
   read is opportunistic, and why any test of the synchronous half must `Gc.full_major ()`
   first. `test/unit/mem_guard.ml` is alarm-only and unaffected -- but do not read
   `quick_stat` synchronously anywhere else without reading D-0071 first.
2. **Do not give either budget a default.** D-0065 and the user's standing instruction both
   say the normal build restricts nothing, and any number here would be a property of the
   machine that measured it. The shipped defaults are sampled at module load in
   `test_proof.ml` (`m7t8_shipped_defaults`) precisely so a later session cannot set one
   without a lane going red -- D-0065's own vacuity lesson, applied again.
3. **The corpus harness (M7-T4) should bucket exit 5 on its own.** That is the point:
   D-0068's `SOLVE-ERR-134` folded "this machine ran out" together with "this proof is
   wrong". `--stats` now prints `budget` and `heap` beside `ladder`/`direct` in the same
   units, so a run that ends in 5 can be re-run with a number rather than a guess.

**Still open, deliberately.** The guard bounds the encoding and the heap; it does not bound
*proof size on disk* or *checker time*, which D-0065 named as the cost a 2 TB machine does
not repeal. A `--max-proof-bytes` would live in `lib/proof/writer.ml` and is a different row.
And `lib/flatzinc/compile.ml` still pre-checks only the per-variable width, not the
aggregate, so an aggregate overrun surfaces from `Encoding` rather than with a source
position -- acceptable, since the message names the variable, but a positioned version would
be better and belongs to whoever owns `compile.ml` next.
## M7-T10 + M7-T4 handoff, 2026-09-23 (agent-harness)

**The corpus harness is now `scripts/corpus_run.sh`**, with `scripts/corpus_selftest.sh`
as its guard (`./scripts/corpus_run.sh --self-test`, no corpus, node, solver or checker
needed). The one-off on `fataepyc-07` is superseded; the fixed copy is deployed at
`/scratch/arthur/baguette/scripts/` and the corrected suspect results are in
`/scratch/arthur/corpus-out-m7t10/results.tsv` (103 rows, complete). The original
`/scratch/arthur/corpus-out/results.tsv` is kept but **101 of its 436 rows are void** --
see the M7-T10 row above for which.

**The surprise.** D-0069 diagnosed a non-atomic capture and prescribed temp-plus-rename.
That was the right prescription for the wrong disease: the real cause was that the
instance ID was the family directory, so fifteen `2010/bacp/*.mzn` jobs shared one output
path. Temp-plus-rename alone would have made one job win cleanly and the other fourteen
silently measure the wrong model -- a quieter version of the same lie. **The harness's
unit of identity has to be the unit of work.** Both fixes are in; the self-test asserts
the ID one, because it is the one that would otherwise come back.

**The self-test earned its keep twice while being written**, which is the argument for
writing it: `grep $'\000'` silently matches *every* file (a NUL truncates the pattern to
empty), and the first validator **accepted** the real `2010_bacp` shape -- a complete
solve item followed by another writer's tail, which neither a solve-item count nor a
trailing-semicolon check can see. A validator that rejects everything is as bad as one
that rejects nothing, so both polarities are asserted.

**Before the next full run**, note it needs about 14 GB of `log/` per 436 instances, and
that `report` will refuse to total a run with no `DONE-` line. Re-running is cheap:
re-invoke with the same arguments and only the missing rows are computed.

## Node trap: `eval "$(opam env)"` silently no-ops over non-interactive ssh

**2026-09-23, found by agent-harness while launching the wave-28 corpus run.** On
`fataepyc-07`, `ssh host 'eval "$(opam env)"; dune build …'` does **nothing** — `opam` is not
on the default non-interactive `PATH`, so the `eval` expands to empty, `dune` is never found,
and **the previously built binary stays in place**. The build appears to scroll past and the
run then measures the *old* solver.

Use `PATH=$HOME/.local/bin:$PATH` before `opam env` in any non-interactive ssh command.

**This is the third instance of one failure mode in this project**: a before/after comparison
whose two sides unknowingly used the same binary (CLAUDE.md records the first two, both on
2026-09-17). It was caught here only because the launch brief required hashing the binary on
both sides. **Hash the binary, every time** — the failure is silent by construction, and in
this case the wrong hash (`edd7d8ff…`, three days old) was the only evidence anything was
wrong. The correct build hashes `605ede271e0df93745b96b04acb8dc25`.

Wave-28 corpus run: `/scratch/arthur/corpus-out-w28`, `PAR=64` (matched to the previous run so
the `TIMEOUT-SOLVE` column stays load-comparable), 436 **distinct** instances. Read it with
`scripts/corpus_run.sh --report /scratch/arthur/corpus-out-w28`.

**Do not subtract this run's `REFUSED-MODEL` from D-0068's 248.** That run had 353 distinct
ids over 436 rows; this one has 436 distinct instances, so 83 of these models were never
measured before. They are new measurements, not deltas. The only like-for-like comparisons
are the 103 re-run suspects (17 verified) and `2012_tpp`, a single named instance.
