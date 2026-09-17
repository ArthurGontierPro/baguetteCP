# Worklog

Coordination between concurrent Claude sessions. **Append only.** Add rows at the bottom
of a section; never reflow, reorder or rewrite rows you did not write. That is what makes
git merge two sessions' edits instead of conflicting.

Read this file at the start of every session. Claim before you edit. See `CLAUDE.md`.

---

## Active claims

**No sessions are running.** Waves four and five are merged and released; the claims table is empty. Round dispatched 2026-09-16 by the orchestrator, one
git worktree each (`.claude/worktrees/<tag>`), so no two share `_build`'s global lock.

| Task | Files being touched | Session | Since |
|---|---|---|---|
| M1-T65 (measuring first) | `lib/proof/encoding.ml`, `lib/flatzinc/compile.ml`, `test/unit/test_flatzinc.ml` | orchestrator | 2026-09-17 |
| M2-T8 | **all of `lib/core/**`**, plus the `test/unit/*.ml` its signature change breaks | agent-iface | 2026-09-17 |
| M1-T29 | `lib/proof/writer.ml`, `test/unit/test_proof.ml` | agent-del | 2026-09-17 |

Two rounds are recorded in `## Completed` below. The rows that stood here on
2026-09-15 (`integration`, M1-T12, M1-T13) were stale — see the handoff note "the
claims table had rotted" — and the round dispatched after it (M1-T18/T19 agent-proof3,
M1-T20 agent-matrix, M1-T21 agent-output, one worktree each so that no two shared an
`_build` lock) is merged and released.

## Cross-session requests

Need a change in a file someone else has claimed? Write it here and move on to other
work. The owning session picks it up.

| Request | For file | From | Status |
|---|---|---|---|
| `lib/proof/lit.ml` is a shared dependency: agent-proof may **add** to it but must not change the existing signatures of `pbvar`, `t`, `ge`, `le`, `eq`, `ne`, `negate`, `to_string`, `var_name`, since agent-core compiles against them | `lib/proof/lit.ml` | orchestrator | standing |
| `WORKLOG.md`, `docs/**`, `dune-project`, `Makefile`, `scripts/**` and all committing are held by the orchestrator this round — agents touch none of them | — | orchestrator | standing |
| **M1-T46**: `lib/core/search.ml:260-261` quotes veripb 2.2.2's `"Constraint is not a contradiction"`. 3.0.2 shares **no substring** with it. Prose only — please widen the comment to name both wordings, as `ne.ml` and `test_random.ml` now do. Do not match on either alone anywhere | `lib/core/search.ml` | orchestrator | open, for agent-rootfix |
| **M1-T50, and a possible lead on M1-T44**: when the fact comes from a **decision**, `linear.ml` emits `pol <own row> <own row> +` — `Trivial` resolves to `ctx.model_id ()` at `justify.ml:288`, so the step derives twice the propagator's own row where the fact belongs. Confirmed by the orchestrator by reading `justify.ml:288` and `linear.ml:317,352`. **Worth checking against M1-T44's chain, which cancels to `0 >= 0`** — a citation that degenerates to the same row twice is exactly the shape that cancels. Do not treat this as a mandate to change `linear.ml` if your diagnosis says otherwise; it is a lead, not a conclusion | `lib/core/linear.ml`, `lib/core/justify.ml` | orchestrator | open, for agent-rootfix |
| **M1-T46**: same, at `test/unit/test_proof.ml:1125` and `:1150` — the second is an assertion *message*, so a reader who trips it gets told to look for a string 3.0.2 never prints | `test/unit/test_proof.ml` | orchestrator | open, for agent-proofhyg |
| **All `dune` files are orchestrator-owned.** `lib/core/dune` already has `(include_subdirs unqualified)` so a new `lib/core/prop/*.ml` needs no dune edit, and `test/unit/dune` already names `test_prop` and `test_justify`. Need another module named? Ask here | `**/dune` | orchestrator | standing |
| `lib/proof/encoding.ml` is now claimed by agent-encoding, and `lib/core/justify.ml` compiles against `Encoding.is_declared`: agent-encoding may **add** to encoding.ml but must not change the signature of anything already there | `lib/proof/encoding.ml` | orchestrator | standing |
| `lib/core/justify.ml`, `lib/core/explanation.ml`, `lib/core/prop/order_reason.ml` and `lib/proof/**` are **read-only** for both sessions this round: read them freely, edit none of them. Need a change? Write it here | — | orchestrator | standing |
| M1-T14 is split in two along a contract stated in full in the dispatch, not merely a type (the D-0009 lesson): agent-compile owns `lib/flatzinc/compile.ml` only; agent-output owns `lib/flatzinc/output.ml` and the `check_assignment` addition to `lib/flatzinc/model.ml` only. Neither touches `bin/main.ml`, any `dune` file, or the other's files; the orchestrator owns the wiring and the integration | `lib/flatzinc/**` | orchestrator | standing |
| M1-T7 is split across two sessions. The contract between them is the **existing** `Explanation.t` ADT in `lib/core/explanation.ml`, which neither may change: agent-core builds `Linear`/`Cut` values, agent-justify renders any of them. A change there is a cross-session request, not an edit | `lib/core/explanation.ml` | orchestrator | standing |
| **This round's split (D-0018).** agent-trace owns the trace vertical in `lib/core/`; agent-ne owns the direct encoding and `int_ne`; agent-mutate owns the mutation harness. The contract between agent-trace and agent-ne is that `Encoding` and `Lit` may only be **added** to — `Encoding.is_declared`, `Lit.ge/le/eq/ne/negate/to_string/owner` keep their current signatures, since `justify.ml` compiles against them | `lib/proof/encoding.ml`, `lib/proof/lit.ml` | orchestrator | standing, this round |
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
| M2-T11's **code** is merged but its **evidence is not**: the byte-identity check across the model suite was never reported, and the suite has since grown from 15 models to 20. Treat "the 20 models are unchanged by seeded branching" as unverified until agent-fuzz2 reports hashes. The gate passing is necessary but not sufficient — it would not catch a proof that changed yet still verifies | `test/models/**` | orchestrator | open |
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
| **Wave eight, dispatched 2026-09-17. Same shape as wave seven and for the same reason**: M2-T8 rewrites the propagator interface, so it needs all of `lib/core`. agent-del works in `lib/proof` only; the orchestrator holds `Makefile` and `scripts/**`. **M2-T3 is still not dispatched** — M2-T8 is its precondition and M2-T9 follows M2-T8 | — | orchestrator | standing, this round |
| **`lib/proof/writer.ml` is agent-del's and `lib/core/justify.ml` is agent-iface's, and they meet at the rule-emission boundary.** agent-del may **add** to `writer.ml` but must not change the signature of `pol`, `rup`, `rup_clause`, `implied`, `pol_concluding`, `fresh`, `delete`, `delete_many`, `wipe_level` or `del_run`, because `justify.ml` compiles against them and agent-iface is rewriting that file. A change there is a request here | `lib/proof/writer.ml` | orchestrator | standing, this round |
| **Wave seven, dispatched 2026-09-17. Three sessions, and the split is dictated by M2-T7's footprint.** M2-T7 threads the propagator instance id onto the trail and onto `Conflict`, which reaches ~110 call sites across seven test files and nearly every module in `lib/core`. So agent-instid gets **all of `lib/core`**, and the only parallel work is outside it: agent-widthcap in `lib/proof` + `lib/flatzinc`, and agent-property read-only. Do not add a fourth session in `lib/core` this round | — | orchestrator | standing, this round |
| **M1-T58 landed mid-round (bf9c84c), so agent-widthcap's dependency is gone.** Its brief said a row refused at `Encoding`'s door would surface as an uncaught exception; it now gets a positioned diagnostic and exit 4. If the report still says "uncaught exception pending M1-T58", that is stale and the orchestrator's fault for dispatching before fixing it, not the agent's | `bin/main.ml` | orchestrator | CLOSED |
| **I-X10 and D-0040 landed mid-round and they bear on `lib/core/prop/`, which agent-instid holds.** Nothing to change for M2-T7 — I-X10 is about what the checker accepts, not about the trail — but **read D-0040 before M4**, and note M1-T62: `Store.remove` and `Store.fix` are live, exported, have **no `lib` callers**, and silently record `no_facts`, which is the I-P5 violation that caused a real bug at M1-T17. If M2-T7's threading gives you a natural moment to make `no_facts` unreachable from `lib/`, take it and say so; if not, leave it — the tests use `Store.remove` deliberately to construct the factless case they assert against, so deleting it is not obviously right | `lib/core/store.ml` | orchestrator | open, for agent-instid to consider |
| **The M1-T25 coupling stayed quiet, as hoped.** Neither agent-instid nor agent-widthcap touched the `Order_reason.weaken_declared` / `Encoding.expand_int_lin_le` substitution, and all 102 proof artefacts are byte-identical across both merges. Closing this for the round; re-open it the moment anyone changes the row's shape | `lib/core/prop/order_reason.ml`, `lib/proof/encoding.ml` | orchestrator | CLOSED for wave seven |
| **I-S4 is still unchecked, and M2-T7 did not change that.** agent-instid confirmed it added no cross-level assertion: `entry.prop` supplies the material for one, but the missing check is about **levels**, not identity, and `Trace` already has `Store.level_of_index`. **Whoever takes M2-T3 owes this check** — a learned clause citing across levels is exactly the case I-S4's level-discipline argument does not cover | `lib/core/**` | orchestrator | open, for M2-T3 |
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

**UPDATE 2026-09-16 (orchestrator): this is now ENFORCED, not requested.** Two further test binaries had to be killed at the ceiling after sessions were warned, so warning is evidently not a control. `make`, `scripts/run_model_tests.sh` and `scripts/verify_proof.sh` apply `ulimit -v 4000000` themselves; `CLAUDE.md` carries the rule where every session reads it first. The cap is verified to bite (5 GB allocation -> `MemoryError`, 100 MB fine, gate peaks at 18.5 MB). **A bare `dune runtest --root .` in a worktree is still uncapped** — that is M1-T53, and until it lands, wrap your runs yourself: `(ulimit -v 4000000; timeout 900 dune runtest --root .)`. A run that dies against the cap is a finding to report, not a cap to raise.

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
