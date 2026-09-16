# Roadmap

Task IDs here are what sessions claim in `WORKLOG.md`. Keep IDs stable once published —
they are referenced from commits and claims.

Status: `TODO` / `WIP` / `DONE` / `BLOCKED`. Update your own task's status; do not reflow
this file (see the append-only note in `CLAUDE.md`).

---

## M0 — it builds

Goal: `make check` passes on a skeleton. Nothing solves anything yet.

| ID | Task | Status | Notes |
|---|---|---|---|
| M0-T1 | Project skeleton, dune files, Makefile | DONE | scaffolded |
| M0-T2 | `scripts/bootstrap.sh` installs opam + OCaml 5 + deps; `dune build` succeeds | DONE | opam 2.5.2, switch `baguette` on OCaml 5.1.1 |
| M0-T3 | The scaffolded OCaml compiles and `dune runtest` is green | DONE | 253 unit checks |
| M0-T4 | CI-equivalent: `make check` gate documented and working | DONE | green; unsolved models are `xfail` via `test/models/PENDING` |

## M1 — linear integer core, proved

Goal: solve models with only linear integer constraints, and VeriPB accepts every proof.

| ID | Task | Status | Notes |
|---|---|---|---|
| M1-T1 | `Domain` with bounds + lazy holes, unit tested | DONE | |
| M1-T2 | `Store`: domains + trail, decision levels and undo | DONE | |
| M1-T3 | `Explanation` type + arena + memoised `Deferred` | DONE | central; claim it alone |
| M1-T4 | Order encoding in `lib/proof/lit.ml`, `.opb` writer | DONE | see PROOF-FORMAT §3 |
| M1-T5 | `writer.ml`: rule emission, constraint ids, audit mode | DONE | |
| M1-T6 | FlatZinc lexer + parser for the §2.1 subset | DONE | independent of core — good parallel task |
| M1-T7 | `int_lin_le` propagator + justification | DONE | verified end to end against veripb; `rup` not `pol`, see D-0009 |
| M1-T7a | `int_lin_le` propagator and its explanations | DONE | the reference propagator; copy its shape, and its `order_reason` chains (D-0010) |
| M1-T7b | `Justify`: explanation to VeriPB rules | DONE | `Linear` states its own terms as `rup`; memo dropped in lockstep with the writer's wipe |
| M1-T7c | Order-encoding expansion of `sum a_i x_i` into a PB row | DONE | `Encoding.expand_int_lin_le`; the consistency clauses are load-bearing |
| M1-T8 | `int_lin_eq`, `int_le`, `int_lt`, `int_eq` | DONE | one instance per model row, not one fused propagator (D-0011) |
| M1-T9 | `int_lin_ne`, `int_ne` | DONE | D-0019: it does **not** need the direct encoding — a `rup` target is a clause. Propagator + proof verify, and M1-T11 wired both builtins into `compile.ml` |
| M1-T10 | DFS search with first-fail, decisions logged in the proof | DONE | the answer is right everywhere; the branch-nogood *proof* is open (D-0012) |
| M1-T11 | End-to-end: 5 small models solve and verify | DONE | **14 of 14** solve and verify, and `test/models/PENDING` is empty for the first time. `int_ne`/`int_lin_ne` wired into `compile.ml`, plus five disequality models — `ne_sat` could not see `int_ne` break, since `int_lt` alone solves it |
| M1-T12 | Make the D-0013 derivation real: `Combine`/`Weaken`/`Model_row` + the root conflict | DONE | D-0015; root refutations now verify |
| M1-T13 | The branching half of D-0013: justify a conflict reached under decisions | DONE | D-0018 + D-0021. One `rup` line per pruning, root prunings included; the nogood is ordinary `rup` along it. `chain_sat` and the three D-0012 parity models verify |
| M1-T14 | Wire the CLI: `.fzn` in, solution + proof out | DONE | 5 models solve with verified proofs; `Compile` + `Output` + `Model.check_assignment` |
| M1-T15 | Proof-mutation harness: corrupt a step, assert veripb rejects | DONE | D-0020: found `lin_unsat`'s refutation carries a unit of slack, registered known-slack with XPASS protection |
| M1-T16 | Populate the tests: a per-propagator × per-situation matrix, and a randomised differential tester | DONE | found 3 real bugs, 2 of them new. 142 + 10 checks, 17 verified break-it mutations |
| M1-T17 | Fix the three `int_ne` composition bugs M1-T16 pinned | DONE | D-0022, I-X7, I-P5. Gate green: 147 matrix + 11 fuzzer checks |
| M1-T18 | Adopt the Rust VeriPB **3.0.2** checker while still emitting format 2.0 | DONE | phase 1 of the upgrade. No proof changes: 3.0.2 reads our 2.0 proofs unchanged. Already installed at `~/.cargo/bin/veripb`, shadowed on PATH by the Python 2.2.2 |
| M1-T19 | Migrate proof **emission** to format 3.0 | DONE | D-0023/D-0024/D-0025. 3.0 is the default; 2.0 still emitted under `BAGUETTE_PROOF_FORMAT=2.0` and green too. Labels delivered the id trap's closure, with two qualifications recorded in D-0023 |
| M1-T20 | Correct `test_matrix.ml`'s empty-cell note and fill the four `int_ne` shape cells | DONE | M1-T17 fixed the factless trace line; the note still says those cells are unreachable |
| M1-T21 | A bool *parameter* folded to a `Const` prints as `0`/`1`, not `false`/`true` | DONE | `output.ml` sees an int and cannot tell; the type is lost in `Model.t`. Real output-correctness bug, independent of the proof |
| M1-T22 | `del range` is half-open: fix `Writer.wipe_level`, correct PROOF-FORMAT §5 | DONE | **Verified bug.** veripb 3.0.2 deletes `[LO, HI)`; we emit `del range lo hi` for the *inclusive* run, so every multi-id run leaves its last id live in the checker while `tags`/`live` drop it (I-X3). 7 lines across 5 of 14 models today. Not unsound — proof growth. See `docs/GCS-COMPARISON.md` §2.1 — **Premise re-measured before fixing**, with controls: 3.0.2 deletes `[LO, HI)`. `del range` lines 7 -> 4, the deleted set is now exact (7 ids that leaked are retired), proofs +0.4% bytes, no solution changed. The regression test asks the *checker* whether each id is still live, because the pre-existing string assertion pinned the buggy text and was green for the bug's whole life |
| M1-T23 | Checked arithmetic in `Linear`/`Ne`; cap declared domains at compile time | DONE | **The only soundness gap found.** No overflow handling exists anywhere in `lib/`; a wrapped product prunes wrongly *and* writes the `.opb` row from the same wrapped arithmetic, so veripb accepts it. Add an overflow axis to `test_matrix.ml`. Independent — good parallel task — **D-0029**, and a normative arithmetic-limit paragraph in SPEC 2.1. Gap reproduced by the orchestrator independently: the model answered UNSAT with `s VERIFIED UNSATISFIABLE` because the `.opb` row and the propagator wrapped identically. Now refused at compile time, exit 3. `lib/core/checked.ml`, cap `max_int/16` derived from a `9M+6` envelope and asserted as a test. 1005 unit checks, 17/17 models, gate peak RSS 42 MB |
| M1-T24 | Trail-cursor walk in `Engine.propagate`, replacing `Store.trail_entries` | DONE | `engine.ml:60` allocates the whole trail per propagator call and keeps only the newest `n_new`; `Store.trail_entry` already gives O(1) indexed access and its own comment says so. Pure perf, no invariant touched |
| M1-T25 | Lazy order-encoding atoms: `.opb` carries bounds, ladder steps enter the proof by `red` on demand | TODO | `declare_int` writes `hi - lo - 1` rows per variable eagerly and uncapped — `var 0..1000000: x` is a million-row `.opb`. `Encoding.ensure_direct` is already this pattern for the direct encoding. SPEC/PROOF-FORMAT §3 change + decision record. Does **not** fix width-proportional *reasons* — that is M1-T27 |
| M1-T26 | Move mutation knobs from proof text into the emitter; add a mandatory control lane | WIP | `mutate_proof.sh`'s own header records that `drop-line` now fails as a *parse* error under 3.0 (it un-defines the label), so the lane is green for a reason unrelated to the derivation — the D-0020 failure mode. GCS types the knobs next to each derivation |
| M1-T27 | Decision record: bound-fact chains are width-proportional; state the policy | DONE | `order_reason.ml:38-43` builds one literal per value between declared and current bound (D-0010 requires the chain); D-0005's hole-span cap does not cover it. Doc-only now; the interval restatement is M4 work — **D-0028.** Row text was wrong and is corrected here: `order_reason.ml:38-43` (`lower_bound_terms`) has **no caller in `lib/`** — orchestrator confirmed, only `test_prop.ml` calls it. The live object is `Order_reason.weaken_declared` (`linear.ml:267`), which spans the **whole declared width**, not the declared-to-current prefix. Measured: two vars at `0..999999` and one row infeasible on declared bounds, so **zero prunings**, still emit a 29.8 MB proof line of ~2M literals and a 156 MB `.opb`. Reasons are already width-independent, so M2-T8 does **not** fix this |
| M1-T28 | Index-walk the trail in `linear.ml`'s `find_lo_reason`/`find_hi_reason` | TODO | Found by M1-T24. The same defect it fixed in `engine.ml`, still present twice in `lib/core/prop/linear.ml` (~172, ~186): the scan stops early on a match but `Store.trail_entries` allocates the whole trail first, and it runs **once per term per pruning** rather than once per propagator call. A downward `Store.trail_entry` walk fixes both identically. **Check M2-T8 first** — it proposes deleting this scan outright, so this may be a throwaway interim fix; take it only if M2-T8 is still far off. Measured context: M1-T24's synthetic 12000-entry-trail benchmark went 4.22s→1.56s and the agent judged the residual to be mostly these two scans — unverified |
| M1-T29 | The `del id` fallback line grows with the reasons retired at one level | TODO | Found by M1-T22. When a wiped run ends at the newest id there is no label one past it, so the run is emitted as a full `del id` list rather than a range. Invisible today (+0.4% bytes, 3 of 7 sites) but O(reasons) per backtrack on a deep search. A numeric exclusive bound would keep it O(1) — 3.0.2 tolerates one past the last id, measured — but that reintroduces bare-integer citation, which D-0023's labels removed. **Unmeasured**; same gap D-0024 already flags. Revisit before M2-T3 |
| M1-T30 | A wide-domain model in `test/models/`, so the gate can see width at all | WIP | Found by M1-T27/D-0028. The widest declared domain in the whole suite is `var 0..9`, so **no test can observe** the width-proportional cost D-0028 measures, nor M1-T25's eager `.opb`. Cheap witness, shape recorded in D-0028: two variables, one row infeasible on the declared bounds, zero prunings, w ~ 10^3 — about 24 kB of proof and 42 ms to verify. This is the project's signature failure mode (a cost no test can reach), which is why it gets its own row |
| M1-T31 | Remove the ambient model row: make `Linear.make`'s `?row_id` required, delete `Justify.emit`'s `Trivial -> ctx.model_id ()` arm | TODO | Found by M1-T27. `search.ml:323,338` pushes a decision with `Explanation.trivial`; `find_lo_reason`/`find_hi_reason` can return that entry, `summand_of_snap` wraps it as `Term (|a|, Trivial)`, and `Justify.emit` then renders it as the **ambient** row — which is not what established that bound. Latent, not observed: unreachable today only because a `Combine` is emitted solely at a root conflict (`offset_unsat` branches at every level and has 31 `rup`, **0** `pol` — orchestrator confirmed). Makes D-0011's original ambiguity a type error, the move D-0015 made for `Weaken`. **Before M4-T1**, and before D-0018 point 2's per-push `pol` path is first used |
| M1-T32 | State and enforce "`Compile` is the only door": check the arithmetic inside `Encoding`/`Opb` too | TODO | From D-0029. `lib/proof/encoding.ml` and `lib/proof/opb.ml` still compute unchecked and are safe *only* because `Compile` caps what reaches them. Nothing states that invariant, and `test_matrix.ml`'s own `build` already calls `Encoding` directly, so a second entry point can still write a corrupted row. A `Checked`-based assertion in `Encoding.linear_terms_int_lin_le` closes it. Not a live bug — an unstated invariant, which is how the first one got in |
| M1-T33 | Make I-S1's oracle genuinely independent: `Model.check_assignment` must not share the propagator's arithmetic | TODO | From D-0029. It evaluates `sum a_i v_i` with the same wrapping `+`/`*` as the code it exists to check, so on the overflow class it agreed with the bug. Under the cap it cannot overflow today, so this is about the *value of the oracle*, not a live defect: an independent check that shares a failure mode with its subject is not independent. Consider arbitrary-precision or a different evaluation order |
| M1-T34 | `bin/main.ml` should catch `Checked.Overflow` and exit with a diagnostic | TODO | From D-0029. Unreachable through the cap, so belt-and-braces only: if it ever fired the CLI would die on an uncaught exception rather than a positioned error. Small |

## M2 — Booleans

| ID | Task | Status | Notes |
|---|---|---|---|
| M2-T1 | `bool_clause`, `array_bool_or`, `array_bool_and` | TODO | |
| M2-T2 | `bool2int`, `bool_eq`, `bool_not` channelling | TODO | |
| M2-T3 | Clause learning from conflicts (1UIP), with proof steps | TODO | the big one |
| M2-T4 | Learned-clause deletion + matching proof `del` | TODO | |
| M2-T0 | **Amend D-0011**: D-0015's `Model_row` closed its ADT gap, so multi-row derivations are permitted | DONE | A literal reading of D-0011 forbids writing a Hall-interval justification at all, and GCS's cites one line per Hall value *and* per Hall variable. Decision record only, no code. **Must land before M4-T1** — **D-0027.** Restated as a rule about *naming* rows, not counting them: citation is unrestricted, so M4-T1's Hall justification is writable with no further decision. The decomposition default stands and `int_lin_eq` is **not** re-fused. Grounded in shipped output — `lin_unsat` already emits a one-`Combine` derivation citing two instances' rows, verified since M1-T12, so the literal reading was already false of working code |
| M2-T5 | `Domain.result` reports change granularity; engine masks wakes by trigger kind | TODO | Delivers what `ARCHITECTURE.md` §2 already promises (`NoChange \| Bound \| Holes`) and the code never did. Ship a `BAGUETTE_DEBUG` I-P2 re-run check in the same round — I-P2 currently has no test, and a skipped wake is invisible except in the node count |
| M2-T6 | Do not re-wake a propagator from its own prunings; aliased-scope veto + claim re-checker | TODO | `linear.ml:22-29` claims single-pass idempotence; `engine.ml:97-98` re-enqueues it anyway. Copy GCS's two guards, not its claim/replay engine. Adopt the re-checker in the *same commit* (GCS #889: 767 → 1,089,375 nodes). Depends on M2-T5; re-run the proof suite, not just unit tests |
| M2-T7 | Record the propagator instance id on every trail entry and on `Conflict` | TODO | Closes D-0011's own named blocker ("the trail records no propagator identity… should be closed before M2-T3 starts, not during it"). Lets `Store.conflict_facts`' one-shot slot go. **Blocks M2-T3** |
| M2-T8 | Propagator interface v2: declarative `Reason` + separate `Justification` (D-0026) | TODO | Collapses I-P4 + I-P5 into one obligation, deletes `linear.ml`'s per-pruning trail scan (`O(n·\|trail\|)` → `O(n)`), and is the precondition for M2-T3, M3-T4 and M4. **Non-narrowable reasons only** — the narrowable form contradicts I-X6. Depends on M2-T7; before M2-T3 |
| M2-T9 | Literal → defining-proof-line index in `Justify.ctx`, populated by `Trace` | TODO | Closes D-0009's "not today" by adding the field it names as missing; `Justify` already has the level-tagged memo and lockstep wipe. May also close D-0019's clause-in-a-`pol` gap — **verify, do not assume**. Depends on M2-T8 |
| M2-T10 | Harness: per-node consistency checking against the brute-force oracle | TODO | Nothing verifies the `consistency` tag that SPEC 2.2 makes normative; today's oracle checks soundness only. Must assert **at least** the declared level — `ne.ml` deliberately declares the weaker `Value`, and weakening a test to match is forbidden. Needs a search trace hook |
| M2-T11 | Fuzzer: randomise branching order from the announced seed | WIP | One seed already drives model generation; drive variable/value choice from it too. M1's whole nogood story is that the branch's own trace supports the refutation, so a different tree is a different trace. Depends on M1-T16 |

## M3 — reification, and the explanation question

| ID | Task | Status | Notes |
|---|---|---|---|
| M3-T0 | **Resolve D-0003** — what "higher-order explanation" means here | TODO | blocks T2 |
| M3-T1 | `red`-based definitions for reified variables | TODO | |
| M3-T2 | Reified linear/comparison propagators + justifications | TODO | blocked by T0 |
| M3-T3 | Benchmark: proof-logging overhead vs. unlogged, report in `bench/` | TODO | first performance checkpoint — **superseded in scope by M3-T5** |
| M3-T4 | Reification dispatcher: author supplies enforce-hold / enforce-not-hold / entailment; framework does the collapse and contrapositive | TODO | Turns M3-T2 from "reified linear *and* reified comparison, each with five cases" into two propagators plus one shared helper (~200 lines). Known limitation to inherit knowingly: one trigger set per dispatcher. Depends on M2-T8 and M3-T0 |
| M3-T5 | Proof benchmark reporting `.opb` bytes, `.pbp` bytes **and** verify seconds separately | WIP | Absorbs M3-T3. GCS measured size and verify time moving in *opposite* directions at an identical search tree (5.9× smaller proof, 3.5× longer to check), so a size-only benchmark misleads. **Also the named falsifier for D-0026's performance prediction.** Take minimums, one at a time |

## M4 — global constraints

| ID | Task | Status | Notes |
|---|---|---|---|
| M4-T1 | `all_different` (bounds consistent) + Hall-interval justification | TODO | see D-0004. **Unblocked 2026-09-16 by D-0027**, which permits the multi-row Hall derivation outright. Land the ambient-row removal (M1-T31) first. Build T1 and T2 as *one propagator with two stages*, not two propagators (below) |
| M4-T2 | `all_different` domain consistent (Régin) — proof story is research-grade | TODO | **Design change from the GCS comparison**: one propagator, one consistency tag, two stages — the cheap value-consistency pass first, returning without an idempotence claim so cheaper propagators react before the matching/SCC work. GCS's cutoff is measured, not chosen: 256 var-value pairs, sitting at the geometric mean between a case 1.36× faster staged and one ~2% slower |
| M4-T3 | `array_int_element` | TODO | |
| M4-T4 | `int_times`, `int_div`, `int_abs` | TODO | **split into T4a/T4b below** |
| M4-T0 | Views (`±x + k`) and constants-as-variables in `Var`/`Store` | TODO | Should precede M4-T3: a 1-based `array_int_element` index is a view, not an auxiliary variable. GCS's aux-variable alternative "silently downgraded" every value-pruning propagator behind it (4/15 → 9/15 optimal on one family once fixed). Opens a proof-side question: each view needs its own range literals |
| M4-T4a | Integer interval arithmetic as a standalone, proof-free, unit-tested module | TODO | Port of GCS's `product_bounds.hh` (~178 lines of pure functions, no solver types): `div_floor`/`div_ceil` (**not** truncating division — the trap `linear.ml:138-142` already works around), `isqrt`, four-corner `product_bounds`, `square_bounds` kept separate, `square_filter`/`quotient_filter`. Testable against brute force today. Good parallel task |
| M4-T4b | `int_times`/`int_div`/`int_abs` over M4-T4a | TODO | Needs **two SPEC additions first**: division rounding (GCS pins truncation toward zero, remainder taking the dividend's sign) and division by zero as *relational* rather than an error (zero has no support in the divisor's domain — matches MiniZinc and XCSP3). Anchor the family on one total `is_in_relation` predicate shared with `Model.check_assignment`. Depends on M4-T4a, M2-T8 |
| M4-T5 | RUP hints on trace lines and nogoods, gated on M3-T5 showing they are needed | TODO | Hinted `rup` is O(hints), hint-free is O(live database) — worth 6–14× on a real model but 25% on a toy one. **All-or-nothing**: an engaged-but-empty hint list restricts propagation to nothing, so half-hinting the D-0018 trace chain breaks a working proof. Depends on M3-T5, M2-T9 |
| M4-T6 | **Spike** (not a build): in-proof tabulation as the GAC route for small-domain relations | TODO | Would give GAC arithmetic for ~10 lines per constraint with *no OPB change*, because the table is derived in-proof. **Unverified that this transfers to our order encoding** — that is why it is scoped as a spike. Depends on M4-T4b |

## M5 — optimisation

| ID | Task | Status | Notes |
|---|---|---|---|
| M5-T1 | Branch and bound, `obju` / `o` / `core` rules | TODO | |
| M5-T2 | `conclusion BOUNDS` for proved optimality | TODO | |
| M5-T3 | MiniZinc challenge instances as a regression set | TODO | |

## M6 — performance

Deliberately last. Do not start before M4 is green.

| ID | Task | Status | Notes |
|---|---|---|---|
| M6-T1 | Profile; establish the propagation hot path | TODO | |
| M6-T2 | Minor-GC pressure: move domains/trail to `Bigarray`/`Bytes` | TODO | the known OCaml risk, D-0001 |
| M6-T3 | Proof-writing buffered/batched off the hot path | TODO | |
| M6-T4 | Compare against Chuffed and the Glasgow solver on a shared set | TODO | |
