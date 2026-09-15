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
| M1-T18 | Adopt the Rust VeriPB **3.0.2** checker while still emitting format 2.0 | TODO | phase 1 of the upgrade. No proof changes: 3.0.2 reads our 2.0 proofs unchanged. Already installed at `~/.cargo/bin/veripb`, shadowed on PATH by the Python 2.2.2 |
| M1-T19 | Migrate proof **emission** to format 3.0 | TODO | phase 2. **Supersedes D-0002, needs its own decision record.** The prize is labels, which delete the `=`-counts-as-two-constraints id trap in PROOF-FORMAT section 2 |
| M1-T20 | Correct `test_matrix.ml`'s empty-cell note and fill the four `int_ne` shape cells | TODO | M1-T17 fixed the factless trace line; the note still says those cells are unreachable |
| M1-T21 | A bool *parameter* folded to a `Const` prints as `0`/`1`, not `false`/`true` | DONE | `output.ml` sees an int and cannot tell; the type is lost in `Model.t`. Real output-correctness bug, independent of the proof |

## M2 — Booleans

| ID | Task | Status | Notes |
|---|---|---|---|
| M2-T1 | `bool_clause`, `array_bool_or`, `array_bool_and` | TODO | |
| M2-T2 | `bool2int`, `bool_eq`, `bool_not` channelling | TODO | |
| M2-T3 | Clause learning from conflicts (1UIP), with proof steps | TODO | the big one |
| M2-T4 | Learned-clause deletion + matching proof `del` | TODO | |

## M3 — reification, and the explanation question

| ID | Task | Status | Notes |
|---|---|---|---|
| M3-T0 | **Resolve D-0003** — what "higher-order explanation" means here | TODO | blocks T2 |
| M3-T1 | `red`-based definitions for reified variables | TODO | |
| M3-T2 | Reified linear/comparison propagators + justifications | TODO | blocked by T0 |
| M3-T3 | Benchmark: proof-logging overhead vs. unlogged, report in `bench/` | TODO | first performance checkpoint |

## M4 — global constraints

| ID | Task | Status | Notes |
|---|---|---|---|
| M4-T1 | `all_different` (bounds consistent) + Hall-interval justification | TODO | see D-0004 |
| M4-T2 | `all_different` domain consistent (Régin) — proof story is research-grade | TODO | |
| M4-T3 | `array_int_element` | TODO | |
| M4-T4 | `int_times`, `int_div`, `int_abs` | TODO | |

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
