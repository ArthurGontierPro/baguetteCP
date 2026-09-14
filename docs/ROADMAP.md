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
| M0-T2 | `scripts/bootstrap.sh` installs opam + OCaml 5 + deps; `dune build` succeeds | WIP | **start here** — no toolchain on this machine yet |
| M0-T3 | The scaffolded OCaml compiles and `dune runtest` is green | WIP | scaffold was written without a compiler present; expect type errors |
| M0-T4 | CI-equivalent: `make check` gate documented and working | TODO | |

## M1 — linear integer core, proved

Goal: solve models with only linear integer constraints, and VeriPB accepts every proof.

| ID | Task | Status | Notes |
|---|---|---|---|
| M1-T1 | `Domain` with bounds + lazy holes, unit tested | WIP | |
| M1-T2 | `Store`: domains + trail, decision levels and undo | WIP | |
| M1-T3 | `Explanation` type + arena + memoised `Deferred` | WIP | central; claim it alone |
| M1-T4 | Order encoding in `lib/proof/lit.ml`, `.opb` writer | WIP | see PROOF-FORMAT §3 |
| M1-T5 | `writer.ml`: rule emission, constraint ids, audit mode | WIP | |
| M1-T6 | FlatZinc lexer + parser for the §2.1 subset | WIP | independent of core — good parallel task |
| M1-T7 | `int_lin_le` propagator + `pol` justification | TODO | the reference propagator; copy its shape |
| M1-T8 | `int_lin_eq`, `int_le`, `int_lt`, `int_eq` | TODO | after T7 |
| M1-T9 | `int_lin_ne`, `int_ne` (needs direct encoding) | TODO | |
| M1-T10 | DFS search with first-fail, decisions logged in the proof | TODO | |
| M1-T11 | End-to-end: 5 small models solve and verify | TODO | the milestone gate |

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
