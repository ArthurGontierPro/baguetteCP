# baguette

A constraint programming solver with VeriPB proof logging and higher-order explanations.

baguette reads FlatZinc, solves, and writes a pseudo-Boolean proof that an independent checker
verifies. The proof is a primary output of every run. Every pruning the solver makes has to
justify itself in the proof, and an answer whose proof the checker rejects counts as a failed run.

Written in OCaml 5, single-threaded, deterministic.

## What it does

| Area | What baguette has |
|---|---|
| Input | FlatZinc over integers and Booleans (`docs/SPEC.md` §2.1), directly or through MiniZinc with its own library `mznlib/` |
| Problems | satisfaction, minimisation, maximisation, every improving solution (`-i`, or `-a` on an optimisation model) |
| Proof | VeriPB 3.0, checked by VeriPB 3.0.2. The proof covers the encoding, every propagation, every learned constraint and the final claim (UNSAT, a solution, or optimality bounds) |
| End-to-end verification | under `--e2e`, the proof can also be checked against the `.opb` produced by `cake_pb_cp`, CakeML's verified encoder, so the encoding of the model is no longer trusted. 197 of the 207 test models verify this way (`make e2e`) |
| Integer encoding | order encoding, or a binary (bits) encoding for wide domains. Bits is the default (`--bits-above 0`), `--bits-above none` gives the order encoding everywhere |
| Linear and arithmetic | `int_lin_le`, `int_lin_eq`, `int_lin_ne` and their reified forms, `int_le`, `int_lt`, `int_eq`, `int_ne` and their reified forms, `int_times`, `int_div`, `int_mod`, `int_abs`, `int_min`, `int_max` |
| Booleans | `bool_clause`, `array_bool_and`, `array_bool_or`, `bool_eq`, `bool_not`, `bool2int`, and the rest of the Boolean family through `mznlib` |
| Global constraints, native | `all_different_int` (domain consistent: Hall intervals on the bounds, then a matching over the values), `global_cardinality` (open, closed, low/up), `array_int_element`, `array_int_maximum`/`minimum`, `cumulative` and `disjunctive` (time-table), `regular` (domain consistent), `inverse`, `member` |
| Learning | 1UIP clause learning with minimisation, and pseudo-Boolean conflict analysis (linear combination plus division or rounding), with a swappable retention policy for the learned database |
| Explanations | each pruning carries a declarative reason (an `Explanation` value), turned into `pol` or `rup` steps only when the proof needs them. Reasons are hash-consed so shared sub-proofs are written once |
| Search | the model's search annotation by default (first-fail, smallest value when there is none). Free search with `-f` (activity order alternating with the annotation, Luby restarts, phase saving) |
| Without proof | `--no-proof` runs the same search without writing a proof, as a measurement tool. Its answers are unverified |
| Limits | `--time-limit`, `--max-heap-mb` (a clean refusal before memory runs out), caps on encoding size |
| Symmetries | `tools/symmetry/` finds model symmetries with dejavu, outside the solver (`make sym`) |

Floats, set variables and multi-objective optimisation are out of scope (`docs/SPEC.md` §1).

## Performance on the MiniZinc Challenge

All sixteen editions of the MiniZinc Challenge (2011 to 2026, 1 600 instances, 1 574 flattened),
run with the Challenge's own settings: 1 200 s per instance, 16 GiB of memory, one thread, on an
AMD EPYC 7643. An answer with a proof counts only when VeriPB verifies the proof. Measured on
2026-11-20/22 (`docs/DECISIONS.md` D-0185, release binary `7c880bce`, main `10b3507`).

| Outcome per instance | Default search, with proof | Free search `-f`, with proof | Default search, `--no-proof` |
|---|---|---|---|
| Optimal or UNSAT, proof verified | 251 | **265** | 296 (unverified) |
| Satisfiable, proof verified | 72 | **97** | 84 (unverified) |
| Complete answer, proof check did not finish (VeriPB memory or time) | 35 | 32 | not applicable |
| Timeout at 1 200 s | 700 | 668 | 780 |
| Proof larger than the 16 GB cap | 198 | 173 | not applicable |
| Refused, memory budget reached | 314 | 336 | 398 |
| Crash | 4 | 3 | 16 |
| **Proofs rejected by VeriPB** | **0** | **0** | not applicable |
| Optimisation runs that printed an objective value (optimal ones included) | 933 | 992 | 1 013 |

The first seven rows add up to the 1 574 instances. The crashes are allocation failures against
the 16 GiB limit, which the memory guard of D-0200 now turns into clean refusals.

What proof logging costs, over the instances both runs complete, comparing the run without proof
to the run with proof:

| | median ratio (no proof / proof) |
|---|---|
| wall time | 0.64 |
| peak memory | 0.96 |
| nodes per second | 1.27 |

So proof logging costs time and disk, not memory. Without proof, 113 instances that hit the
memory budget or the 16 GB proof cap become ordinary attempts, and 8 of them end with a complete answer.

Rank in the fixed-search category of each edition, scored against that year's official entrants
by `tools/compare/challenge_rank.py`:

| Edition | 2026 | 2025 | 2024 | 2023 | 2022 | 2021 | 2020 | 2019 | 2018 | 2017 | 2016 | 2015 | 2014 | 2013 | 2012 | 2011 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| entrants | 13 | 10 | 9 | 7 | 7 | 7 | 6 | 8 | 8 | 12 | 11 | 9 | 11 | 11 | 10 | 8 |
| with proof | 12 | 10 | 9 | 7 | 7 | 7 | 6 | 7 | 6 | 12 | 8 | 9 | 11 | 10 | 8 | 8 |
| without proof | 11 | 10 | 9 | 7 | 7 | 7 | 6 | 7 | 6 | 12 | 7 | 9 | 9 | 10 | 6 | 7 |

The other entrants do not log proofs. baguette's score summed over the sixteen editions is 2 789
with proof and 3 237 without.

Two caveats.

- This series ran before the bits encoding became the default (D-0201), so every column above
  uses the order encoding. On an earlier binary the bits encoding raised the summed score with
  proof from 2 712 to 3 441 and cut the proofs over the cap from 214 to 68 (D-0175). A series on
  the current default has not been run yet.
- Free search is stronger in aggregate but not on every model. It wins on 489 instances and loses
  on 336, mostly routing models, so the default stays the fixed search (D-0185 §5).

## Getting started

```sh
scripts/bootstrap.sh     # once: installs opam, OCaml 5, dune, dependencies
make build
make test
make release             # optimised binary in _build_release/default/bin/main.exe
```

## Usage

```sh
baguette model.fzn                          # solve, keep the proof as ./model.opb and ./model.pbp
baguette model.fzn --proof out              # solve, write the proof as out.opb and out.pbp
veripb out.opb out.pbp                      # verify
baguette model.fzn -f                       # free search
baguette model.fzn --no-proof               # solve without a proof (the answer is unverified)
```

Every run writes its proof and keeps it. Without `--proof` the two files are named after the
model and go in the current directory, replacing those of an earlier run of the same model.

`baguette --help` lists every option.

### From MiniZinc

`tools/baguette.msc` registers baguette as a MiniZinc solver, with its own library for the
global constraints it handles natively.

```sh
export MZN_SOLVER_PATH=$PWD/tools
minizinc --solver baguette model.mzn data.dzn                  # solve, keep ./baguette-proof.opb, .pbp
minizinc --solver baguette --proof out model.mzn data.dzn      # and write out.opb, out.pbp
minizinc --solver baguette -t 300000 -s model.mzn data.dzn     # 300 s limit, statistics
```

MiniZinc hands baguette a temporary `.fzn` and not the name of the `.mzn`, so without
`--proof` the proof is kept as `./baguette-proof.opb` and `.pbp`, and baguette says so on
stderr. `--no-proof` works through MiniZinc too.

baguette accepts the MiniZinc standard flags `-a -i -f -n -p -r -s -t -v`. It runs on one
thread and draws no random numbers, so `-p` and `-r` are accepted and change nothing.

### Search

By default baguette follows the model's search annotation. A model without one is searched
first-fail with the smallest value first. There are no restarts. This is the fixed search of
the MiniZinc Challenge.

With `-f` (free search, as with Chuffed) the search alternates between the annotation and an
activity order at each Luby restart, and it keeps the last value of each variable (phase
saving). It is the same as `--search alternate --restarts luby --phase-saving`, and each of
those options can also be given on its own. Free search often helps when the annotation is a
poor order or when there is none. It can also be much slower, so neither search wins on every
model (the Challenge table above, and D-0137 §10 and D-0202 on smaller sets). A run under `-f`
writes a proof the checker verifies, as the default search does.

## Documentation

| | |
|---|---|
| `docs/SPEC.md` | what the solver must do (normative) |
| `docs/ARCHITECTURE.md` | how it is put together |
| `docs/PROOF-FORMAT.md` | the VeriPB contract and encoding |
| `docs/INVARIANTS.md` | properties every change must preserve |
| `docs/ROADMAP.md` | milestones |
| `docs/DECISIONS.md` | why things are the way they are |
| `docs/GLOSSARY.md` | vocabulary |
| `bench/challenge/README.md` | how the Challenge runs are made and where they are kept |
| `scripts/README.md` | the operating manual for the compute node (runs, gates, lanes) |

Contributors, Claude sessions included, start with `CLAUDE.md`.
