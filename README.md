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

All sixteen editions of the MiniZinc Challenge (2011 to 2026, 1 600 instances, 1 575 flattened), run with the Challenge's own settings: 1 200 s per instance, 16 GiB of memory, one thread, on an AMD EPYC 7643. An answer with a proof counts only when VeriPB verifies the proof. Measured on 2026-11-23/24 (`docs/DECISIONS.md` D-0203, release binary `f244c35a`, commit `e1971f6`).

| Outcome per instance | Default search, with proof | Free search `-f`, with proof | Default search, `--no-proof` |
|---|---|---|---|
| Optimal or UNSAT, proof verified | 302 | **346** | 340 (unverified) |
| Satisfiable, proof verified | 74 | **95** | 86 (unverified) |
| Complete answer, VeriPB hit its time limit (3 600 s) | 18 | 26 | not applicable |
| Timeout at 1 200 s | 1 017 | 970 | 992 |
| Refused, memory budget reached | 164 | 138 | 157 |
| Crash | 0 | 0 | 0 |
| **Proofs rejected by VeriPB** | **0** | **0** | not applicable |
| Optimisation runs that printed an objective value (optimal ones included) | 1 060 | 1 149 | 1 079 |

The first rows down to the rejected proofs add up to the 1 575 instances, checked when this table was written. A check that ran out of time or memory is the checker's limit, not a rejected proof, so it is counted apart.

What proof logging costs, over the instances both runs complete, comparing the run without proof to the run with proof:

| | median ratio (no proof / proof) |
|---|---|
| wall time | 0.47 |
| peak memory | 0.91 |
| nodes per second | 1.50 |

Without proof, 41 instances that hit the memory budget or a crash with proof become ordinary attempts, and 2 of them end with a complete answer.

The 817 verified proofs (all proof arms) have a median size of 198 MB, the largest is 23.6 GB and together they were 793.0 GB. They are deleted once checked, their sizes stay in the tables.

Rank in the fixed-search category of each edition, scored against that year's official entrants by `tools/compare/challenge_rank.py` (the free-search arm is scored in this category too, so the rows compare):

| Edition | 2026 | 2025 | 2024 | 2023 | 2022 | 2021 | 2020 | 2019 | 2018 | 2017 | 2016 | 2015 | 2014 | 2013 | 2012 | 2011 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| entrants | 13 | 10 | 9 | 7 | 7 | 7 | 6 | 8 | 8 | 12 | 11 | 9 | 11 | 11 | 10 | 8 |
| with proof | 11 | 10 | 9 | 7 | 7 | 7 | 5 | 7 | 6 | 12 | 7 | 9 | 9 | 10 | 5 | 7 |
| `-f`, with proof | 7 | 9 | 3 | 3 | 3 | 6 | 2 | 3 | 3 | 8 | 5 | 7 | 5 | 5 | 3 | 4 |
| without proof | 11 | 10 | 9 | 5 | 7 | 6 | 4 | 6 | 6 | 11 | 7 | 9 | 7 | 8 | 5 | 7 |

The other entrants do not log proofs. baguette's score summed over the sixteen editions is 4 043 with proof, 5 799 with proof under `-f`, 4 428 without proof.

The series before this one, D-0185 (release `7c880bce`, order encoding by default, 16 GB proof cap), verified 323 answers with proof in the default arm and 362 under `-f`, and completed 380 without proof.

Two caveats.

- This series ran the binary `f244c35a`, which has the bits encoding as its default (D-0201) and no
  proof cap, but predates the speed and coverage work merged since (D-0206, D-0208, D-0209, D-0212
  to D-0217 and D-0220). A series on a later binary will move these numbers, and the next one is
  due after the next merge that changes the encoding or the search.
- Free search is stronger in aggregate but not on every model. It wins on 670 instances and loses
  on 327 (578 ties), so the default stays the fixed search (D-0185 §5, D-0203).

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
