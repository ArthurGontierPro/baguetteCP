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
| End-to-end verification | under `--e2e`, the proof can also be checked against the `.opb` produced by `cake_pb_cp`, CakeML's verified encoder, so the encoding of the model is no longer trusted. At the last recorded run (D-0201), 197 of the 207 test models of that day verified this way and 10 were skipped (`make e2e`). The suite has 264 models since |
| Integer encoding | order encoding, or a binary (bits) encoding for wide domains. Bits is the default (`--bits-above 0`), `--bits-above none` gives the order encoding everywhere |
| Linear and arithmetic | `int_lin_le`, `int_lin_eq`, `int_lin_ne` and their reified forms, `int_le`, `int_lt`, `int_eq`, `int_ne` and their reified forms, `int_times`, `int_div`, `int_mod`, `int_abs`, `int_min`, `int_max` |
| Booleans | `bool_clause`, `array_bool_and`, `array_bool_or`, `bool_eq`, `bool_not`, `bool2int`, and the rest of the Boolean family through `mznlib` |
| Global constraints, native | `all_different_int` (domain consistent: Hall intervals on the bounds, then a matching over the values), `global_cardinality` (open, closed, low/up), `array_int_element`, `array_int_maximum`/`minimum`, `cumulative` and `disjunctive` (time-table), `regular` and `table` (domain consistent), `inverse`, `member`, `circuit` (with Chuffed's no-subtour rule) |
| Global constraints, through `mznlib` | `bin_packing`, `bin_packing_capa` and `bin_packing_load` (one linear row per bin), `diffn` and `diffn_nonstrict` (pairwise rows plus two `cumulative` relaxations). The capacity rows of the two relaxations are rows of the model, so the proof uses them without deriving them (D-0213). `nvalue`, the reified `all_equal`, `alldifferent_except` and `all_different(xs, S)` (D-0233), `lex_less` and `lex_lesseq` over integers and Booleans, hence `lex_greater`, `lex_chain_*` and `lex2` (D-0239) |
| Learning | 1UIP clause learning, the clause minimised over the order ladder (MiniSat's removal of root-level and re-derivable literals exists behind `BAGUETTE_MINIMISE` and is off by default, D-0241), and pseudo-Boolean conflict analysis (linear combination plus division or rounding), with a swappable retention policy for the learned database |
| Explanations | each pruning carries a declarative reason (an `Explanation` value), turned into `pol` or `rup` steps only when the proof needs them. Reasons are hash-consed so shared sub-proofs are written once |
| Search | free search by default since D-0261 (the activity order alternating with the model's annotation at each Luby restart, phase saving). The fixed search, the annotation alone (first-fail, smallest value when there is none) with no restarts, with `--fixed-search`. A conflict-driven search, where the learned clause decides the backjump, is available with `--cdcl` (or `BAGUETTE_CDCL=1`) and off by default (D-0219) |
| Without proof | `--no-proof` runs the same search without writing a proof, as a measurement tool. Its answers are unverified |
| Limits | `--time-limit`, `--max-heap-mb` (a clean refusal before memory runs out), caps on encoding size |
| Symmetries | `tools/symmetry/` finds model symmetries with dejavu, outside the solver (`make sym`) |

Floats, set variables and multi-objective optimisation are out of scope (`docs/SPEC.md` §1).

## Performance on the MiniZinc Challenge

All sixteen editions of the MiniZinc Challenge (2011 to 2026, 1 600 instances, 1 575 flattened), run with the Challenge's own settings: 1 200 s per instance, 16 GiB of memory, one thread, on an AMD EPYC 7643. An answer with a proof counts only when VeriPB verifies the proof. Measured on 2026-11-26/27 (`docs/DECISIONS.md` D-0227, release binary `fa2d4ee4`, commit `73b4cab`).

| Outcome per instance | Default search, with proof | Free search `-f`, with proof | Default search, `--no-proof` | Free search `-f`, `--no-proof` |
|---|---|---|---|---|
| Optimal or UNSAT, proof verified | 311 | **356** | 352 (unverified) | 419 (unverified) |
| Satisfiable, proof verified | 79 | **98** | 92 (unverified) | 111 (unverified) |
| Complete answer, VeriPB hit its time limit (3 600 s) | 25 | 35 | not applicable | not applicable |
| Solution found, not proved optimal, proof verified | 45 | 25 | not applicable | not applicable |
| Solution found, not proved optimal, proof not verified | 739 | 800 | 783 | 809 |
| Timeout at 1 200 s, no solution | 311 | 206 | 304 | 195 |
| Refused, memory budget reached | 65 | 55 | 44 | 41 |
| Crash | 0 | 0 | 0 | 0 |
| **Proofs rejected by VeriPB** | **0** | **0** | not applicable | not applicable |
| Optimisation runs that printed an objective value (optimal ones included) | 1 101 | 1 192 | 1 121 | 1 213 |

The first rows down to the rejected proofs add up to the 1 575 instances, checked when this table was written. A check that ran out of time or memory is the checker's limit, not a rejected proof, so it is counted apart.

What proof logging costs, over the instances both runs complete, comparing the run without proof to the run with proof:

| | median ratio (no proof / proof) |
|---|---|
| wall time | 0.48 |
| peak memory | 0.89 |
| nodes per second | 1.57 |

Without proof, 21 instances that hit the memory budget or a crash with proof become ordinary attempts, and 2 of them end with a complete answer.

The 844 verified proofs (all proof arms) have a median size of 233 MB, the largest is 23.6 GB and together they were 913.5 GB. They are deleted once checked, their sizes stay in the tables.

Rank in the fixed-search category of each edition, scored against that year's official entrants by `tools/compare/challenge_rank.py` (the free-search arm is scored in this category too, so the rows compare):

| Edition | 2026 | 2025 | 2024 | 2023 | 2022 | 2021 | 2020 | 2019 | 2018 | 2017 | 2016 | 2015 | 2014 | 2013 | 2012 | 2011 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| entrants | 13 | 10 | 9 | 7 | 7 | 7 | 6 | 8 | 8 | 12 | 11 | 9 | 11 | 11 | 10 | 8 |
| with proof | 11 | 10 | 9 | 5 | 7 | 6 | 4 | 6 | 6 | 11 | 7 | 9 | 8 | 7 | 5 | 7 |
| `-f`, with proof | 6 | 5 | 3 | 3 | 3 | 3 | 2 | 3 | 3 | 8 | 3 | 7 | 4 | 4 | 3 | 4 |
| without proof | 10 | 9 | 7 | 4 | 7 | 3 | 2 | 3 | 6 | 9 | 7 | 7 | 7 | 6 | 5 | 7 |
| `-f`, without proof | 5 | 4 | 3 | 3 | 3 | 3 | 2 | 3 | 3 | 7 | 3 | 6 | 3 | 4 | 3 | 4 |

The other entrants do not log proofs. baguette's score summed over the sixteen editions is 4 442 with proof, 6 277 with proof under `-f`, 4 922 without proof, 6 803 without proof.

The series before this one, D-0203 (release `f244c35a`, the same settings and instances), verified 376 answers with proof in the default arm and 441 under `-f`, and completed 426 without proof.

How to read these numbers.

- This series ran the release binary `fa2d4ee4`, built from main `6c9cf97`. It has the bits encoding as its default
  (D-0201), no proof cap, the native `table`, `circuit`, `diffn` and `bin_packing` (D-0206, D-0213, D-0217, D-0220),
  the speed and memory work of D-0208, D-0209, D-0212 to D-0216 and D-0222, and the interrupted-run proofs of D-0225.
  The proofs of runs stopped by the time limit were not checked, as in the series before.
- Against the series before (D-0203, binary `f244c35a`, the same settings and the same flattened instances), the verified answers
  with proof rise from 376 to 390 in the default arm and from 441 to 454 under `-f`, and the complete answers without proof from 426 to 444. The
  refusals fall from 164 to 65, from 138 to 55 and from 157 to 44. The summed scores rise from 4 043 to 4 442 (with proof), from 5 799 to
  6 277 (`-f`) and from 4 428 to 4 922 (without proof). The `-f` arm without proof, which D-0203 did not run, reaches 530 complete answers and 6 803 points, against 509 and 6 288 for the binary of D-0203 (D-0229).
  The median wall time of the instances solved both times is 0.95, so the gain is in memory and coverage.
  The `table` instances lose 37 of their 48 refusals (D-0227).
- The editions 2011 to 2014 had a limit of 900 s and baguette ran them with 1 200 s, so their ranks and
  scores favour baguette. A fair comparison on these four editions needs a run at 900 s.
- The solver has 16 GiB of address space, and it refuses an instance when its own heap reaches 8 GiB.
  With 64 GiB and a heap of 32 GiB the binary of D-0203 refused 60 instances instead of 164 with proof,
  but verified 304 optimal or UNSAT answers instead of 302 (D-0210, in `bench/series/HISTORY.md`).
- Free search is stronger in aggregate but not on every model. It wins on 715 instances and loses
  on 349 (511 ties). Since D-0261 (M19-config-T1, decided by D-0259 on this series) the free search is the
  default and the fixed search is `--fixed-search`. The "Default search" columns above are the fixed search,
  which was the default when the series ran. The `-f` rows above are there to compare the arms against the same opponents. They
  are not legal entries, because the fixed category requires the model's annotation to be followed.
  The ranks of `-f` in its own category are below.
- Against the other solvers that log proofs, GCS verified 141 answers in the same editions and settings and scored 2 792 (D-0211), against 390 and 4 442 for the default arm here. Chuffed, which logs nothing, scored 8 466.
- A node is still expensive. Before D-0208, a proved node cost from 66 to 592 times the instructions
  of a Gecode node on four problems where the two trees agree to within 2 % (D-0207).
- The scoring script reproduces the organisers' pairwise scores exactly for 2013 to 2026, but not for
  2012 (816 of 81 200 differ) and 2011 (137 of 60 000), so the ranks and the part of the summed
  scores from these two editions are approximate, in every series.

Rank of `-f` with proof in the free-search category, against that year's official free-search
entrants, from the same runs (`rank_B_<year>.txt` of the series). The entrants include baguette.

| Edition | 2026 | 2025 | 2024 | 2023 | 2022 | 2021 | 2020 | 2019 | 2018 | 2017 | 2016 | 2015 | 2014 | 2013 | 2012 | 2011 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| entrants | 27 | 21 | 22 | 18 | 19 | 17 | 17 | 14 | 15 | 22 | 23 | 19 | 17 | 18 | 17 | 14 |
| `-f`, with proof | 16 | 11 | 9 | 5 | 15 | 11 | 8 | 5 | 8 | 12 | 14 | 12 | 7 | 6 | 4 | 6 |
| the series before (D-0203) | 18 | 16 | 9 | 7 | 15 | 13 | 8 | 6 | 8 | 15 | 15 | 15 | 9 | 8 | 4 | 6 |

`bench/series/HISTORY.md` has one row per series.

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
baguette model.fzn --fixed-search           # the fixed search: the model's annotation, no restarts
baguette model.fzn --no-proof               # solve without a proof (the answer is unverified)
```

Every run writes its proof and keeps it. Without `--proof` the two files are named after the
model and go in the current directory, replacing those of an earlier run of the same model.

`baguette --help` lists every option.

The exit status is 0 when the run solved the model (SAT or UNSAT) or was stopped by
`--time-limit`, 2 for a usage error or a malformed model, 3 for a model outside the supported
subset, 4 for an internal invariant failure, 5 when a resource budget (`--max-heap-mb`, the
encoding caps) was exhausted before any solution was printed, and 6 when a file could not be
written (a missing directory or a full disk), in which case the proof is incomplete (D-0248).

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
thread and draws no random numbers, so `-p` and `-r` are accepted and change nothing. `-f`
changes nothing either, because the free search is already the default. MiniZinc runs without
`-f` still get the free search, so a run that must follow the model's annotation (the fixed
category of the MiniZinc Challenge) passes `--fixed-search`:

```sh
minizinc --solver baguette --fixed-search model.mzn data.dzn
```

### Search

By default (since D-0261) baguette runs the free search, as Chuffed does under `-f`. The search
alternates between the model's annotation and an activity order at each Luby restart, and it
keeps the last value of each variable (phase saving). It is the same as `--search alternate
--restarts luby --phase-saving`, and `-f` names it too.

With `--fixed-search` baguette follows the model's search annotation alone. A model without
one is searched first-fail with the smallest value first. There are no restarts. This is the
fixed search of the MiniZinc Challenge, and it was the default until D-0261.

On either search, `--search`, `--restarts` and `--phase-saving` replace their own part of it.
The free search is stronger in aggregate (the Challenge table above: 356 verified optima and
UNSAT answers against 311), but not on every model, because a good annotation can lose its proof of
optimality under it (31 instances of that series). Both
write a proof the checker verifies.

`--cdcl` replaces the default depth-first search with the CDCL loop of lazy clause
generation: after a conflict, the learned clause sends the search back to the level where it
asserts a literal and propagates there, and no branch nogood is written. It is off by default
(D-0219). With it, `--chrono T` goes back a single level whenever the jump would skip more
than T levels (chronological backtracking, D-0224).

`BAGUETTE_PROBE=root` probes at the root before the first decision: each bound literal of a
small domain is tried on its own, and one that fails is asserted negated at level 0, with
the failed node's nogood as its proof (failed-literal probing, D-0250). It is off by default.

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
| `docs/REFERENCES.md` | one line per decision, task and invariant the code cites |
| `bench/challenge/README.md` | how the Challenge runs are made and where they are kept |
| `bench/series/HISTORY.md` | the results of every Challenge series |
| `scripts/README.md` | the operating manual for the compute node (runs, gates, lanes) |

Contributors, Claude sessions included, start with `CLAUDE.md`.
