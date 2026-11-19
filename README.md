# baguette

A constraint programming solver with VeriPB proof logging and higher-order explanations.

Reads FlatZinc, solves, and emits a pseudo-Boolean proof that an independent checker
verifies. The proof is a primary output, not a debugging option: every pruning the solver
makes must be able to justify itself.

Written in OCaml 5.

## Status

Solves the FlatZinc subset of `docs/SPEC.md` §2.1, directly or through its MiniZinc library
(`mznlib/`), and writes a VeriPB 3.0 proof for every answer. `docs/ROADMAP.md` says what is
done and what comes next.

## Getting started

```sh
scripts/bootstrap.sh     # once: installs opam, OCaml 5, dune, dependencies
make build
make test
```

## Usage

```sh
baguette model.fzn                          # solve
baguette model.fzn --proof out              # solve, write out.opb and out.pbp
veripb out.opb out.pbp                      # verify
```

`baguette --help` lists every option.

### From MiniZinc

`tools/baguette.msc` registers baguette as a MiniZinc solver, with its own library for the
global constraints it handles natively.

```sh
export MZN_SOLVER_PATH=$PWD/tools
minizinc --solver baguette model.mzn data.dzn                  # solve
minizinc --solver baguette --proof out model.mzn data.dzn      # and write out.opb, out.pbp
minizinc --solver baguette -t 300000 -s model.mzn data.dzn     # 300 s limit, statistics
```

baguette accepts the MiniZinc standard flags `-i -f -n -p -r -s -t -v`. It runs on one
thread and draws no random numbers, so `-p` and `-r` are accepted and change nothing.

### Search

By default baguette follows the model's search annotation. A model without one is searched
first-fail with the smallest value first. There are no restarts. This is the fixed search of
the MiniZinc Challenge.

You can also try free search with `-f`, as with Chuffed. The search then alternates between
the annotation and an activity order at each Luby restart, and it keeps the last value of
each variable (phase saving). It is the same as `--search alternate --restarts luby
--phase-saving`, and each of those options can also be given on its own. Free search often
helps when the annotation is a poor order or when there is none. It can also be much slower,
so neither search wins on every model (`docs/DECISIONS.md` D-0137 §10 compares them). A run
under `-f` writes a proof the checker verifies, as the default search does.

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

Contributors — including Claude sessions — start with `CLAUDE.md`.
