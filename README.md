# baguette

A constraint programming solver with VeriPB proof logging and higher-order explanations.

Reads FlatZinc, solves, and emits a pseudo-Boolean proof that an independent checker
verifies. The proof is a primary output, not a debugging option: every pruning the solver
makes must be able to justify itself.

Written in OCaml 5.

## Status

Early scaffold. See `docs/ROADMAP.md` — M0 (it builds) is in progress.

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
