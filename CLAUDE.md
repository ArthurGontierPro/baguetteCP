# baguette

A constraint programming solver with VeriPB proof logging and higher-order explanations.

- **Input**: FlatZinc (a subset — see `docs/SPEC.md`)
- **Output**: solutions + a VeriPB 2.0 proof that the checker accepts
- **Language**: OCaml 5, built with dune

---

## Read before you start

This project is worked on by **several Claude sessions at once, in this same checkout,
on the same branch**. The protocol below is not optional; ignoring it means two sessions
overwrite each other's work.

### The protocol

1. **Read `WORKLOG.md` first, every session.** It lists who is working on what right now.
2. **Claim before you edit.** Append your task to the `## Active claims` table in
   `WORKLOG.md` with a task ID from `docs/ROADMAP.md`, the files you intend to touch,
   and a session tag. Commit that claim immediately, before writing any code.
3. **Do not touch files claimed by another session.** If you need a change in a claimed
   file, write the request under `## Cross-session requests` in `WORKLOG.md` and work on
   something else. Do not wait.
4. **Release when done.** Move your row to `## Completed`, and write two or three lines
   under `## Handoff notes` saying what changed and what the next session should know.
5. **Commit in small pieces.** A session that runs for an hour without committing is a
   session whose work another session will clobber.

`/claim`, `/handoff` and `/check` automate steps 2, 4 and the pre-commit gate.

### dune's build directory is shared, and it is locked

`dune` takes a **global lock on `_build/`**. Two sessions running `dune build` in this
checkout at the same time will corrupt `_build/.lock` and both will fail with
*"Unexpected contents of build directory global lock file"*.

File-level claims do not protect you from this. Either build when no one else is, or
build into your own directory:

```sh
dune build --build-dir=/tmp/baguette-build-$$ lib/core/
```

If you find `_build/.lock` already corrupted, check whether another session is mid-build
before deleting it — deleting it under a running build breaks that build.

Scope your builds to your own directory (`dune build lib/core/`) rather than a bare
`dune build`, which will also try to compile whatever half-finished state the other
sessions have on disk and fail for reasons that are not yours.

### Files that are contention hotspots

Edits to these are frequent conflicts. Claim them explicitly and keep the edit short:

| File | Why |
|---|---|
| `lib/core/dune`, `lib/*/dune` | every new module adds a line |
| `docs/ROADMAP.md` | task status |
| `WORKLOG.md` | by design — append only, never rewrite others' rows |
| `lib/core/explanation.ml` | central ADT, every propagator depends on it |

Append-only discipline on `WORKLOG.md` and `docs/DECISIONS.md`: add at the bottom of the
relevant section, never reflow or reorder what is already there. That makes git's merge
of concurrent edits succeed instead of conflicting.

---

## Where things are

| Path | Contents |
|---|---|
| `docs/SPEC.md` | **normative**. What the solver must do. Changes here need a decision record. |
| `docs/ARCHITECTURE.md` | module map, data structures, how a propagation actually flows |
| `docs/PROOF-FORMAT.md` | the VeriPB contract: encoding, rule vocabulary, per-propagator justification |
| `docs/INVARIANTS.md` | properties every change must preserve. Read before touching core. |
| `docs/ROADMAP.md` | milestones and task IDs (`M1-T3` etc.) — the source of claimable work |
| `docs/DECISIONS.md` | append-only decision log. Check it before re-arguing a settled design point. |
| `docs/GLOSSARY.md` | CP and proof-logging vocabulary as *this project* uses it |
| `lib/core/` | domains, trail, explanations, propagators, search |
| `lib/proof/` | OPB emission and VeriPB proof writing |
| `lib/flatzinc/` | FlatZinc lexer, parser, model builder |
| `bin/` | the `baguette` CLI |
| `test/` | unit tests, `.fzn` models, expected outputs |

## Commands

```sh
make build          # dune build
make test           # dune runtest  (unit + model + proof-checking tests)
make check          # fmt + build + test — the gate before any commit
make proof FZN=test/models/foo.fzn   # solve and verify one model's proof
```

## Rules for this codebase

- **Every propagation that prunes must be able to justify itself.** A propagator that
  narrows a domain without producing an `Explanation` is a bug, not an optimisation.
  There is no "add proof logging later" mode.
- **A test that does not check the proof is half a test.** Any test that solves a model
  must also run `veripb` over the emitted proof. See `scripts/verify_proof.sh`.
- **Never weaken a test to make it pass.** If a model test starts failing, the propagator
  or the proof is wrong. Say so and stop; do not adjust the expected output.
- **`docs/SPEC.md` is the authority.** If the code and the spec disagree, that is a bug
  report against one of them — raise it, do not silently pick a side.
- Keep explanations *lazy where they are expensive*: see `docs/ARCHITECTURE.md`,
  "Deferred explanations".

## Git

Several sessions share this checkout, so staging discipline matters more than usual.

- **Never `git add -A`, `git add .`, or `commit -a`.** Another session's half-finished
  work is almost certainly sitting in the tree next to yours. Run `git status`, look at
  what is there, and stage explicit paths.
- Commit in small pieces. A session that works for an hour without committing is a
  session whose work someone else will clobber.
- Prefix commits with the task ID: `M1-T7: int_lin_le propagator and its pol justification`.
- Claim commits are their own commit (`claim: M1-T7`), pushed before the work starts.

## Environment note

The OCaml toolchain is **not yet installed on this machine**. Run `scripts/bootstrap.sh`
once before the first build. `veripb` is already present at `~/.local/bin/veripb`
(proof format version 2.0).
