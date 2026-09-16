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

### If you are working in a worktree under `.claude/worktrees/`

`make` and a bare `dune build` **do not work from there**, and the error does not say why:

```
Error: Don't know about directory .claude/worktrees/<name> specified on the command line!
Error: No rule found for alias .claude/worktrees/<name>/default
```

The cause is that the worktree lives *inside* the main checkout, so dune walks up, finds
the outer `dune-project` first, and treats your worktree as a subdirectory of the outer
project rather than as a project of its own.

Pass `--root .` to pin the project root to the worktree. That also puts `_build` inside
the worktree, which is what you want anyway — it is then a private build directory, so
the shared `_build/.lock` above stops being your problem:

```sh
dune build   --root .
dune runtest --root .
```

Do **not** reach for a `--build-dir` outside the checkout instead. Two suites locate
`test/models/` and `test/expected/` relative to the cwd or the executable, and the
mutation harness needs `scripts/mutate_proof.sh`; from an out-of-tree build directory
they cannot find those. They say so rather than passing quietly, which is the behaviour
to preserve:

```
FAIL scripts/mutate_proof.sh was not found ... NOT ONE mutation lane ran. This is not a pass.
```

`BAGUETTE_ROOT=<checkout>` fixes the mutation harness but not the other two; `--root .`
fixes all three.

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
| `lib/core/` | domains, store/trail, explanations, propagators, search |
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

### The machine has 15 GB of RAM, shared by every session running at once

This is the constraint that has bitten this project hardest in practice. On 2026-09-16 a
`test_prop.exe` reached **14.9 GB RSS** and had to be killed by hand; later the same day
two more test binaries had to be killed at the ceiling. Each time it disrupted the user,
not just the session that caused it.

- **Run every suite under a cap.** `make`, `scripts/run_model_tests.sh` and
  `scripts/verify_proof.sh` now apply `ulimit -v 4000000` themselves. If you invoke a
  test binary or `dune runtest` directly, apply it yourself:

  ```sh
  (ulimit -v 4000000; timeout 900 dune runtest --root .)
  ```

- **A run that dies against the cap is a finding, not an obstacle.** Report it. Do not
  raise the cap to get past it. `MEM_CAP_KB` and `BAGUETTE_MEM_CAP_KB` exist for
  deliberate, explained exceptions and belong in `WORKLOG.md` when used.

- **No test may declare a wide domain.** This is almost always the cause. The order
  encoding is width-proportional (D-0028): `var 0..1000` is not a slightly larger test,
  it is a thousand ladder clauses and a proof that dwarfs the whole suite. Keep declared
  domains in the single or low double digits. If a property is only observable at width,
  `test/models/width_root_unsat.fzn` already exists for that at w=999 — it is deliberate,
  measured, and enough.

- **Report peak RSS** for your final run (`/usr/bin/time -v`, or `\time -f '%M'`).


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

The toolchain is installed and working:

- opam 2.5.2 at `~/.local/bin/opam`, switch `baguette` on OCaml 5.1.1
- **The checker of record is VeriPB 3.0.2** (the Rust build) at `~/.cargo/bin/veripb`,
  and the solver emits `pseudo-Boolean proof version 3.0` by default (D-0025).
  `~/.local/bin/veripb` is the **Python VeriPB 2.2.2** this project used until then; it
  is still on `PATH` and still used to check format-2.0 output, so *both* exist and they
  are different programs. Never assume which one you invoked — `scripts/checker.sh` is
  the single place that resolves it, and it documents the order. The two word their
  rejections differently and share no substring (see M1-T46), so never match on one
  wording alone.

Put `eval "$(opam env --switch=baguette)"` in your shell before building. On a fresh
machine, `scripts/bootstrap.sh` does the whole setup and is safe to re-run.
