# baguette

A constraint programming solver with VeriPB proof logging and higher-order explanations.

- **Input**: FlatZinc (a subset — see `docs/SPEC.md`)
- **Output**: solutions + a VeriPB 2.0 proof that the checker accepts
- **Language**: OCaml 5, built with dune

---

## Context budget — read this before you open a file

`docs/` is **340 KB ≈ 85k tokens**. `WORKLOG.md` alone is 68 KB ≈ 17k tokens. Reading
them "to be thorough" costs more than the work you were dispatched to do, and a session
that spends its context on reading has none left for the task. So the rule is:

**Never read a file over ~20 KB whole. Scope the read.**

| File | Size | How to read it |
|---|---|---|
| `WORKLOG.md` | 68 KB | **The `SessionStart` hook already printed `## Active claims` for you.** Do not re-read the file to get it. For other sections: `sed -n '/^## Cross-session requests/,/^## Completed/p' WORKLOG.md`, or `tail -60` for the latest handoff notes. |
| `docs/DECISIONS.md` | 126 KB | Never whole. `grep -n 'D-0028' docs/DECISIONS.md` then `sed -n '<start>,<end>p'`. To catch up: `grep -n '^## D-' docs/DECISIONS.md \| tail -20`. |
| `docs/ROADMAP.md` | 46 KB | Never whole. `grep -n -A8 'M1-T31' docs/ROADMAP.md` for your task's row. |
| `docs/PROOF-FORMAT.md` | 30 KB | By section, and the sections are stable: §1 checkers, §2 rules 2.0, §2a rules 3.0, §3 encoding (normative), §4 per-propagator justification, §5 backtracking/deletion, §6 debugging a rejected proof. `sed -n '352,402p'` is §4. |
| `docs/GCS-COMPARISON.md` | 29 KB | Background. Read only if the task is explicitly about the comparison. |
| `docs/SPEC.md` | 14 KB | Normative. Read the relevant section whole; §2.1 is the FlatZinc subset, §3.2 consistency levels, §3.3 explanations. |
| `docs/INVARIANTS.md` | 6 KB | Read whole before touching `lib/core/`. It is short on purpose. |
| `docs/ARCHITECTURE.md` | 7 KB | Read whole if you are changing structure. Its §1 module map is **stale** — use the map below. |
| `docs/GLOSSARY.md` | 4 KB | Read whole if the vocabulary is new to you. |

**Module headers are the cheapest documentation in this repo.** Every module in `lib/`
opens with a comment stating what it is, its consistency level, and which spec section
governs it. `head -40 lib/core/prop/linear.ml` answers most questions about a propagator
for ~400 tokens. Do that before grepping, and grep before reading whole files.

**Command output is context too.** `dune runtest`, `make bench` and model runs emit far
more than you need:

```sh
(ulimit -v 4000000; timeout 900 make test) > /tmp/test-$$.log 2>&1; tail -40 /tmp/test-$$.log
grep -c FAIL /tmp/test-$$.log
```

Never pipe a full test or benchmark run into your context and then read it. Redirect,
then `grep`/`tail`. Report the peak RSS line and the failures, not the transcript.

---

## Read before you start

This project is worked on by **several Claude sessions at once, in this same checkout,
on the same branch**. The protocol below is not optional; ignoring it means two sessions
overwrite each other's work.

### The protocol

1. **Know what is claimed.** The `SessionStart` hook prints `## Active claims` from
   `WORKLOG.md` at the top of your session. That is your copy — work from it. Re-read
   from disk only if you have reason to think it changed under you (a long session, or a
   `git pull`), and then re-read *that section*, not the file.
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

Dependency direction is strictly `flatzinc -> core -> proof`. `core` must not depend on
`flatzinc`. `proof` must not reach back into `core`'s mutable state — it receives values.

This map is current. Trust it over `docs/ARCHITECTURE.md` §1, which still lists
propagators that do not exist (`alldiff`, `element`, `clause`) and omits several that do.

```
bin/main.ml                 CLI: parse args, wire everything, print results

lib/flatzinc/   Baguette_flatzinc
  pos.ml error.ml           source positions; the single front-end error type
  ast.ml                    FlatZinc syntax tree, restricted to SPEC 2.1
  lexer.ml parser.ml        hand-written scanner + recursive descent (D-0006)
  model.ml                  the front end's output: vars, domains, constraints
  builder.ml                ast -> Model.t, and the normative rules of SPEC 2.1
  compile.ml                Model.t -> store + PB encoding + propagator instances;
                            this is the flatzinc -> core edge
  output.ml                 solution printing in FlatZinc output format

lib/core/       Baguette_core
  var.ml                    variable identity (abstract int)
  domain.ml                 bounds pair + lazily allocated hole set (ARCH §2)
  store.ml                  backtrackable store: domains + undo trail (ARCH §3)
  explanation.ml    *****   THE Explanation ADT. Read SPEC §3.3 + ARCH §4 first.
                            D-0003 is OPEN and will reshape it. No new constructor
                            without a decision record.
  justify.ml                Explanation.t -> VeriPB rules -> constraint id. Lives in
                            core, not proof, because proof cannot see Explanation.
  trace.ml                  records what a branch learned so its nogood is plain RUP
                            (D-0018, M1-T13)
  propagator.ml             the PROPAGATOR module type (51 lines — read it whole)
  engine.ml                 propagate-to-fixpoint loop and the queue (ARCH §5)
  search.ml                 DFS, branching, backtracking, every step proof-logged
  checked.ml                checked integer arithmetic + the overflow cap (M1-T23)
  interval.ml               interval arithmetic: mul, square, div of bounds (M4-T4a)
  debug.ml                  BAGUETTE_DEBUG-gated invariant checks
  prop/                     one module per constraint family:
    linear.ml               int_lin_le. THE REFERENCE PROPAGATOR — copy this shape.
    lin_eq.ml               int_lin_eq (two model rows, see D-0011)
    ne.ml                   int_lin_ne and int_ne (VALUE consistency)
    int_le.ml int_lt.ml     degenerate linear constraints, delegate to Linear
    int_eq.ml               delegates to Lin_eq
    bool2int.ml             bool <-> int channelling
    bool_clause.ml          clauses, and the array_bool_or/and/eq/not family
    order_reason.ml         bound-fact chains in the order encoding (D-0010)

lib/proof/      Baguette_proof
  lit.ml                    encoding literals; naming is NORMATIVE (PROOF-FORMAT §3)
  encoding.ml               which variable has which encoding; channelling
  opb.ml                    writes the .opb model file
  writer.ml                 writes the .pbp proof; owns the constraint-id counter
                            (I-X2: an id you receive is an id you must delete)
  checker.ml                resolves which veripb to use; mirrors scripts/checker.sh

test/unit/                  test_core test_domain test_engine test_prop test_proof
                            test_justify test_trace test_flatzinc test_compile
                            test_endtoend test_matrix test_mutation test_output
                            test_random test_interval
test/models/                31 .fzn models   test/expected/  their expected outputs
scripts/                    checker.sh verify_proof.sh run_model_tests.sh shrink.sh
                            mutate_proof.sh check_test_widths.sh bootstrap.sh
```

## Commands

```sh
make build          # dune build
make test           # unit + model + proof-checking tests
make check          # fmt + build + lint + test — the gate before any commit
make proof FZN=test/models/foo.fzn   # solve and verify one model's proof
make bench ARGS="..."                # measurement only, never a commit gate
```

---

## Dispatching subagents

If you are an orchestrator session, the sub-sessions you spawn are the largest single
line in this project's token bill, because each one starts with no context and
rediscovers the codebase from scratch. Four rules:

1. **Give the agent its coordinates, not a search.** Name the files, the module headers
   to read, and the doc sections by line range. "Fix the `pol` step in
   `lib/core/prop/linear.ml:317,352`, see `justify.ml:288`, PROOF-FORMAT §4" costs a
   fraction of "investigate the linear propagator's justification".
2. **Match the effort to the task.** Design, proof-soundness and conflict-analysis work
   earn `high`/`xhigh`. Mechanical work — adding a test model, widening a comment to
   name both checker wordings, formatting, running the gate and reporting — does not.
   Dispatch those at `low` or `medium`.
3. **Match the model tier to the task.** Reading-and-reporting work (locate every site
   that matches a string; summarise what a suite failed on) does not need the top tier.
   Reserve it for the work where the explanation type or the proof is at stake.
4. **Bound the report.** Say what you want back and what you do not: *"Return the file
   and line of each site, one line of context each, and the final `make check` verdict.
   Do not paste source or test output."* An unbounded agent report lands in your context
   and is re-read on every subsequent turn of your session.

Use `Explore`-style read-only agents for "where is X" questions and reserve
general-purpose agents for work that actually edits. Continue an existing agent rather
than spawning a fresh one for a follow-up in the same area — the fresh one pays the
discovery cost again.

---

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

### Proof discipline

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
