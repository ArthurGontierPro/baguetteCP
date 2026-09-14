# Tests

Three layers, all of which must pass before a commit (`make check`).

## 1. Unit tests — `test/unit/`

`dune runtest`. Direct checks of the invariants in `docs/INVARIANTS.md`: domains, the
trail, explanation memoisation, OPB rendering.

When you add a propagator, add it to the soundness check (I-P1): brute-force every
assignment over small domains and confirm the propagator removes only values that no
solution of its own constraint uses. This catches the bug class that otherwise shows up
as a rejected proof much later, with a far worse error message.

## 2. Model tests — `test/models/` + `test/expected/`

`scripts/run_model_tests.sh`. Each `.fzn` is solved and its stdout compared against the
matching `.out`. Expected outputs assume the default search (first-fail, `indomain_min`);
a model whose answer depends on search order should carry an explicit search annotation
rather than an expected output that encodes today's heuristics.

## 3. Proof checking — every model, every run

The same script then runs `veripb` over the emitted `.opb`/`.pbp`. **A model test that
passes its output comparison but fails proof checking is a failing test.** That is the
product: see `docs/SPEC.md` section 1.

`veripb` is at `~/.local/bin/veripb` on this machine. If it is missing the proof step is
skipped with a `SKIP` line rather than silently passing — check for those in the output
before believing a green run.

## Expected failures — `test/models/PENDING`

Until the engine lands, no model solves, so every model test would be red. A gate that is
red for five milestones is a gate everyone learns to ignore, so models that are not yet
expected to work are listed in `test/models/PENDING`, one basename and a reason per line.
They are reported as `xfail` on every run and do not turn the gate red.

Two properties keep that from rotting into a list of quietly broken things:

- Every run prints the pending count and says the file should be empty by M1-T11.
- If a model listed there starts **passing**, the runner reports `XPASS` and **fails**,
  telling you to delete the line. You cannot leave a working model marked as broken.

Delete a line the moment its model works. Adding a line is a decision about scope, not a
way to silence a failure: a model that used to pass and now does not is a regression, and
belongs in a bug report rather than in this file.

## Rules

- Expected outputs are ground truth. Changing one requires a spec change and a decision
  record (invariant I-M1). If a test starts failing, the solver is wrong until proven
  otherwise.
- Add a model for every new builtin, satisfiable *and* unsatisfiable. The UNSAT case is
  the one that exercises the proof.
- Keep models small enough that a rejected proof is readable by hand.
