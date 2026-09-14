---
description: Run the full pre-commit gate and report honestly
---

Run `make check` and report the result.

- Show the real output on failure. Do not summarise a failure as "minor".
- If a model test failed proof checking, say so explicitly and point at the `.opb` and
  `.pbp` in `test/out/`. Follow `docs/PROOF-FORMAT.md` section 6; `scripts/shrink.sh`
  narrows it to a propagator.
- If the run printed `SKIP` lines because `veripb` was not found, say so — that run did
  **not** check any proofs, and is not a green run.
- Never make a failing test pass by editing `test/expected/` (invariant I-M1).
