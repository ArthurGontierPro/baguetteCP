---
description: Scaffold a new propagator with its justification and tests
argument-hint: <builtin name, e.g. int_lin_le>
---

Add a propagator for the FlatZinc builtin `$1`.

Before writing code, read:
- `docs/SPEC.md` section 3.2 for what a propagator must guarantee
- `docs/PROOF-FORMAT.md` section 4 for the justification table
- `lib/core/prop/linear.ml` as the reference shape, if it exists yet

Then produce all four of these — a propagator without the last two is not done:

1. **The module**, in `lib/core/prop/`, implementing `Propagator.S`. Its header comment
   must state its consistency level and the exact shape of the proof step it emits.
2. **The justification**: every pruning constructs an `Explanation.t`. Use `Deferred`
   where building the reason is more expensive than the pruning itself. Prefer a `Linear`
   or `Cut` reason (renders to `pol`) over `Clause` (renders to `rup`) — and if only
   `rup` is possible, say why in the header comment.
3. **Soundness test**: add `$1` to the brute-force check in
   `test/unit/test_propagator_soundness.ml` — enumerate assignments over small domains
   and confirm it removes only values no solution of its own constraint uses (I-P1).
4. **Model tests**: a satisfiable and an unsatisfiable `.fzn` in `test/models/` using
   `$1`, with expected outputs. The UNSAT one is the one that exercises the proof.

Finally update the justification table in `docs/PROOF-FORMAT.md` section 4, and run
`make check`.
