# Invariants

Properties that must hold after every change. If you break one, the bug is usually not
where the symptom appears — these are the things worth asserting and testing directly.

Assertions guarded by `BAGUETTE_DEBUG=1` should check as many of these as is affordable.

---

## Domains

- **I-D1** `lo <= hi` for every unfixed variable; a domain with `lo > hi` is failure and
  must have been reported as such, never stored.
- **I-D2** `lo` and `hi` are themselves in the domain — holes are never at the bounds.
  After removing a value equal to a bound, the bound must be tightened past it.
- **I-D3** A domain only ever shrinks within a decision level.

## Trail

- **I-T1** `backtrack_to l` restores every domain to exactly its state when level `l` was
  opened. Testable directly: snapshot, descend, backtrack, compare.
- **I-T2** Trail entries are strictly ordered by level; the level marks are monotone.
- **I-T3** Every trail entry has an explanation index that resolves. No orphan reasons.

## Propagation

- **I-P1** Soundness: a propagator removes only values that cannot extend to a solution of
  *its own constraint* under the current domains. Tested by brute force on small domains —
  see `test/unit/test_prop.ml`, and add every new propagator to it.
- **I-P2** Fixpoint: when `engine.propagate` returns without failure, running any
  propagator again changes nothing.
- **I-P3** Checking: with all variables fixed, a propagator reports failure iff the
  assignment violates its constraint.
- **I-P4** Every change carries an explanation. Enforced by the type — the function that
  writes a domain takes an `Explanation.t`, not an optional one. Do not add a `?reason`
  optional argument to work around this.

## Proof

- **I-X1** Every emitted rule is accepted by VeriPB. Non-negotiable; it is the product.
- **I-X2** Constraint ids are deleted exactly once. Checked at `conclusion` time under
  `BAGUETTE_PROOF_AUDIT=1`: the live set must be empty.
- **I-X3** Proof state mirrors solver state: a reason that has been deleted from the proof
  is not referenced by any live trail entry.
- **I-X4** The proof is append-only and never rewound. Backtracking in the solver becomes
  *deletion* rules in the proof, not truncation of the file.
- **I-X5** The `.opb` is written before any `.pbp` rule references it, and its constraint
  count matches the `f` line.

## Search

- **I-S1** Every solution printed satisfies every constraint — re-checked independently by
  `Model.check_assignment`, not by trusting the propagators.
- **I-S2** The search is complete: `=====UNSATISFIABLE=====` is only printed after the
  space is exhausted, and the proof must independently establish it.
- **I-S3** Decision level on return from search equals the level on entry.

## The meta-invariant

**I-M1** A failing test is information. The expected outputs in `test/expected/` and the
model files in `test/models/` are ground truth; they are changed only when the *spec*
changes, and that change goes through `docs/DECISIONS.md`.
