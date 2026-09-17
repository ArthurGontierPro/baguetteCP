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

- **I-X6** A `Deferred` explanation's thunk closes over a **snapshot** and never reads live
  store state. Forcing it later must render the derivation as of the moment the pruning
  was made, not as of now. This is what makes D-0018's lazy trace sound: the trace is
  written when a branch fails, by which time the store has moved on. `linear.ml`'s
  `snapshot_source` is the pattern to copy; `explain_cross_conflict` violated this until
  M1-T13 and was harmless only by accident, because search happened to force a conflict
  explanation immediately. Conflict analysis (M2-T3) will not.

- **I-X7** What `conclusion UNSAT` cites is a line the checker has itself established is a
  contradiction — either a `pol` chain closing at `0 >= k` (D-0013) or an explicitly
  derived empty clause (D-0022). A propagator's reason is never cited as a contradiction
  on the propagator's word. `Search.rests_on_a_clause` is where the two are told apart.

- **I-X8** No row is committed to the `.opb` whose arithmetic wrapped.
  `Encoding.add_int_lin_le` and `add_int_lin_ne` check, in overflow-checked arithmetic,
  that every integer they and `Opb` will derive from the row is representable, and
  **raise** rather than wrap or decline — D-0029: there is no "decline" available for an
  artefact that must exist. `lib/flatzinc/compile.ml`'s cap keeps this unreachable for any
  model the CLI accepts; the guard is what makes "Compile is the only door" a property of
  the code rather than of who happens to call it. It does **not** cover a hand-built
  `Opb.constr` passed to `add_constraint`, nor the pure `expand_*` forms, which stay
  unguarded **deliberately** so that `test_prop.ml` can go on demonstrating the D-0029
  defect on the expansion itself. Inspecting an expansion is not writing a file.

- **I-X9** An explanation justifies the bound as **recorded on the trail**, not the bound
  the propagator asked for. `Domain.set_lo`/`set_hi` settle past holes to re-establish
  I-D2, so a recorded bound can be strictly stronger than what the reason derives; the
  reasons of the holes the settle walked over are part of the justification and are cited
  with it. Violating this produced M1-T44: a correct UNSAT whose chain fell exactly one
  unit short. See D-0035.

  **Scope, narrowed 2026-09-16 (M1-T50).** This holds where an explanation is *emitted as
  a `pol`* at all. A bound resting on a **decision** is a deliberate exception: a decision
  has no constraint id and structurally cannot have one (D-0009), so `Snap_assume` weakens
  the term out of the row and derives something strictly weaker than the trail records.
  Such a bound is justified by its **trace line**, not by a `pol`. Harmless today because a
  `Combine` is emitted only at a root conflict, where no decision is in force — but
  D-0018 point 2's per-push `pol` path and M2-T3 both reach it. See D-0037.

- **I-P5** Every store mutator that can move a bound takes `~facts`, and every propagator
  that calls one passes the facts it actually read. A propagator that prunes through a
  factless mutator writes a D-0018 trace line with an empty reason — an unconditional
  claim — and on a satisfiable model such a line is not merely unprovable, it is **false**.
  This is the companion to I-P4: I-P4 makes every change carry an *explanation*, I-P5 makes
  every bound move carry the *facts* its trace line negates. `int_ne` violated this from
  M1-T9 until M1-T17 by pruning through `Store.remove`.

## Search

- **I-S1** Every solution printed satisfies every constraint — re-checked independently by
  `Model.check_assignment`, not by trusting the propagators.
- **I-S2** The search is complete: `=====UNSATISFIABLE=====` is only printed after the
  space is exhausted, and the proof must independently establish it.
- **I-S3** Decision level on return from search equals the level on entry.

- **I-S4** A trace line that cites a hole is supported only while that hole's own line is
  live, so **the cited line must outlive the citing line**. Since M1-T57 a settle line is
  RUP against the `.opb` *plus* earlier trace lines rather than standalone (D-0039,
  PROOF-FORMAT §4), which makes deletion order load-bearing where it previously was not.
  It holds today by the level discipline rather than by a check: a settle at level `l` can
  only cite holes punched at levels `<= l`, because a deeper hole does not exist yet when
  it runs; and `w l` retires levels `>= l`, so the cited line is never retired before the
  citing one. **Argued from the level discipline, not exhaustively measured** — and worth
  re-checking when M2-T3's learned clauses start citing lines across levels, which is
  exactly the case the argument above does not cover.

## The meta-invariant

**I-M1** A failing test is information. The expected outputs in `test/expected/` and the
model files in `test/models/` are ground truth; they are changed only when the *spec*
changes, and that change goes through `docs/DECISIONS.md`.
