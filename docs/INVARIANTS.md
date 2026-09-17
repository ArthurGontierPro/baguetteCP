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
  written when a branch fails, by which time the store has moved on.

  **The two halves now have different standing (M2-T8).** On the *reason* half it is
  discharged **by the type**: `Reason.t` is a list of frozen facts and `Reason.lits` takes
  no store, so a reason cannot read live state even by mistake. On the *justification*
  half it is still discipline, not type — a thunk can still close over the wrong thing,
  and M2-T8 measured what that costs: moving a per-term snapshot inside the justification
  thunk kills four binaries with a **stack overflow** rather than a wrong answer, because
  at force time the pruning's own entry supports the bound and the derivation cites
  itself. A crash is not a check; two tests now catch it and they are the only ones that do.

  **`explain_cross_conflict` is settled, and the sentence that used to stand here was
  wrong.** I wrote on 2026-09-17 that it "violated I-X6 until M1-T13 and still does", and
  that the blind spot was open. It does not: M1-T13 hoisted the `lo_rests_on`/`hi_rests_on`
  lookup out of the thunk and it never went back, so the thunk closed over nothing live.
  What *was* true is narrower and was worth fixing — `store` remained in scope one line
  above a thunk that must not read it, so the discipline was one careless edit from being
  undone. It is structural now: the lookup is a separate `opposite_rests_on` at the push
  site and the function takes `~opposite` and **no store at all**, so re-breaking it
  requires changing a signature. Same move `Reason.lits` makes on the reason half.

  Two facts to keep attached, because together they explain why nothing could see the
  original break. **The cross-row path is unreachable from any `.fzn`**:
  `compile.ml`'s `normalise_terms` merges duplicate coefficients before both the `.opb`
  row and `Linear.make`, so `int_lin_le([2,-1],[d,d],-4)` arrives as `d <= -4` and is
  solved with zero `pol` and zero `rup` lines (measured). The path is reachable only by
  calling `Linear.make` directly, as `test_matrix.ml` does — which is why no test *model*
  can cover it, and why one was deliberately not added. And **search forces a conflict
  explanation immediately**, so even on that route the store has not moved. One test now
  fires on a wrong *answer* rather than a crash (`test_prop.ml`), and it is the only thing
  in the suite that does.

  So the remaining I-X6 exposure is the **general** one, not this function: any future
  thunk can still close over the store, and on the justification half nothing but
  discipline stops it. That is what M2-T3 should be careful of.

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

- **I-P5** *(merged into I-P4 by M2-T8 — kept for its history, which is the reason the
  merge was worth doing.)* Every bound move carries the **facts** its trace line negates,
  as I-P4 makes every change carry an *explanation*. A propagator that pruned through a
  factless mutator wrote a D-0018 trace line with an empty reason — an unconditional claim
  — and on a satisfiable model such a line is not merely unprovable, it is **false**.
  `int_ne` violated this from M1-T9 until M1-T17 by pruning through `Store.remove`, and
  M1-T57 was the same shape again in a different guise.

  Since M2-T8 there is **one** obligation, not two that can drift apart: every mutator
  takes a single `Reason.justified`, which pairs the reason with the justification, and
  `set_lo_with_facts` / `set_hi_with_facts` / `remove_with_facts` / `no_facts` are gone.
  A caller with genuinely no facts writes `Reason.none` and is **seen** doing it, which is
  the property the separate `~facts` argument could never enforce.

## Search

- **I-S1** Every solution printed satisfies every constraint — re-checked independently by
  `Model.check_assignment`, not by trusting the propagators.
- **I-S2** The search is complete: `=====UNSATISFIABLE=====` is only printed after the
  space is exhausted, and the proof must independently establish it.
- **I-S3** Decision level on return from search equals the level on entry.

- **I-T4** Every trail entry names the propagator instance that made it, in `entry.prop`,
  or `no_prop` where no propagator did (a decision, or a root-level declaration). The
  naming instance must also **watch** the variable the entry changed. `Store.apply` stamps
  the field from a slot the engine sets around each `run`, so no mutator takes an id and a
  propagator has nothing to get wrong; `Engine.check_attribution` reads it back and raises
  `Mis_attributed` on a mismatch. **It is on always, not under `BAGUETTE_DEBUG`** — M2-T3
  resolves an entry's reason constraint through this field, so a wrong id is a wrong
  learned clause, and an id that is threaded but never read is decoration. The cost is one
  hashtable lookup per new entry, the same one `watchers_of_new_entries` already makes.

  The "watches the variable it changed" half is the part that catches a *plausible* wrong
  id rather than an obviously wrong one, and it is checked rather than sealed: the mutators
  make a wrong id unreachable, but `Store.with_running` is public and must stay so, so that
  route is guarded by the check. Two tests perform the break — `Steals_credit` re-enters
  `with_running` with another instance's id, and `Under_declared` has `vars` under-report
  so the propagator prunes a variable it never declared. Measured: stamping
  `current_prop + 1` reddens 121 unit checks, kills 7 binaries and fails 30 of 34 models;
  dropping the bracket reddens 123 and fails all 34.

- **I-X10** Every trace line a propagator emits is RUP against the `.opb` plus the lines
  already on the page, and the reason is a property of **this propagator set**, not of the
  order encoding: every M1 pruning follows from a **single model constraint**, whose rows
  unit-propagate the claim once the facts on the line's own tail are assumed. Holds by
  enumeration over the whole set — `Linear`, `Lin_eq`, `Int_le`, `Int_lt`, `Int_eq` (one
  `int_lin_le` row each), `Ne` (`int_lin_ne`'s two big-M rows, the `_neN` selector filled
  in by the checker's own unit propagation), `Bool2int` and `Bool_clause` (channelling and
  clause rows). `Ne` is also the **only** thing that punches a hole: it is the sole caller
  of `Store.remove_with_facts` in `lib/`; `Store.remove`/`Store.fix` have no `lib` callers
  at all; `Domain.settle` only walks bounds past holes that already exist; and
  `Domain.of_list` is unreachable because `compile.ml`'s `reject_set_domain` refuses a
  declared set domain outright.

  A propagator that counts **several** constraints (Hall intervals over n disequalities),
  or rests on a structure the `.opb` does not carry (Régin's matching, `element`'s value
  set, a product), breaks this. **It breaks it by a bound move as readily as by a hole**,
  so an invariant phrased about holes would not see the first violator coming — that
  phrasing was the orchestrator's, and it was wrong. Measured against 3.0.2 on a
  satisfiable four-variable Hall scene (`x, y, w ∈ 2..4` saturate `{2,3,4}`, `z ∈ 2..5`):
  the Hall **bound move** `rup +1 z_ge_5 >= 1` is **refused**, and so is Régin's hole
  `rup +1 ~z_ge_3 +1 z_ge_4 >= 1`, while an `int_ne` line on the same `.opb` is accepted.
  Both pruned values are genuinely entailed — restricting `z` to `2..4`, and pinning
  `z = 3`, each make the model UNSAT — so these are true claims the checker will not take.
  Such a propagator must derive its pruning explicitly (`pol`/`ia`) **before** its trace
  line, so the line is RUP in sequence (D-0039's move, one step further), or else force
  the direct encoding (D-0019 point 3). **Adding a propagator family without classifying
  it against this invariant is the event I-X10 exists to make visible** — see D-0040 and
  the closure gate in `test/unit/test_trace.ml`.

  *Status, in I-S4's register*: the enumeration and both Hall measurements are **measured**.
  That the enumeration stays complete as propagators are added is **argued**, and the
  closure gate is what converts it into a check.

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
