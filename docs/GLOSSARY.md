# Glossary

Words this project uses in a specific way. CP and proof-logging vocabulary overlap
badly — "constraint", "reason", "explanation" and "clause" all mean different things on
either side of the fence, and sessions drift apart when they are used loosely.

---

**Assignment** — a map from variables to single values. *Total* if every variable is
fixed.

**Bounds consistent** — a propagator that guarantees `lo` and `hi` of each variable can be
extended to a solution of that constraint, saying nothing about interior values.

**Channelling** — constraints linking two encodings of the same variable, here the order
encoding and the direct encoding. See `docs/PROOF-FORMAT.md` §3.

**Constraint** — ambiguous, so always qualify:
- *model constraint* — something from the FlatZinc file
- *proof constraint* — a numbered line in the `.opb`/`.pbp`, referenced by a `Cid.t`
Never write bare "constraint" in code comments where it could be either.

**Cutting planes** — the proof system VeriPB checks: linear combination, division with
rounding, saturation, over PB constraints. `pol` steps are cutting-planes derivations.

**Decision level** — depth in the search tree. Level 0 is what propagation alone gives.

**Direct encoding** — Booleans `x_eq_v` meaning `x = v`.

**Domain consistent** (= *generalised arc consistent*) — every remaining value of every
variable extends to a solution of that constraint.

**Explanation** — *this project's* term for the reason attached to a pruning or a failure,
in a form the proof layer can render. It is a value of `Explanation.t`. Distinguish from:

**Higher-order explanation** — deliberately unsettled; see D-0003. Do not use the phrase
in code or comments without saying which reading you mean.

**Justification** — the concrete proof step(s) an explanation renders to. Explanations are
solver-side; justifications are proof-side. `lib/proof/justify.ml` is the boundary.

**Nogood** — an assignment fragment known to extend to no solution. Learned from
conflicts. A clause over encoding literals.

**OPB** — the pseudo-Boolean model file format that VeriPB reads alongside a proof.

**Order encoding** — Booleans `x_ge_v` meaning `x >= v`. The default here because bound
prunings become single literals.

**pol** — VeriPB's cutting-planes rule, reverse Polish over proof-constraint ids.

**Propagator** — code that removes values from domains given one model constraint.
"Propagation" is running them to fixpoint.

**Pruning** — removing values from a domain. Every pruning carries an explanation (I-P4).

**Reason** — informal synonym for explanation. Prefer "explanation" in code.

**RUP** (reverse unit propagation) — a proof step checked by propagating the negation to
contradiction. Cheaper to emit, more expensive to check than `pol`.

**Trail** — the undo log making domain mutation backtrackable.
