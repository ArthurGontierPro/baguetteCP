# Decision log

Append-only. Newest at the bottom. Never edit a decided entry — supersede it with a new
one that references it.

Check this file before re-arguing a design point; several are settled and the reasoning
is not obvious from the code.

Format:

```
## D-NNNN  <title>
Status: OPEN | DECIDED | SUPERSEDED by D-MMMM
Date: YYYY-MM-DD
Context:   what forced the choice
Decision:  what was chosen
Consequences: what this costs us, including what it makes harder
```

---

## D-0001  Implementation language: OCaml 5 + dune
Status: DECIDED
Date: 2026-09-14

Context: the solver's centre of gravity is the explanation type — a recursive sum type
with a deferred/lazy constructor, pattern-matched everywhere. Candidates were Rust
(fastest, static help on proof-id lifetimes, closest precedent in Pumpkin), OCaml
(most readable for this shape, functors for swapping domain representations,
frictionless closures for deferred explanations) and C++ (best ecosystem interop,
worst explanation layer).

Decision: OCaml 5 with dune.

Consequences:
- Deferred explanations are closures rather than enum-encoded thunks. This is the main
  win and it is a large one for readability.
- We get no static help on proof constraint-id lifetimes. Compensated with a runtime
  audit mode (`BAGUETTE_PROOF_AUDIT=1`, invariant I-X2).
- Expect roughly 2-4x off a C++ equivalent, and minor-GC pressure in the propagation
  loop is the known risk. Mitigation is deferred to M6-T2 deliberately: correctness and
  verified proofs first.
- Tooling is three tools (opam, dune, the compiler) rather than one. `scripts/bootstrap.sh`
  exists so no session has to rediscover the setup.

## D-0002  Proof format: VeriPB 2.0, no local extensions
Status: DECIDED
Date: 2026-09-14

Context: we could define a CP-native proof format, or target an existing checked one.

Decision: emit VeriPB 2.0. Rule vocabulary restricted to the table in
`docs/PROOF-FORMAT.md` §2.

Consequences: we inherit a verified checking story (and `cake_pb`) for free. If some
piece of CP reasoning turns out not to be expressible, that is a research finding to
write up — not a licence to extend the format in-tree.

## D-0003  What "higher-order explanation" means here
Status: **OPEN** — blocks M3-T2
Date: 2026-09-14

Context: the project goal names "explanations of higher order". Two readings are live and
they produce different code:

(a) *Higher-order logic*: explanations expressed in a richer language than clauses —
    PB constraints, cutting planes, quantified or parameterised reasons. This is mostly
    about what `Explanation.t`'s constructors can hold.

(b) *Higher-order functions*: explanations as first-class deferred computations —
    a reason is a function, reasons compose by function composition, a propagator hands
    back a closure that is forced only during conflict analysis. This is about the
    lazy/composition machinery, and it is what the scaffolded `Deferred` constructor
    assumes.

These are not exclusive; the question is which one is the project's contribution and
therefore which one gets the design investment.

Decision: **not yet made.** Whoever resolves this, record the reasoning, not just the
verdict — the rest of the explanation design follows from it.

## D-0004  all_different justification strategy
Status: OPEN — M4
Date: 2026-09-14

Context: Hall-interval pruning for bounds-consistent `all_different` has a known
cutting-planes justification; domain-consistent (Régin/matching-based) pruning does not
have an obvious cheap one.

Decision: pending. M4-T1 does bounds consistency first precisely so that M4-T2 can be
evaluated against a working baseline.

## D-0005  Domains decline to punch holes in enormous ranges
Status: DECIDED
Date: 2026-09-14

Context: `Domain.t` allocates its hole bitset lazily, sized to the declared range. A
variable declared over a very wide range would make that allocation absurd, but the
alternative representations (a balanced set, a run-list) cost O(log n) membership, and
SPEC section 3.1 requires O(1).

Decision: above `max_hole_span = 2^20` values, `Domain.remove` declines to punch an
interior hole and returns `Unchanged`. Bound movements are never affected — they do not
touch the bitset.

Consequences: declining to prune is *sound* (we only ever keep values we could have
removed, never remove ones we should have kept) and leaves search complete, so no
solution is lost and no proof step is affected. It makes propagation weaker on such
variables, which is a performance question, not a correctness one. The FlatZinc subset in
SPEC section 2.1 does not produce domains this wide in practice. If it ever does, the fix
is a second representation for wide domains, not raising the constant.

This is the kind of behaviour that looks like a bug to whoever next reads a weak
propagation result, which is why it is written down rather than left in a comment.
