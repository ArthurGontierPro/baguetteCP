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

## D-0006  Hand-written lexer and parser rather than ocamllex/menhir
Status: DECIDED
Date: 2026-09-14

Context: `dune-project` originally declared a `menhir` dependency. Using it also requires
a `(using menhir X.Y)` stanza in `dune-project`, a file held by the orchestrator while
three sessions worked in parallel — so the choice was forced earlier than it otherwise
would have been.

Decision: a hand-written scanner (`lexer.ml`) and recursive-descent parser (`parser.ml`),
about 550 lines together. `menhir` is dropped from the declared dependencies, since an
unused declared dependency misleads whoever reads the file next.

Consequences:
- Exact control of diagnostics, which SPEC section 2.1 leans on hard: every error carries
  `file:line:col`, and an unsupported builtin names itself and the milestone it belongs
  to rather than being silently skipped.
- The FlatZinc grammar for this subset is small and stable; if the accepted subset grows
  substantially, revisit this. Adding menhir later is a one-line change to
  `dune-project` plus a grammar file, not a rewrite of the front end.

## D-0007  Booleans use the order encoding on [0, 1]
Status: DECIDED
Date: 2026-09-14

Context: `Lit.pbvar` has constructors for the order encoding (`Ge`) and the direct
encoding (`Eq`) but none for a plain Boolean. A `var bool` needs *some* PB name.

Decision: encode `var bool` as the order encoding on `[0, 1]`. "b is true" is `b_ge_1`,
reached through `Lit.bool_true` / `Lit.bool_false`.

Consequences: one naming scheme instead of two, so `bool2int` channelling is free and
Booleans compose with linear constraints without a special case. The cost is that proofs
say `b_ge_1` where a reader might expect `b`. That is a real readability cost and it is
accepted deliberately — PROOF-FORMAT section 3 exists to make names predictable, and a
second scheme for the same concept would undermine it more than an unfamiliar spelling
does.

## D-0008  Backtracking uses proof levels, not per-reason deletion
Status: DECIDED
Date: 2026-09-14
Supersedes the original advice in PROOF-FORMAT section 5.

Context: PROOF-FORMAT originally said to retire reasons on backtrack with one `del` per
reason. VeriPB has `# <level>` (set level) and `w <level>` (wipe level), which this
document had mis-documented — `#` was wrongly described as a comment marker.

Decision: tag derived constraints with the solver's decision level via `#`, and retire
them on backtrack with a single `w`.

Consequences: one proof line per backtrack instead of one per reason. The proof then
grows with the interesting part of the search rather than with its total size, which is
the difference between a proof you can check and one you cannot. Individual `del id N`
remains correct for constraints not tied to a decision level, such as forgotten learned
clauses.

## D-0009  A bound fact in a `pol` needs a constraint id, not a literal
Status: DECIDED
Date: 2026-09-14
Arose from: M1-T7, where the propagator and the proof bridge were written against
incompatible readings of `Explanation.Linear`.

Context: `Explanation.Linear (terms, rhs)` was documented as "renders to `pol` over the
model constraint". Two sessions read that differently and both readings were defensible:
the propagator built `Linear` as *the order-encoding unit literals witnessing the current
bounds of the other variables* (`Cut (Trivial, Linear units, 1, 1)`, model row plus the
bound facts), while the bridge read it as *a restatement of the model row itself* and
emitted `pol <model_id>`, discarding `terms` and `rhs`.

The bridge's reading is not merely a different convention, it is unsound as a
justification: veripb accepts a restatement, so the tests passed, but the id handed back
does not state what the explanation claims, and the composition of the two halves emits
twice the model row and justifies nothing.

The propagator's reading, however, **cannot be rendered as a `pol` at all**. Checked
against veripb 2.2.2 directly:

```
f 1                  * model: 1 x1 >= 1
pol x2
rup 1 x2 >= 1 ;      * Failed to show '1 x2 >= 1' by reverse unit propagation
```

A bare literal in a `pol` expression is the *trivial axiom* `x2 >= 0`. It does not assert
that the literal holds. So a list of literals can never tell a `pol` step that
`x_i >= lo_i` currently holds; only a constraint already in the checker's database can,
and during search that means the constraint the solver logged when it made the decision
or the earlier pruning (D-0008 gives those their levels).

Decision: an explanation that appeals to a bound fact must name the **constraint id** that
established it. Until `Explanation.t` can carry ids, `Linear (terms, rhs)` renders as
`rup` of exactly the constraint it states -- faithful, and the bound facts it needs are in
the checker's database once search logs its decisions. `pol` remains the target and
returns once ids are expressible.

Consequences:
- `docs/PROOF-FORMAT.md` section 4's `int_lin_le` row ("`pol` -- the model constraint plus
  order-encoding units, one division") describes the destination, not what M1 emits. The
  table now says so.
- `Cut` has no division operator, so even with ids the "one division" of a bounds pruning
  is not expressible today. Both gaps are the same gap, and both are properly part of
  **D-0003**, which is still open: whether an explanation is a *value* naming ids or a
  *computation* that derives them is exactly the (a)-versus-(b) question there. This is
  the first place where leaving D-0003 open has cost real work, which is itself an
  argument for closing it before M2-T3.
- End-to-end validation of an `int_lin_le` justification is blocked until search logs
  decisions as constraints (M1-T10). A unit test at level 0 has no bound facts in the
  database and cannot stand in for it.
- Nothing yet expands an integer linear term `sum a_i x_i` into PB literals over the order
  encoding -- `Opb` constraints are built over `Lit.t` directly. The model row an
  `int_lin_le` justification must cite therefore cannot be written yet. That is M1-T7c.

## D-0010  A bound fact is a chain of order literals, not one literal
Status: DECIDED
Date: 2026-09-14
Arose from: M1-T7b round 2, driving the real `int_lin_le` propagator into veripb.

Context: `int_lin_le` explains a pruning with `Cut (Trivial, Linear units, 1, 1)`, where
`units` is meant to say "the other variables are at these bounds". It built one literal
per excluded term, `(a_i, x_i_ge_b_i)`, with `rhs = sum_i a_i * b_i`.

That is dimensionally wrong. An order literal is 0/1, so `a_i * x_i_ge_b_i` reaches at
most `a_i`, while the row demands `a_i * b_i`. For `b_i = 1` the two coincide, which is
why a one-step bound verified and looked like a working shape. A two-step bound is
rejected outright:

```
Hint: Failed to show '1 x2_ge_2 >= 2' by reverse unit propagation
```

This is arithmetic, not a missing fact: no proof state can satisfy that row.

Decision: a bound fact is stated in the **same currency as the model row** — the order
encoding's own expansion, `x = lo_decl + sum_{v = lo_decl+1}^{hi_decl} [x >= v]` (M1-T7c,
`Encoding.expand_int_lin_le`). So, for coefficient `a` and *declared* bounds
`[lo_decl, hi_decl]`:

- a lower bound `x >= b` contributes the chain `(a, x_ge_v)` for `v` in
  `lo_decl+1 .. b`, adding `a * (b - lo_decl)` to the right-hand side;
- an upper bound `x <= b` contributes `(|a|, Lit.le x u)` for `u` in `b .. hi_decl-1`
  — that is `~x_ge_(u+1)` — adding `|a| * (hi_decl - b)`.

Both are measured **relative to the declared bound**, never against the raw value, which
is the mistake above: the constant `lo_decl` lives on the right-hand side of the model
row, so an explanation that omits it is speaking a different language from the row it
must combine with.

Consequences:
- The bound used is the *current* one from the store; the offset is the *declared* one
  from the model. A propagator therefore has to capture its variables' declared bounds at
  construction, when the store still holds them, rather than reading the store at prune
  time. This is a new obligation on every propagator that appeals to a bound.
- It follows that **`Store`'s initial domains and `Encoding`'s declared domains must
  agree**, since the row's constant comes from one and the explanation's offset from the
  other. Nothing wires the two together yet; when M1-T11 does, that agreement is an
  assertion at wiring time, not a hope. Recorded here so it is not discovered a third time.
- Chain construction belongs in one shared helper that every propagator calls, not copied
  into each. `int_lin_le` is the reference propagator precisely because four more are
  about to copy it.
- `Explanation.Linear` keeps meaning literally what it says — a PB constraint over the
  literals listed. The alternative, having `Justify` silently expand a single literal into
  its chain, was rejected: it would make the emitted proof differ from what the value
  states, which is the exact failure mode D-0009 records.
