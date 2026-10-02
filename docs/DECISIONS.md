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
Status: SUPERSEDED by D-0023
Date: 2026-09-14

Context: we could define a CP-native proof format, or target an existing checked one.

Decision: emit VeriPB 2.0. Rule vocabulary restricted to the table in
`docs/PROOF-FORMAT.md` §2.

Consequences: we inherit a verified checking story (and `cake_pb`) for free. If some
piece of CP reasoning turns out not to be expressible, that is a research finding to
write up — not a licence to extend the format in-tree.

## D-0003  What "higher-order explanation" means here
Status: **RESOLVED by D-0026** (2026-09-16) — was OPEN, blocked M3-T2
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

Decision: **made in D-0026** — (a) and (b) are layered, not alternatives: reasons are
declarative data, justifications stay the reified cutting-planes expression. The
reasoning is recorded there, as this record asked.

## D-0004  all_different justification strategy
Status: **CLOSED — ACCEPTED, 2026-09-22 by M4-T2.** Régin's pruning **does** have a
cutting-planes justification, and **the existing ADT expresses it with no new constructor.**
The resolution is recorded at the bottom of this record.

*(Original status line, kept: OPEN — M4)*
Date: 2026-09-14

Context: Hall-interval pruning for bounds-consistent `all_different` has a known
cutting-planes justification; domain-consistent (Régin/matching-based) pruning does not
have an obvious cheap one.

Decision: pending. M4-T1 does bounds consistency first precisely so that M4-T2 can be
evaluated against a working baseline.

### RESOLUTION, 2026-09-22 (M4-T2, agent-regin)

**The bridge is a fact about matchings, not about proofs.** With `M` a matching saturating the
variables, `u` a variable, and `K = {u} ∪ reach(u)` in the digraph *"x → x′ when M(x′) ∈ dom(x)"*:
if no member of `K` has a free value in its domain, then every `w ∈ dom(x)` for `x ∈ K` is `M(x′)`
for some `x′` reachable from `x`, so `N(K) = M(K)` and `|N(K)| = |K|` — **K is a Hall set**.
Conversely an edge `(y,v)` in no maximum matching gives exactly such a `K`. So **every Régin
pruning is witnessed by a Hall set**, and enumerating `K` over every `u` is **complete** — which
is what earns the `Domain` tag rather than merely asserting it.

**So the justification is M4-T1's counting argument over a value SET rather than an interval**,
stopped one step earlier: instead of telescoping the excluded values into a bound, weaken away
all but one and the row is `~y_eq_v >= 1`. `core_summands` is parameterised by `~vals`, and
stage 1 emits **byte-identical** summands.

**Where it could have stopped being expressible, and did not**: narrowing a Hall variable's
at-least-one line past an **interior hole** — something an interval never forces. Both level
cases are in the existing ADT: a **root-established** hole uses `Defining` (exact cancellation,
the `pol` still closes), and a hole **under a decision** uses `Explanation.clause` with the facts
carried into the pruning's `Reason` so the trace line stays true. **`explanation.ml` and
`justify.ml` are untouched.**

> **D-0044's no-new-constructor table held eight times, broke once (D-0064), and does NOT break
> here — on the row that was supposed to be the hard one.** D-0061 predicted the ADT would carry
> it; that prediction is confirmed.

**What stays open, and is not this record's:**

- **The staging cutoff (256 var-value pairs) is adopted from GCS and NOT re-measured here.** Every
  model in this suite is two orders of magnitude below it, so the staged branch is exercised only
  by a test that lowers the cutoff.
- **The Hall-set choice lever D-0061 flagged is still unmeasured, and now has a second dimension**:
  `regin_pass` takes the first tight set it finds per `u`, not the smallest — alongside M4-T1's
  interval scan taking the lexicographically first tight interval, not the narrowest.

## D-0005  Domains decline to punch holes in enormous ranges
Status: DECIDED — the cap here covers the domain bitset only. The proof-side width cost
it does *not* cover, and why this record's remedy is unavailable there, is **D-0028**.
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
Status: DECIDED — mechanism SUPERSEDED by D-0024 (VeriPB 3.0 has no level stack)
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
Status: DECIDED — the chain requirement stands. What it costs at width, and what a
cheaper restatement must preserve to keep convincing the checker, is **D-0028**.
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

## D-0011  One propagator instance, one model row
Status: DECIDED — but **read D-0015 first**: its `Model_row` closed the ADT gap this
record rests on, so a derivation citing several model rows *is* expressible (M4-T1's
Hall-interval justification needs exactly that). Whether the one-instance-one-row
*policy* still stands on its own cost grounds is settled by **D-0027**: the rule is
restated as one about *naming* rows, not counting them, and the decomposition half stands.
Date: 2026-09-14
Arose from: M1-T8, where `int_lin_eq` was built as one propagator over two model rows.

Context: `Explanation.Trivial` means "the model constraint itself justifies this". It
carries no payload, so *which* constraint that is has to come from somewhere else.
`Justify` takes it from `ctx.model_id`, which the caller sets.

`int_lin_eq` posts as two rows (`Encoding.add_equality` returns both ids) and was
implemented as a single propagator running an `le` and a `ge` half to a joint fixpoint.
Its header proposes that a caller route each explanation to the context for whichever
half produced it, by comparing against the exposed `Linear.t` values.

That does not work for a pruning. A pruning's explanation is recorded on the trail as
`{ var; old; why }` — **the trail records no propagator identity**. A caller walking the
trail has the explanation and nothing else, so it cannot tell which half produced it, and
`Trivial` is unresolvable.

Decision: **one propagator instance justifies against exactly one model row.** An
equality posts as two `Linear` instances rather than one fused propagator. The engine
already runs propagators to a fixpoint and wakes them on the variables that changed, so
two instances reach the same fixpoint the fused loop reaches by hand — the internal
alternation duplicates the engine's own job.

Consequences:
- The propagator-to-row map stays a lookup on the instance, which is what makes `Trivial`
  resolvable at all in M1.
- In M1 this is sufficient, because reasons are demanded only for *conflicts*, which
  `propagate` returns directly to the engine — so the instance that produced it is known.
- It is **not** sufficient from M2-T3 on. Clause learning walks the trail, and there the
  explanation is all there is. Resolving that needs either the trail to record the
  propagator that made each change, or `Explanation` to carry the row — and that is the
  same "value naming ids versus computation deriving them" question as **D-0003**, which
  remains open. This is the second time D-0003 has blocked concrete work (D-0009 was the
  first). It should be closed before M2-T3 starts, not during it.
- Cost: a little more queue churn than a fused loop. M6 is deliberately the last
  milestone, and a routing hazard that every future caller must get right is worse than
  queue churn.

## D-0012  A branch nogood is not RUP-derivable from the model rows alone
Status: DECIDED
Date: 2026-09-14
Arose from: the M1-T10 integration test, running search over `[0, 3]` domains.

Context: M1-T10 logs one clause per failed branch — "not all of these decisions hold
simultaneously" — over the decision literals, by `rup`, and resolves them up the tree.
It avoids rendering propagator explanations during search at all. The argument was that
`rup`'s check is exactly "assume these decisions and re-derive the conflict", and that
the checker can always replay it because every M1 bounds propagator *is* generalised unit
propagation over its own row.

**That argument is false**, and its tests could not see it: they use `[0, 1]` domains,
where the order encoding degenerates (`x = [x >= 1]`) and the rows become clauses, on
which PB unit propagation really is as strong as bounds propagation. Over `[0, 3]` it
fails. From the model `x1 = x2, x3 = x4, x1+x2+x3+x4 = 7`, all in `[0, 3]`:

```
rup +1 ~x1_ge_1 +1 x2_ge_1 >= 1 ;              accepted
rup +1 x3_ge_3 +1 x1_ge_2 +1 ~x1_ge_1 >= 1 ;   Failed ... by reverse unit propagation
```

The second is the nogood for the branch `x1 = 1, x3 <= 2`. It is *semantically valid* —
`x1 = 1` forces `x2 = 1`, leaving `x3 + x4 = 5` with `x3 = x4`, which `x3 <= 2` refutes.
It is simply not reachable by unit propagation: the sum rows carry slack 2 or more under
those assumptions, so no literal is ever forced and propagation stalls before reaching a
contradiction. Bounds propagation across several rows is strictly stronger than PB unit
propagation on each row.

Decision: a search proof **must carry the propagator reasoning**, not delegate it to the
checker's `rup` search. The nogood scheme stays as the skeleton — one clause per failed
branch, resolved up the tree — but each branch must first emit the derivation that
actually refutes it, built from the `Explanation.t` values the propagators already
produce, so that the nogood is then reachable. This is option (a) from M1-T10's original
framing: derived constraints guarded by the negated active decisions.

Consequences:
- `Justify`, `Explanation` and the per-propagator justification work (M1-T7, M1-T8) are
  **load-bearing for search after all**. M1-T10's report concluded they were not needed;
  that conclusion held only for 0/1 domains.
- The integration test's `k = 7` case is an expected failure (`~xfail_veripb`) until this
  lands, using the same discipline as `test/models/PENDING`: if it starts passing, the
  suite fails and tells you to delete the marker. The solver's *answer* is correct; its
  *proof* is not, and that distinction is what the marker records.
- `k = 8` (SAT) passes and always would have: `conclusion SAT` checks the assignment
  against the model, so a SAT run's nogoods carry no weight. **An end-to-end test that
  only covers SAT proves very little here.** Any future end-to-end coverage must include
  UNSAT.
- This is the third finding in a row that was invisible on a toy instance and visible on a
  slightly larger one (D-0009 was invisible because a restatement is valid, D-0010 because
  a one-step bound is the value where the arithmetic coincides). The pattern is strong
  enough to act on: **no proof-layer claim should be believed on the strength of 0/1
  domains or single-step bounds.**

## D-0013  How a bounds conflict is justified: weaken, divide, add
Status: DECIDED for the no-decision case; the branching case is **OPEN** (see below)
Date: 2026-09-14
Follows: D-0012, which established that asserting a conflict is not enough.

Context: D-0012 left the question "what should search emit instead". The smallest form of
the question needs no search at all. For `2*x1 + 4*x2 = 7` with both in `[0, 3]`, bounds
propagation refutes at the root — the `>=` row forces `x2 >= 1`, the `<=` row forces
`x2 <= 1`, and `2*x1 = 3` has no integer solution — and the solver emitted `rup >= 1 ;`,
a bare empty clause, which veripb rejects.

Decision: a bounds conflict is justified by **pure cutting planes**, no `rup`. Verified
against veripb 2.2.2, which accepts this in full and concludes UNSAT:

```
f 6                     * 5 is the <= row, 6 the >= row
pol 6 ~x1_ge_1 2 * + ~x1_ge_2 2 * + ~x1_ge_3 2 * + 4 d    * 7:  x2 >= 1
pol 5 x1_ge_1 2 * + x1_ge_2 2 * + x1_ge_3 2 * + 4 d       * 8:  x2 <= 1
pol 6 8 4 * + 2 d                                          * 9:  x1 >= 2
pol 5 7 4 * + 2 d                                          * 10: x1 <= 1
pol 9 10 +                                                 * 11: contradiction
conclusion UNSAT : 11
```

The rule it establishes, for a pruning on `x_j` from `sum a_i x_i <= c`:

1. Start from the model row, in the `>=` form the `.opb` holds.
2. For every other variable `i`, remove its contribution by adding `|a_i|` times a
   **literal axiom** per order literal — the positive literal to pin `x_i` at its declared
   *lower* bound, the negated literal to pin it at its declared *upper* bound, whichever
   direction the pruning needs. This is the step that makes D-0009's finding harmless:
   an axiom cannot assert a bound, but it can *weaken one away*, which is all this needs.
3. Where `x_i` sits at a bound that was **derived** rather than declared, cite that
   constraint's id, multiplied by `|a_i|`, instead of the axioms.
4. Divide by `|a_j|`. VeriPB's `d` rounds the right-hand side up, which is exactly the
   ceiling a bounds push needs — this is PROOF-FORMAT section 4's promised "one division",
   and it is why unit-coefficient tests prove nothing about this step.
5. A conflict is two opposite bounds on the same variable, added: their sum normalises to
   `0 >= 1`.

Consequences:
- Every one of these steps is `pol`. The project's standing preference for `pol` over
  `rup` (PROOF-FORMAT section 2) is not merely satisfiable here, it is the natural form;
  the checker never has to search.
- Steps 2 and 3 are the same operation with a different source, so `Explanation` needs to
  distinguish "declared bound, weaken with axioms" from "derived bound, cite this id".
  It currently expresses neither: `Linear` carries literals with no ids (D-0009) and
  `Cut` has no divisor for step 4 (D-0010, D-0011). **This is the concrete shape of the
  change D-0003 has been blocking**, and it is now specified precisely enough to make.
- **Still open: the branching case.** A constraint derived inside a branch is valid only
  under that branch's decisions, and a decision is not in the database. The natural
  extension is to derive constraints that *carry the decision variable's order literals
  with large enough coefficients*, making them globally valid — for `2*x1 + 6*x2 + 2*x3 = 9`
  the constraint `x1 + 9*[x2>=1] + x3 >= 5` is globally valid and gives the branch bound
  when `[x2>=1]` is 0. Getting the second branch's bound tight enough by the same route
  was not achieved by hand here and is the open work. Until it is settled, the UNSAT
  models in `test/unit/test_endtoend.ml` stay xfail.
- Artefacts: `scratchpad/research/r.opb`, `r.pbp` (session-local).

## D-0014  Decision-free lemmas strengthen a branch nogood, but do not yet close it
Status: **PARTIAL** — the mechanism is confirmed; the scheme is not complete
Date: 2026-09-14
Follows: D-0012, D-0013. Does **not** close D-0013's open half, despite being asked to.

Context: D-0013 left open how to justify a branch refutation, since a decision is not
entailed by the model and `pol` cannot assert one (D-0009). Investigated by hand-deriving
proofs and checking every one against veripb 2.2.2.

Three things came back, and they matter in different directions.

**1. Both instances chosen to exercise branching turn out not to need it.** They are
refutable at the root, decision-free, by `pol` alone. For `2*x1 + 6*x2 + 2*x3 = 9` over
`[0,3]`, dividing each row by 2 gives `x1 + 3*x2 + x3 >= 5` and `<= 4` — a contradiction
in three lines. For `x1 = x2, x3 = x4, x1+x2+x3+x4 = 7` the equalities are *added into*
the sum row to eliminate `x2` and `x4`, then the same division applies. Both verified.

This generalises D-0013 in a way worth stating: where two rows are linked by a
channelling equality, **add the equality row** with a coefficient that cancels the
redundant variable, rather than pinning either variable to a literal. These are
Chvátal–Gomory arguments, and the order encoding represents each variable's whole
declared domain, so cutting planes sees them without a case split.

**2. Interning those lemmas turns a rejected nogood into an accepted one.** D-0012's own
failing step — `rup +1 x3_ge_3 +1 x1_ge_2 +1 ~x1_ge_1 >= 1 ;` — is accepted verbatim,
same clause and same decisions, once the two decision-free lemmas are in the database.
This is the first direct evidence for what to *do* about D-0012 rather than what is wrong
with it: `rup` was not too weak in principle, it was running against too weak a database.

**3. It is not enough.** The sibling nogood for the `x1 = 2` sub-branch still fails with
the same lemmas interned, because unit propagation forces nothing from either lemma
alone and never adds two constraints together. So a scheme of "intern decision-free
lemmas, then `rup` the nogood" closes some branches and not others, and nothing here
says which in advance.

Decision: record the mechanism as confirmed and the scheme as **incomplete**. Do not
implement "intern and hope" as though it were a rule. The remaining gap is exactly the
case where closing a leaf needs two lemmas *combined*, which is a `pol` step no `rup`
will find on its own.

Also flagged, because it is a real architectural departure rather than a detail: the
proposed rule has the **proof layer derive things the solver never derived**. The root
refutations above are not reasoning any bounds propagator performs — the solver branches
on these models. A proof need not mirror the search, and shortening it this way is
legitimate, but "the proof layer runs its own derivations" is a different system from
"the proof layer records what the solver did", and it should be adopted deliberately
rather than as a side effect of fixing a rejected step.

Consequences:
- `rup` is not eliminable. Closing a leaf whose contradiction appears only under an
  assumed decision is exactly what `rup`'s check does and what `pol` structurally cannot
  (D-0009). It stays legitimate here rather than being a workaround, and
  `docs/PROOF-FORMAT.md` section 2's preference is still honoured everywhere else.
- The UNSAT models in `test/unit/test_endtoend.ml` stay xfail. Three of them are
  root-refutable and should start verifying when M1-T12 lands; the two branching ones
  need the gap above closed first.
- None of this generalises past linear bounds consistency. It rests on Chvátal–Gomory
  completeness for integer-linear infeasibility over an exact domain representation.
  Hall-set reasoning (D-0004, M4) is a different problem and this record says nothing
  about it.
- For **D-0003**: this is concrete evidence for reading (a), a richer explanation
  language. What has to be expressible is a *derivation recipe* — which rows to add, at
  which coefficients, which variable to eliminate — not merely a value versus a
  computation. That is the fourth finding to land on D-0003.
- For **M2-T3**: a decision-free lemma is precisely a learned clause with root-level
  lifetime. Clause learning should test whether a conflict clause depends on any decision
  before tagging it to a level, since a level-0 lemma is strictly more valuable.

## D-0015  Explanation gets a divisor, a named row, and a weaken-only summand
Status: DECIDED
Date: 2026-09-14
Implements: D-0013. Supersedes the ADT gaps recorded in D-0009, D-0010 and D-0011.

Context: D-0013 specified the derivation and named what `Explanation.t` could not say —
`Linear` carries literals but no id, `Cut` has no divisor, and nothing distinguished
"still at the declared bound, weaken it away" from "at a derived bound, cite that id".

Decision: three additions.

- `Combine (summands, divisor)` is one `pol` step: sum the summands, then divide unless
  the divisor is 1.
- A summand is `Term (coeff, t)` — recurse and cite the resulting id, as `Cut` already
  did — or `Weaken` , a sum of literal axioms. **`Weaken` is deliberately not a `t`** and
  cannot be emitted on its own, because D-0009 established that an axiom cannot assert a
  bound, only weaken one away. Making that structural beats leaving it a convention
  someone has to remember, which is how D-0009 happened.
- `Model_row id` names a constraint id directly rather than going through the single
  ambient `ctx.model_id`. This is D-0011's unresolvable `Trivial` made tractable: one
  `Combine` can cite an explanation another propagator instance built against a
  *different* row, in the same tree, which one mutable pointer cannot express.

Consequences:
- Every propagator instance must be given its own row id at construction. Without it the
  explanation falls back to `Trivial` and reinherits D-0011's ambiguity — which is not a
  hypothetical: `test_endtoend.ml` computed the ids and discarded them, and that is
  exactly what it did.
- A root conflict now logs its real derivation and veripb accepts it. Two of the
  integration test's UNSAT models flipped from xfail to passing on this.
- A root refutation's intermediate steps sit at level 0 where no `w` retires them, so the
  emitting caller must delete them before `conclusion` or the I-X2 audit fails. It did.
- Cross-instance conflicts — two instances tightening opposite bounds on one variable,
  caught by `Store`'s own check rather than either row's slack — take a second
  combination path that no model in the current suite exercises. It is covered by code
  review only, which is worth knowing given this project's history with untested paths.

## D-0016  The `pol` vocabulary, and what it can and cannot reach
Status: PARTIAL — amends D-0014
Date: 2026-09-14

Context: whether a `pol` step can close a leaf that `rup` cannot, since unit propagation
never adds two constraints together and adding is what `pol` does.

Findings, all checked against veripb 2.2.2:

1. **`pol` can recover any leaf's nogood once the model is refuted at the root**, by
   adding the leaf's decision literals as axioms on top of the derived contradiction.
   Verified for the `x1 = 2` leaf that D-0014 could not close. But the honest shape is
   narrower than it sounds: it works by going *through* the root contradiction, so it
   recovers a clause shape rather than doing branch-local reasoning. Where a root
   refutation exists, the per-branch nogood scheme is simply unnecessary.
2. **Keeping a decision's literal rather than weakening it away is a real and more general
   operation.** Keeping `x1_ge_2` in D-0013's derivation yields `x1 < 2 => x2 >= 1`,
   globally valid and strictly more general than the `x1 = 0` instance of it. It did not
   close the leaf here, for a reason worth recording: that model's refutation runs through
   the equalities, not through `x1`'s bound family, so the kept literal was not the one
   the refutation depends on. **Guarding the wrong literal produces a valid but useless
   generalisation** — so a derivation recipe must identify which decision a branch's
   refutation actually turns on.
3. **No genuinely branch-only instance has been found.** Three instances built to require
   branching turned out not to, the third (`x1 + 2*x2 = 4`) being settled by `rup` at the
   bare root with no decisions asserted. Chvátal–Gomory completeness for integer-linear
   infeasibility over a bounded box is a structural reason to expect none exists in this
   class: **branching is a search strategy here, never a proof necessity.** That does not
   extend past linear arithmetic — Hall-set reasoning (D-0004) is a different problem.

Correction to a claim made in reaching these: `rup` is **not** "complete cutting-planes
search inside the checker". It is reverse unit propagation over PB constraints — stronger
than clausal unit propagation, weaker than cutting planes. The third instance's fact is
reachable by plain PB propagation: asserting `x1 >= 3` forces `x1`'s whole order family,
the `<=` row then forces every `~x2` literal, and the `>=` row is violated. Nothing
stronger than propagation is involved, and the distinction matters because it is the
difference between "the checker will find it" and "the checker will find it if it is one
propagation away".

Consequences:
- Look for a root refutation before emitting a per-branch nogood; it can make the nogood
  machinery unnecessary for that model entirely.
- `rup` stays legitimate where composing the `pol` chain mechanically is harder than the
  checker's own propagation, which includes some decision-free facts, not only
  branch-dependent ones.
- Still open: a hand-derivable `pol` chain for the third instance's parity fact, and an
  instance where a kept decision literal is genuinely load-bearing.

## D-0017  A SAT run's nogoods are checked too, so SAT proofs fail as well
Status: DECIDED
Date: 2026-09-15
Amends: D-0012, whose consequences section overstates one point.

Context: M1-T14 wired the CLI and added `test/models/chain_sat.fzn`, a **satisfiable**
model with a unique solution (`b = a+1`, `c = b+1`, `a+b+c = 6`, so `a = 1, b = 2, c = 3`).
The solver gets the right answer. veripb rejects the proof.

D-0012 says, of its own satisfiable instance:

> `k = 8` (SAT) passes and always would have: `conclusion SAT` checks the assignment
> against the model, so a SAT run's nogoods carry no weight.

The second clause is false as stated. It is true that the *conclusion* does not depend
on them. It is not true that they carry no weight, because **veripb checks every rule as
it is emitted**, not only the ones the conclusion cites. A nogood logged while the search
is still looking for its solution is a proof step like any other, and an unreachable one
sinks the whole proof. The entire emitted proof for `chain_sat` is:

```
f 30
# 1
rup +1 a_ge_1 >= 1 ;        <- rejected here, line 4, long before the conclusion
# 1
w 1
conclusion SAT : a_ge_1 ~a_ge_2 ... c_ge_3 ~c_ge_4 ...
```

`indomain_min` tries `a = 0` first; that branch fails, and the nogood "not `a <= 0`" is
logged. It is true — `a = 0` forces `b = 1`, `c = 2`, and `3 <> 6` — and it is not
reachable by reverse unit propagation, because getting there means bounds propagation
across three equality rows. That is precisely D-0012, arriving through a door D-0012 said
was closed.

Decision: record the correction, and treat the branching gap (D-0013's open half, M1-T13)
as gating **satisfiable** models too, not only unsatisfiable ones.

Consequences:
- The practical reach of M1-T13 is much larger than the roadmap's framing suggests. Any
  model whose search takes one wrong turn before finding a solution emits an unverifiable
  proof, and that is most models of any size. "The UNSAT models stay xfail" (D-0013,
  D-0014) understates what is xfail.
- Why D-0012's claim survived this long: a SAT run only logs a nogood if some branch
  *fails first*. Every satisfiable instance in `test/unit/test_endtoend.ml` and the two
  shipped satisfiable models happen to be solved by a search whose first choice is right
  at every level, so no nogood is ever emitted and the proof is three lines long. A model
  has to be wrong once, and recover, before this shows up at all.
- This is the fourth finding in this project to be invisible on the instances chosen to
  test the thing it breaks, and the shape repeats: the failing case needs one more step
  of something than the test instance had — one wider domain (D-0012), one further bound
  (D-0010), one restatement (D-0009), and here one wrong turn. It is worth choosing test
  instances that are *deliberately one step past* the smallest thing that exercises the
  feature.
- `chain_sat` is in `test/models/PENDING` for this reason. Its answer is checked and
  correct; only its proof is xfail. If it starts passing, the runner fails and says so.

## D-0018  A branch nogood is RUP over the branch's own logged trace
Status: DECIDED
Date: 2026-09-15
Amends: D-0012 and D-0017, whose *diagnosis* is wrong. Their observations stand.
Closes the open half of D-0013. Supersedes D-0014's framing.

Context: D-0012 observed that veripb rejects the nogood over the active decisions, and
concluded:

> bounds propagation across several rows is strictly stronger than PB unit propagation
> on each row

D-0017 carried that forward and made it gate satisfiable models too. Both observations
are correct. The conclusion drawn from them -- that the nogood is *unreachable* and needs
some new derivation to reach it -- is not.

The Glasgow Constraint Solver (`~/gcs/glasgow-constraint-solver`, the reference
implementation of this technique, McIlree's thesis) emits that nogood as a plain `rup`
with the decisions negated, and veripb accepts it. Read directly:

  - `gcs/innards/proofs/proof_logger.cc:391-410`, `ProofLogger::backtrack`: the claim is
    the empty sum `>= 1` emitted under a reason which is the guess list. Rendered, from
    their checked-in proof `.github/veripb_smoke/smoke.pbp`:

        % backtracking
        rup 1 ~i[_2][b0] 1 i[_1][in3_4] 1 i[_1][eq2] >= 1;

    which is our `rup +1 a_ge_1 >= 1 ;` with more than one decision on the stack.

  - `gcs/solve.cc:296-297`, the ordering, which is load-bearing:

        logger->backtrack(guesses, backtrack_clause_set);   // emit the nogood FIRST
        logger->forget_proof_level(depth + 1);              // then delete the trace

The reason it works for them and not for us is not the encoding and not the rule. It is
that **every propagation is logged, at the moment it is made, as its own reified line**
(`proof_logger.cc:496-541`):

    rup 1 <inferred literal> 1 ~r1 1 ~r2 ... >= 1 ;

so that when veripb checks the backtrack clause it negates it -- asserting each decision
as a unit -- and then unit-propagates *down the trace the solver already wrote*, one
single constraint at a time, to the conflict line. It is never asked to re-derive a
multi-row bounds fixpoint in one step. Their framework note (`dev_docs/literal-
encodings.tex:2027`) puts it plainly: "it is essentially the solver writing down all the
facts that it learned, at the points that it learned them."

Our `lib/core/search.ml:27` states the strategy we chose instead, in its own words:
"nothing is logged inside a branch; the branch's refutation is derived only when it
closes." That is the whole defect. There is nothing for the checker to propagate along.

This project has now spent D-0012, D-0014 and D-0017 on the wrong explanation of a
symptom. GCS records the identical mistake as a known trap (`literal-encodings.tex:1712`,
read in full):

> We record the historical trap: when the literal layer is incomplete, a replay stalls,
> and the stalled trail's *next* step is typically a bound crossing. The failure
> therefore looks exactly like "unit propagation cannot thread a bound across the
> equality". It usually is not. Twice, that misdiagnosis produced elaborate and
> unnecessary machinery -- global cross-variable coverings, durable top-level lemmas --
> for a problem that was a missing covering clause somewhere else entirely.

D-0012's wording is that misdiagnosis almost verbatim.

Decision: a branch's refutation is justified by **logging the branch's own propagation
trace**, and the nogood is then an ordinary `rup` over the negated decisions.

1. Every pruning that happens under at least one decision gets a proof line of its own:
   the order literal it establishes, disjoined with the negation of its reason's
   literals. One line per pruning, at the branch's proof level.
2. The existing D-0013 `Combine` derivation is kept and is still correct -- but it is
   applied **per bound push**, not once per conflict. Where the pruning is not plain RUP
   over the row, the `pol` is emitted at a scratch level above the branch's, the reified
   claim is emitted at the branch's level, and the scratch level is wiped immediately.
   This is GCS's `JustifyExplicitly{..., ThenRUP::Yes}` (`gcs/innards/proofs/
   infer_explicitly.hh:100-138`) and their `justify_linear_bounds`
   (`gcs/constraints/linear/justify.cc:14-45`) is our weaken/divide/add, per push.
3. A conflict under decisions logs its own reason line first, then the nogood.
4. The nogood is emitted **before** the level is wiped. Reversing these two is the bug
   this record exists to prevent someone rediscovering.

We keep our lazy variant of (1) rather than copying GCS's eager logging: the trace is
emitted when a branch actually *fails*, by walking the trail, not at every pruning on
every successful path. This is sound here for a reason that is specific to this codebase
and must be preserved -- `lib/core/prop/linear.ml`'s `snapshot_source` already pins down
*which* trail entry witnesses each bound at push time, so a reason forced later still
renders the derivation as of the moment it was made. A propagator whose `Deferred` thunk
reads live store state instead of a snapshot would silently break this, which is the
GCS `snapshot_reason` distinction (`gcs/innards/inference_tracker.hh:104-130`) arrived at
from the other direction.

Consequences:
- D-0014's "interning a decision-free lemma makes some nogoods verify, but not all" is
  explained: the lemma supplied, by hand and by luck, one of the trace lines that should
  have been there all along. Stop pursuing it as a technique.
- Nothing in `lib/proof/encoding.ml` needs to change. The encoding clauses are *not* what
  makes a branch nogood reachable -- `literal-encodings.tex:2179` is explicit that they
  "contribute nothing to the validity of any individual line". Our pure order encoding is
  in fact ahead of GCS here: GCS's OPB is two's-complement bits, so it must mint order
  atoms mid-proof with `red` and derive the ladder clauses with `pol`, all of which we
  get as axioms. Do not port that machinery.
- `Store.entry` records `old` but not the domain the pruning produced, so the literal a
  trace line must claim is not directly recoverable from a trail entry. Recording it is
  expected to be part of M1-T13.
- A proof gets longer by one line per pruning under a decision. That is the cost of the
  technique and it is not negotiable for correctness; M6 may revisit *when* lines are
  written, never *whether*.
- Testing: a RUP line asserting the fact one cares about tests nothing (`literal-
  encodings.tex:2196`). Only a backtracking justification, checked after the decisions
  are asserted, discriminates -- so the witness test for this work must branch,
  propagate to a failure, and backtrack. A root-level UNSAT model cannot catch a
  regression here. This is the fifth finding in this project invisible on the instance
  chosen to test the thing it breaks; see M1-T15.

## D-0019  A disequality needs the order encoding, not the direct one
Status: DECIDED
Date: 2026-09-15
Corrects: `docs/PROOF-FORMAT.md` section 3, which named disequalities as a reason to
introduce the direct encoding. Roadmap M1-T9's own wording ("needs direct encoding") was
wrong for the same reason.

Context: M1-T9 was scoped on the belief that `int_ne` cannot be justified over the order
encoding. The belief rests on a true statement — the order encoding cannot express `x = v`
as a single **literal** — and an unnoticed jump from "literal" to "clause". A `rup` target
is a clause, and

    x <> v   <->   ~x_ge_v \/ x_ge_(v+1)

is two ordinary order literals. Constant halves drop at the declared bounds; a
declared-fixed variable yields the **empty** clause, which is correct (it is the false
clause) and which veripb accepts as `rup >= 1 ;`.

Decision:
1. `int_ne` and `int_lin_ne` justify over the **order** encoding, as the claim disjoined
   with the negation of the reason — D-0018's trace-line shape, arrived at independently.
   No `Explanation` constructor was needed: `Clause` was enough, as PROOF-FORMAT section 4
   predicted, and that prediction was checked against the real checker rather than assumed.
2. The `.opb` carries a disequality as two big-M rows over the order encoding with one
   fresh selector Boolean, both posted through `add_int_lin_le` so that both are plain
   `>=` lines. The `.opb` must carry it at all because it is what `conclusion SAT` is
   checked against — equisatisfiability is not enough when the checker re-checks the
   assignment against the file.
3. The direct encoding stays unbuilt until M4. **The test for when it is genuinely forced
   is whether a reason has to mention a hole**: such a reason cannot be negated into a
   clause without a single literal standing for `x = v`. A disequality's reasons never do;
   `element` and `all_different` reasons do.

Consequences:
- Two rows and a `>=` apiece means the section 2 trap (an `.opb` line with `=` counts as
  **two** constraints for the `f` rule, shifting every later id) is not in play. There is
  a test asserting the checker's constraint count matches ours after posting.
- Not building the direct encoding also avoids an I-X2 problem that would have had to be
  solved first: `ensure_direct` mints `red` ids that nothing between `start_proof` and
  `conclusion` can retire, and the CLI turns the audit on by default.
- A disequality propagator *can* move a bound (removing a value at `lo` or `hi` shrinks
  the interval) and its explanation is a `Clause`, not a chain-sum. `int_lin_le`'s
  `Snap_cite` path assumes anything it cites is a unit-coefficient chain-sum over a
  declared range. See D-0020's consequences and the M1-T13 handoff; this is a real gap,
  it is reachable only at a root conflict, and it fails loudly rather than silently.

## D-0020  lin_unsat's refutation has a unit of slack, and only mutation found it
Status: DECIDED
Date: 2026-09-15
Follows from: D-0018's last consequence, which asked for M1-T15.

Context: the mutation harness's first run found that `lin_unsat`'s proof still verifies
after a coefficient inside one of its weakening `pol` steps is corrupted. Reproduced by
hand, outside the harness, against veripb 2.2.2:

    before: pol 9 y_ge_1 y_ge_2 + y_ge_3 + y_ge_4 + y_ge_5 + +
     after: pol 9 y_ge_1 2 * y_ge_2 + y_ge_3 + y_ge_4 + y_ge_5 + +
    s VERIFIED UNSATISFIABLE

The honest refutation closes at `0 >= 2`, one unit wider than a contradiction needs to be,
so a one-unit coefficient error leaves a residual that is still infeasible. The proof is
*valid*; it is simply not the proof we meant, and every test we had said it was.

Decision: keep the derivation (it is sound) and keep the finding visible. The lane is
registered as known-slack, reported on every run, and turns the suite **red as an XPASS**
if it ever starts rejecting — the anti-rot mechanism `test/models/PENDING` already uses.
Mutation lanes over `pol` steps gate on an instance whose margin is one.

Consequences:
- **"veripb accepts" is not evidence that a derivation is load-bearing.** Three of this
  project's findings (D-0009, D-0010, and this one) are cases where the checker accepted
  something that did not assert what we believed. A `pol` only has to get close enough
  that unit propagation finishes the job; slack rows still close a proof.
- Choose mutation instances at margin one. A corruption applied to a conflict with three
  units of slack proves nothing, and prints green.
- `drop-line` is accepted on every `conclusion SAT` proof, because a SAT conclusion leans
  on the assignment and nothing downstream cites a derivation step. This nuances D-0017: a
  SAT run's nogoods *are* checked when emitted, but they are not load-bearing for the
  conclusion, so deleting one leaves a valid proof. Mutation lanes that delete a line
  belong on UNSAT instances only.

## D-0021  Every pruning needs a trace line, not only the ones under a decision
Status: DECIDED
Date: 2026-09-15
Amends: D-0018, point 1, which is wrong as written. The rest of D-0018 stands and was
confirmed by building it.

Context: D-0018 point 1 says "every pruning that happens **under at least one decision**
gets a proof line of its own". Implementing it revealed that the qualifier is wrong:
**root-level prunings need lines too.**

The reason is that a `rup` check starts from nothing. It does not inherit the solver's
root fixpoint, so any root-derived bound that a branch's trace cites as a fact has to be
derivable by the checker as well, and the only thing that makes it derivable is its own
line. Measured: with level-0 lines suppressed, `offset: 2x1-2x2+4x3 = 7` is rejected.

`chain_sat` does not discriminate, and how it fails to is worth recording, because it is
this project's recurring failure mode in miniature. Measured against veripb 2.2.2 by
rewriting trace lines into same-shaped tautologies, which keeps every later constraint id
in place:

- blank the ten level-0 lines, keep the two level-1 lines: **accepted**
- blank the two level-1 lines, keep the ten level-0 lines: **accepted**
- blank all twelve, keep the conflict reason line and the nogood: **rejected**

So on `chain_sat` the two halves of the trace are individually redundant and jointly
necessary — either one suffices to rebuild enough of the fixpoint for the nogood. A test
that blanked one half and watched the proof still verify would have concluded that half
was dead weight. Only blanking everything, or running a model with an offset domain,
shows what is load-bearing.

Decision: the rule is "every pruning gets a line", with no qualifier about decisions.

Consequences:
- Level-0 lines are not covered by any `w` (nothing wipes level 0), so they must be
  deleted explicitly before `conclusion`, or I-X2 fails. `Search.solve` does this on both
  the SAT and UNSAT paths.
- D-0018 point 3, the conflict's own reason line, turns out to be **redundant for
  `int_lin_le`**: a `slack < 0` row is detected as violated by the checker's own unit
  propagation once the trace has assigned the bounds. Measured — dropping it, every model
  still verifies. It is kept because it is cheap, because it makes the final step a single
  unit propagation rather than a row violation, and because a propagator whose conflict is
  not a single-row slack computation will need it. Recorded so nobody "discovers" it is
  removable and removes it.
- The count: a proof now grows by one line per pruning, root prunings included. `chain_sat`
  went from 3 lines to 20.
- New invariant **I-X6**, which D-0018 stated only in prose: a `Deferred` thunk closes over
  a snapshot and never reads live store state.

## D-0022  A root conflict is its own contradiction only if its derivation is numeric
Status: DECIDED
Date: 2026-09-15
Amends: D-0013, whose "with no decision active there is nothing to negate, and the
propagator's own derivation *is* the contradiction" was written when `int_lin_le` was the
only propagator and is false for a second family.

Context: M1-T16's matrix found that an `int_ne` conflict with no decision on the stack was
handed to `conclusion UNSAT` as though it were a contradiction. It is not. `int_lin_le`'s
root conflict is a numeric chain closing at `0 >= positive`, which the checker can see is
infeasible. A `Clause` says "not all of these values at once", which is only a
contradiction once the facts fixing each variable to its value are present — and the root
arm wrote no trace, so they were absent. veripb: `Constraint is not a contradiction`.

Decision: a propagator's root conflict is closed as its own contradiction **only when its
derivation is a pure numeric chain**. A derivation that rests on a `Clause` anywhere —
because the reason *is* one (`int_ne` with everything fixed), or because a `Combine` folded
one in as a cited bound (D-0019's last consequence) — is closed the D-0018 way instead:
the root's own trace lines, the conflict's reason line, the derivation, and then the
**empty clause** as `rup >= 1 ;`, which is what the conclusion cites. The empty clause is
not a new shape: it is the nogood over an empty decision stack.

`Search.rests_on_a_clause` is where the two are told apart, by walking the forced
explanation structurally.

Consequences:
- D-0021's "every pruning gets a line" now covers the root conflict of a clausal reason
  too. **Measured**: both instances that pinned this bug verify *without* the root trace,
  because PB unit propagation refutes them from the rows alone — so neither is evidence
  that the trace is needed. An instance where it is: `2x>=3, 2x<=5, 2y>=3, 2y<=5, x<>y`,
  where both bounds need a division so nothing propagates from the rows; it is accepted
  with the trace and **rejected with the trace blanked**. That is the eighth case in this
  project where the instance chosen to test a thing could not see it break.
- **Folding a `Clause` into a `pol` is left in place deliberately.** It is sound — a `pol`
  derives whatever it derives — and strictly stronger than weakening it away, which
  produces `0 >= 0` and still fails to close. The defect D-0019's last consequence
  recorded was the *citation*, not the arithmetic. Weakening would also erase the very
  signal `rests_on_a_clause` reads, so adopting it later means `linear.ml` must instead
  tell `search.ml` the derivation is not self-contained.
- A disequality that removes a value strictly inside the interval moves no bound, writes
  no trace line, and no order literal can state it. That is D-0019 point 3's boundary, and
  it is where the direct encoding would become necessary.

## D-0023  Proof format: VeriPB 3.0, and the Rust checker of record
Status: DECIDED (its account of `drop-line` as a 3.0-only parse error is corrected by **D-0030**: the lane fails for the wrong reason under 2.0 as well)
**HISTORICAL in part, D-0046 (2026-09-18):** its choice of 3.0 and of the Rust 3.0.2 as the checker of record is IN FORCE and is now the whole arrangement. Everything it says about 2.0 still being emitted, about the dual-format suite, and about the Python 2.2.2 as a second checker describes a state that no longer exists. Kept because the measurements that chose 3.0 are the reasoning, not the contract.
Date: 2026-09-15
Supersedes D-0002.

Context: the project emitted VeriPB 2.0 and checked with the Python VeriPB 2.2.2 at
`~/.local/bin/veripb`, because that is what came first on `$PATH`. A Rust VeriPB 3.0.2
was installed at `~/.cargo/bin/veripb` and unused. Two questions: which checker, and
which format.

Everything below was produced by running a checker. This entry contains no claim about
VeriPB that was reasoned rather than measured; where a previous session's note said
otherwise, the measurement is given and the note is contradicted.

### The equivalence claim was false

The claim inherited from the previous handoff was that 3.0.2 reads the existing 2.0
proofs unchanged and agrees with 2.2.2 on all of this project's proofs *including which
mutations it rejects*. Run over all 14 models and all 84 mutation lanes (6 mutations x
14 proofs), there was **one disagreement**: `ne_conflict_sat`, accepted by 2.2.2 and
rejected by 3.0.2, plus a second, dependent one on the same instance's `drop-line` lane.

It was our proof that was under-specified, not the checker that was wrong.
`conclusion SAT : <assignment>` carries the order literals of the *model* variables
only; the `.opb` also carries the `_neN` selector of PROOF-FORMAT section 3 and the
solver has no value for it. 2.2.2 unit-propagates the inline assignment and fills the
selector in — which `encoding.ml` recorded as "checked against veripb 2.2.2, not
assumed", and it was, for 2.2.2. 3.0.2 says in as many words that "the solution given
for the conclusion is not propagated", reads the unmentioned selector as false, and
finds row A falsified. `ne_conflict_sat` is the only model whose answer needs that
selector *true*.

Fixed by logging the solution with `sol` and concluding with the bare `conclusion SAT`,
which is what PROOF-FORMAT already claimed we did. A *logged* solution is propagated by
both. `solx` is not an alternative: 3.0.2 refuses it outside a preserved set. After the
fix: 14/14 models and 84/84 lanes agree, zero disagreements.

**The lesson is not "3.0.2 is stricter".** It is that "checked against veripb" names a
build, and a fact about one build of a checker is not a fact about the format. Nine
places in this tree each decided for themselves which build that was.

### Speed

Per test executable, same binaries, same proofs:

| | Rust 3.0.2 | Python 2.2.2 |
|---|---|---|
| `test_prop` | 137 ms | 3011 ms |
| `test_random` | 420 ms | 10719 ms |
| `test_trace` | 847 ms | 24262 ms |
| `test_endtoend` | 67 ms | 1167 ms |
| 14 model proofs | 109 ms | 2344 ms |

17x to 29x per invocation. Whole-suite **wall** time does not move (31.8s vs 32.0s),
because dune runs the executables in parallel and `test_matrix.exe` alone takes 28-31s
and resolves its own checker. Suite CPU time does move: 28s user vs 72s user. The
headline number is real and currently invisible on the clock; said here rather than
implied.

### Decision

1. The checker of record is the Rust VeriPB **3.0.2**. Selection lives in exactly two
   places — `scripts/checker.sh` and `lib/proof/checker.ml` — and `$PATH` is consulted
   last. A missing checker FAILS; it does not skip.
2. The proof format is VeriPB **3.0**. `BAGUETTE_PROOF_FORMAT` selects it;
   see "what is not yet done" for why the default is still 2.0 at the time of writing.

### 3.0 is not a dialect of 2.0

Measured rule by rule against 3.0.2. Flipping only the version line makes every one of
this project's proofs a **syntax error**.

- Every rule is terminated by `;`. `f 4` becomes `f 4 ;`, and so do `output`,
  `conclusion` and `end pseudo-Boolean proof`. `rup` already ended in one and must not
  get a second.
- Comments are `%`. `*` is rejected outright ("Expected a top level rule name").
- `red`'s witness follows a `:`, *before* the terminator: `red <c> : <w> ;`. Written
  after a `;` it is silently not a witness and the checker says "A witness must be
  specified for the red-rule".
- `delc` drops its `id` keyword; `del` and `core` keep theirs.
- The short forms `u`, `p`, `d`, `v`, `o` are gone.
- `solx` requires a preserved set. `obju` requires explicit subproofs ("Proofgoal #1
  could not be autoproven"). Neither is reachable from M1; both will meet M5.
- **`#` and `w` do not exist.** See D-0024.
- veripb 2.2.2 rejects a 3.0 proof outright ("Unsupported version"), so the switch
  cannot be made one consumer at a time. This is asserted by a test, not assumed.

### Labels, and what they actually bought

The stated prize was that 3.0 labels would remove the "`=` counts as two constraints"
id-numbering trap of PROOF-FORMAT section 2, one of two traps flagged as silently
corrupting. Measured:

- A constraint in the `.opb` **can** carry a label — `@c1 +1 x +1 y >= 1 ;` — and a
  proof can cite it: `pol @c1 @c2 +`, `del id @c1`, `del range @c1 @c7`,
  `conclusion UNSAT : @c13`. Every one of those was run.
- Citing a label that was never assigned is a hard parse error naming the label
  ("The label `@NOPE` is not assigned to a constraint ID"). It cannot silently be a
  different constraint. **That is the trap, gone.**
- A label on an `=` row is refused by the OPB parser ("Expected inequality
  constraint"), because one name cannot stand for the two constraints an `=` splits
  into. The checker now enforces the discipline `Encoding.add_constraint` imposed by
  raising `Equality_in_opb`.

So: yes, with two qualifications that must be said plainly.

- **A label is not a group.** Binding a name twice rebinds it to the newer constraint;
  it does not name both. `del id @L` then deletes one. Labels are therefore *not* a
  replacement for the level stack, which is why D-0024 exists as a separate problem.
- **The `f` count was never the silent half of the trap.** Both checkers reject a wrong
  `f N` outright and name the right number ("The formula contains 3 constraints, but the
  rule expected that there are 2"), measured on both. What was silent was the
  consequence *inside* `Encoding` — an id counter that had drifted, producing a `pol`
  that cited a real but wrong constraint. That is the half labels remove.

### Consequences

- The proof text grows about 19% on the current models (4540 -> 5409 bytes over all 14
  proofs); the `.opb` about 5%. Terminators, labels and D-0024's explicit deletions.
- `Writer` now carries `t.tags`, a mirror of checker state that 2.0 did not need
  (invariant I-X3 gains a second thing to keep exact).
- We inherit the Rust checker's error messages, which name the failing line and column.
  We lose `--proofGraph` and `--toAnnotatedRUP`, which nothing here used.
- `scripts/mutate_proof.sh` parses 2.0 syntax — `# N` for level tracking, and the short
  rule forms. It must be taught 3.0 before the mutation gate means anything about a 3.0
  proof.

### What is NOT done, and why the default is still 2.0

3.0 emission is implemented, and every one of the 14 models emits a 3.0 proof that
3.0.2 accepts, with `BAGUETTE_PROOF_AUDIT=1` and stdout unchanged:
`BAGUETTE_PROOF_FORMAT=3.0 ./scripts/run_model_tests.sh` is 14 passed, 0 failed.
`test_proof.ml` checks the full 3.0 vocabulary end to end, including two negative
controls (3.0.2 must REJECT a corrupted 3.0 proof; 2.2.2 must reject a 3.0 proof).

The default is 2.0 because flipping it leaves **58 unit checks red**, 43 of them in a
file this session does not own. Measured by running every test executable with
`BAGUETTE_PROOF_FORMAT=3.0`. It was 80 before the format-agnostic fixes listed in the
right-hand column:

| executable | failures | why |
|---|---|---|
| `test_matrix` | 43 | resolves its own checker (`~/.local/bin`, which cannot read 3.0 at all) and greps proofs for `# 1` to detect a decision level. **Owned by another session** — not touched |
| `test_justify` | 4 | pins emitted 2.0 line text |
| `test_prop` | 4 | pins emitted 2.0 line text |
| `test_endtoend` | 4 | greps for `# 1` |
| `test_proof` | 2 | pins the unlabelled `.opb` and the `f` line |
| `test_random` | 1 | greps for `# 1` |
| `test_mutation` | **0** (was 11) | `mutate_proof.sh` taught both grammars: an optional `@label` before the rule name, `% level N` as well as `# N`, and `del range` expansion when working out which ids are already dead |
| `test_trace` | **0** (was 11) | label-aware `mints_id`, a standalone-check wrapper in the proof's own format, and a backtrack test that accepts the explicit deletion 3.0 uses in place of `w` |

None of these is a proof being wrong. Every one is a test that pins 2.0 *text*, which
is a correct thing for those tests to do and exactly why they have to be changed
deliberately rather than deleted. The `# 1` greps are the ones to be careful with:
under 3.0 they become vacuously true or vacuously false depending on their polarity,
and a test that silently stops testing is the failure mode this project keeps finding.
They need the `% level 1` marker, not removal. `test_mutation` and `test_trace` show
what that looks like; the two `not (contains "# 1" ...)` assertions in `test_matrix`
are the dangerous ones, because they go vacuously TRUE.

One thing the fix to `mutate_proof.sh` exposed, worth knowing before reading a green
lane: under 3.0 the `drop-line` mutation also un-defines the deleted step's label, so
any later rule citing it is a *parse* error. The lane then holds for a reason that has
nothing to do with the derivation — it holds on `chain_sat`, where under 2.0 it
correctly reported the instance as wrong for that lane. Noted in the script.

Flipping the default is a single change to `Writer.format_from_env`'s fallback plus
those six files. It is not attempted here because `test_matrix.ml` is held by another
session and 43 of the 58 are in it.

## D-0024  VeriPB 3.0 deletes the level stack, so the writer keeps the tags
Status: DECIDED — **IN FORCE, and explicitly kept by D-0046.** Its account of what `w l` did is what `Writer.wipe_level` exists to imitate; the 2.0 half of the record is the specification of the function that survives, not a description of a dead format.
Date: 2026-09-15
Supersedes the mechanism of D-0008, not its intent.

Context: D-0008 chose proof levels over per-reason deletion for backtracking: `# l`
tags everything derived afterwards, `w l` wipes level `l` and above in one rule, one
proof line per backtrack instead of one per reason. VeriPB 3.0 **has neither rule**.
`#` there introduces a proofgoal id and `# 1` is a parse error; `w` is only the
weakening operator inside a `pol`. Measured, not inferred from a changelog.

Labels do not fill the gap: a label names one constraint and rebinding it moves the
name rather than adding to a set (D-0023).

Decision: `Writer` keeps the tags itself. `t.tags` maps each live derived id to the
level it was derived at — always, not only under the audit, because it is no longer
optional once the checker has stopped holding it. `set_level` records the level and
emits a `% level l` comment where the rule used to be. `wipe_level l` computes exactly
the set `w l` would have retired, deletes it, and drops it from the table. Consecutive
ids are compressed into `del range`, so a backtrack is usually still one line.

The set has to be "every id tagged at level >= l", not "every id derived since the
level was set". Those differ the moment a level is re-entered after a spell at a lower
one, which is precisely what search does: `# 1`, `# 0`, prune at the root, `# 1`, prune
under the decision, backtrack. The root prunings must survive. `test_v3_levels` is that
case and exists for that reason.

Consequences:
- D-0008's asymptotic argument is weakened, and this is the real cost of 3.0 for this
  project. "One line per backtrack" is now "one line per *run* of consecutive retired
  ids". Runs are the common case — ids are handed out in order — but not guaranteed,
  and a level whose constraints interleave with deletions costs a line per run. On the
  current models the effect is invisible; on a search deep enough for D-0008's argument
  to have mattered it is not measured, and should be before M2's conflict analysis
  lands.
- The writer now mirrors a piece of checker state that the checker no longer keeps.
  Invariant I-X3 covers it, and a bug there is a wrong deletion, which the checker
  catches ("Trying to access constraint with ID N that has already been deleted") —
  loudly, which is the one comfort here.
- `del range` tolerates an already-deleted id and a reversed range; `del id` does not.
  Both measured. That is why deletion removes ids from `t.tags`.

---

## D-0025  The 3.0 default is on, and what the test flip actually cost
Status: DECIDED — **SUPERSEDED by D-0046 (2026-09-18)**, which removed the dual-format arrangement this record set up: there is no default to flip any more, because there is one format. **HISTORICAL, and kept deliberately:** what the flip cost, and the five silently-vacuous tests it exposed, are the evidence for how this project tests a format change at all.
Date: 2026-09-15
Completes D-0023. Task M1-T19.

Context: D-0023 decided 3.0 and built the emission, but left the default at 2.0 because
flipping it turned 58 unit checks red and 43 of those were in a file another session
held. This entry records the flip and what was found doing it.

**The flip itself is one line** — `Writer.format_from_env`'s fallback. Everything else
was tests that pinned 2.0 *text*. Not one of them was a proof being wrong, which is the
outcome D-0023 predicted and the reason the flip was safe to do in one go.

### The failures were of three kinds, and only one was interesting

1. **Level markers** (`test_matrix`, `test_endtoend`, `test_random`). 2.0 has the
   SetLevel rule `# l`; 3.0 deleted it (D-0024) and `Writer.set_level` leaves
   `% level l`. Tests grepped for `# 1`.
2. **Labels and terminators** (`test_prop`, `test_justify`, `test_proof`). 3.0
   introduces every derived constraint as `@cN rule ... ;`. Tests pinned the 2.0
   spelling of an unchanged rule body.
3. **`test_matrix`'s private checker lookup**, which preferred `~/.local/bin` — the
   Python 2.2.2, which cannot read a 3.0 proof at all. 43 of the 55 failures.

### The dangerous kind, and the rule that comes out of it

Two of `test_matrix`'s assertions had the form `not (contains "# 1" proof)` — "this
model is refuted at the root, so no decision level is ever opened". Under 3.0 the
string `# 1` does not occur **whatever the proof says**, so both assertions go
**vacuously true**. They would not have failed. They would have stopped testing, and
the suite would have stayed green while two root-refutation claims went unchecked.

**Rule: a test that reads emitted proof text must go through the module that wrote it.**
`Writer` now exports `level_marker`, `level_of_line`, `opens_level`, `strip_label` and
`rule_body`, and the tests use those instead of spelling a format out. The spelling then
lives in exactly one place, and the next format change breaks compilation or fails a
test rather than quietly emptying one. This is the same fix, and the same reasoning, as
D-0023's collapse of nine private `veripb` lookups into `Checker.find` — a project-wide
fact had been copied into many files, and the copies could not all be right at once.

Stripping a label is not a weakening. What those assertions check is what a rule
**says**; the label is its *name*, which 2.0 does not have and which the checker already
verifies far more strictly than a string compare could — citing a name that was never
bound is a parse error, which is precisely the id-drift trap D-0023 bought labels for.

### Measured after the flip

- **925 unit checks, 0 failures, under BOTH formats.** The 2.0 fallback is not
  decorative: it is exercised in full, so it cannot rot.
- 15/15 model tests pass; `test/models/PENDING` still empty.
- 194 matrix, 18 mutation, 11 random checks.
- Default emission is 3.0 and `scripts/checker.sh` resolves `~/.cargo/bin/veripb` 3.0.2.
- `BAGUETTE_PROOF_FORMAT=2.0` still emits 2.0 and veripb 2.2.2 still accepts it.

### The speed claim, corrected again

D-0023 reported 17–29x per checker invocation but no change in suite wall time, because
`test_matrix` ignored `$VERIPB` and took 28–31s of a 32s run. With that file on the
shared resolver, **`test_matrix` alone went from ~30s to 1.2s**. The per-invocation
speedup was always real; it was one file's private lookup that hid it from the clock.

## D-0026  D-0003 resolved: reasons are data, justifications are cutting planes
Status: DECIDED
Date: 2026-09-16
Resolves: D-0003. Arose from the GCS comparison, `docs/GCS-COMPARISON.md`.

Context: D-0003 asked which reading of "explanations of higher order" is this project's
contribution — (a) a richer explanation *language* (PB, cutting planes, parameterised
reasons), or (b) explanations as first-class deferred *computations* that compose. It has
now blocked concrete work three times: D-0009, D-0011 and M3-T2.

The comparison against the Glasgow Constraint Solver supplied the missing evidence.

- GCS answered (b), and answered it **against the shape our `Deferred` assumes**. Their
  old closure-valued reasons "look lazy but are not — the domain walk, the fill and the
  allocation all happen eagerly at the call site", measured at ~20% of runtime. What
  replaced it is not a richer closure: a reason is *declarative data* naming a variable
  scope, materialised into literals in exactly one place.
- Nothing in GCS reads (a) as a contribution. They call a `pol` builder inline and get
  the same proofs. Our `Combine`/`Weaken`/`Model_row` (D-0015) is already further down
  the (a) road than GCS ever went.

Decision: **(a) and (b) are layered, not alternatives.**

- **(b) is the mechanism, and we adopt the mature form.** A *reason* — which facts
  justify this pruning — becomes declarative data over a variable scope, materialised
  into `Lit.t`s in one place. It is not a thunk graph. Laziness lives in *when* the
  reason is materialised, not in a closure per pruning.
- **(a) is the claim.** A *justification* — how the checker is convinced — stays the
  reified cutting-planes expression: `Combine` with a divisor, `Weaken`, `Model_row`, and
  `Term (coeff, t)` recursing into another justification. An explanation taking
  explanations as arguments is the higher-order content, and it is what D-0016's "what
  `pol` can and cannot reach", D-0004's `all_different` question and D-0012's branch
  nogoods are all actually about.

Reasoning, recorded because D-0003 asked for the reasoning and not just the verdict: the
two readings answer different questions about the same pruning. For `2x + 3y <= 10` with
`y >= 2` deriving `x <= 2`, the *reason* is the fact `y >= 2`; the *justification* is
"add 3 times that fact to the row, then divide by 2". Our code already builds both — as
`facts ()` and as `expl`, from one `row_snaps` call in `linear.ml` — and keeps them in
agreement with a comment rather than a type. The layering makes the split the type it
already is in practice.

Consequences:

- `Explanation.t` loses the reason-shaped constructors and keeps the derivation. A new
  `Reason.t` carries the literal content. `Store`'s `~facts` thunk and `Trace`'s literal
  list are that type in disguise today.
- **I-P4 and I-P5 collapse into one obligation.** `int_ne` violated I-P5 from M1-T9 to
  M1-T17; under one channel that is a type error rather than a code-review miss.
- `linear.ml` loses `find_lo_reason`/`find_hi_reason`, which call `Store.trail_entries`
  — allocating the whole trail — once per term per pruning. See the performance claim
  below, which is the condition this decision was accepted under.
- **Only non-narrowable reasons.** GCS's `Narrowable*` variants re-materialise against
  whatever narrower state is current later. That is the exact opposite of I-X6, which
  `explain_cross_conflict` violated until M1-T13 and which I-X6 itself warns conflict
  analysis will not forgive. A reason materialised later must render the derivation as of
  the moment of the pruning.
- D-0003's own framing said the rest of the explanation design follows from this. What
  follows: M2-T3's conflict analysis walks the trail and reads *variables* from a reason
  without materialising literals; M3's reification dispatcher becomes possible because a
  verdict can carry reason and justification as values; M4's Hall-interval reason is one
  declarative value rather than a hand-built `Combine` plus a hand-built facts list.

Accepted under a stated condition, with its falsifier named:

> The layering must not cost speed and must make the code easier.

"Easier" is already checkable: `linear.ml` sheds roughly 120 of its 421 lines and one
invariant becomes a type. "Not slower" is a **prediction, not a measurement** — the
change deletes an `O(n * |trail|)` scan per pruning and adds only a type split, so it
should be faster, but nothing here has been benchmarked. This project has been wrong
about speed twice already (D-0023, and "The speed claim, corrected again" in D-0025), so
the prediction is recorded as falsifiable: **M3-T5 measures it, and if the layered form
is slower on a real model, that reopens this record rather than being absorbed.**

What this decision does NOT do: it does not remove D-0013's arithmetic, which becomes the
justification half unchanged; it does not adopt GCS's second inference tracker, since we
have no proofs-off mode by rule; and it does not settle how a reason is *restated* for
wide domains, which is the interval question D-0010 and the order-encoding width policy
own.

## D-0027  D-0011 is a rule about naming rows, not about counting them
Status: DECIDED
Date: 2026-09-16
Amends: D-0011, which D-0026 left pointing here. Task M2-T0.
Prerequisite for M4-T1 (`docs/GCS-COMPARISON.md` §2.2 and §3, "Propagation").

Context: D-0011 decided "**one propagator instance justifies against exactly one model
row**". Read literally, that sentence forbids M4-T1 before it is written: a Hall-interval
justification cites one recovered at-most-one line per Hall *value* and one at-least-one
line per Hall *variable* (`docs/GCS-COMPARISON.md` §3), which is many model rows from one
propagator instance. D-0026's round added a forward pointer saying D-0015 had closed the
ADT gap D-0011 rests on, and deliberately left the *policy* open. This record closes it.

D-0011's reasoning has two halves, and only one of them was about the ADT.

- The **ADT half**. `Trivial` carries no payload, so *which* row it means comes from the
  single ambient `ctx.model_id`; the trail records no propagator identity; therefore a
  caller walking the trail cannot recover which half of a fused equality produced a
  pruning, and `Trivial` is unresolvable. That half is closed, and by a record that says
  so verbatim: D-0015 "supersedes the ADT gaps recorded in D-0009, D-0010 and D-0011",
  and its `Model_row id` names a row *in the value*, so one `Combine` can hold an
  explanation this instance built and one another instance built against a different row.
- The **decomposition half**. An equality posts as two `Linear` instances rather than one
  fused propagator, because the engine already runs propagators to a fixpoint and wakes
  them on the variables that changed, so the fused loop's internal alternation duplicates
  the engine's own job; and because a routing hazard every future caller must get right is
  worse than queue churn. Nothing in D-0015 touches that argument, and nothing here does
  either.

And a third thing, which is what actually settles the question: **the literal reading is
already false of shipped, verified output, and was false long before M4 was contemplated.**
Measured in this worktree at this commit, `test/models/lin_unsat.fzn` (two `int_lin_le`
constraints, hence two rows and two instances), whose proof the 15/15 model suite has
veripb accept:

```
@c9  ... >= 7 ;      * row of int_lin_le(coeffs, [x,y], 3)      -- instance A
@c10 ... >= 8 ;      * row of int_lin_le(neg_coeffs, [x,y], -8) -- instance B
@c11 pol @c9 y_ge_1 y_ge_2 + ... + ;
@c12 pol @c9 x_ge_1 x_ge_2 + ... + ;
@c13 pol @c10 @c11 + @c12 + ;
```

`@c13` is one `Combine`, built by instance B, citing B's own row **and**, through `@c11`
and `@c12` — which `linear.ml`'s `Snap_cite` path took off the trail — instance A's row.
One derivation, two model rows, two instances, in a proof this project has shipped since
M1-T12. So D-0027 is not a permission being granted. It is a description of what M1
already does, arrived at exactly the way D-0015 predicted it would be.

Decision: restate D-0011 as the rule it has always operationally been.

1. **Anchoring stands, and it is about naming.** Every explanation must name the
   constraints it rests on, explicitly, in the value: `Model_row id` for a model row,
   `Term (c, e)` for another explanation. What D-0011 forbade, and what stays forbidden,
   is an explanation whose row is resolved from *ambient context* while more than one row
   is in play — that is the unresolvable `Trivial`, and it is a real hazard, not a
   historical one (see the consequences).
2. **Citation is unrestricted.** A derivation may cite any number of model rows and any
   number of other instances' explanations. Multi-row derivations are permitted, and
   M4-T1's Hall-interval justification is writable under this record with no further
   decision needed.
3. **Instance-per-row is the default for constraints that decompose, not a law.** Where a
   constraint's rows propagate independently and the engine's fixpoint reproduces the
   fused loop — `int_lin_eq`, `int_le`, `int_lt`, `int_eq` — post one instance per row, as
   D-0011 said. Where the inference is *not* per row, and a global constraint's is not,
   one instance owns several rows. `all_different`'s Hall argument cannot be split into
   per-row propagators without destroying the propagation, and splitting it was never what
   D-0011 was arguing about.
4. **This does not re-fuse `int_lin_eq`.** D-0011's cost argument survives untouched, and
   `docs/GCS-COMPARISON.md` §2.2 makes the same call: what D-0015 dissolved is D-0011's
   *stated reason*, not automatically its *policy*. A session that wants the fused
   equality back needs a new record and a measurement, not this one.

Consequences:

- **The residual `Trivial` hazard is concrete and should be closed before a multi-row
  propagator lands.** Read off the code (not observed in emitted output, for the reason
  below): `search.ml:323,338` pushes a decision with `Explanation.trivial`;
  `linear.ml`'s `find_lo_reason`/`find_hi_reason` will happily return that entry's
  explanation, `summand_of_snap` wraps it as `Term (|a|, Trivial)`, and `Justify.emit`
  renders `Trivial` as `ctx.model_id ()` — the ambient row, which is *not* what
  established that bound. That is D-0011's ambiguity, alive in the one place D-0015 did
  not reach. It is unreachable today only because a `Combine` is emitted **only** at a
  root conflict: `search.ml`'s under-decision arm writes the trace and the nogood and
  never emits the derivation (measured: `offset_unsat`, which branches and refutes both
  children at every level, contains 31 `rup` lines and 0 `pol`). The moment D-0018
  point 2's per-push `pol` path is used — M4 is the first thing that will need it — the
  hazard is live.
- The cheap closure is to stop having an ambient row at all: every propagator passes its
  `row_id`, `Linear.make`'s `?row_id` stops being optional, and `Justify.emit`'s
  `Trivial -> ctx.model_id ()` arm goes. Then D-0011's hazard is a type error rather than
  a convention, which is the same move D-0015 made for `Weaken`. Not done here — this
  record is doc-only — and it is proposed to the roadmap rather than taken.
- **M2-T7 is not a prerequisite for M4-T1, and that is a change from D-0011's own
  reading.** D-0011 said the trail's missing propagator identity must be fixed before
  M2-T3; that still holds for clause learning, which needs to know *who* inferred a
  bound. A multi-row justification does not: if every explanation names its own rows,
  trail-walking needs no propagator identity to resolve them. The two problems were the
  same problem only while `Trivial` was the only way to name a row.
- What is still **not** permitted, stated so that a later reader does not have to
  re-derive it: an explanation that leaves its row ambiguous (point 1); a derivation that
  finds the id it cites by searching proof state at emit time instead of naming an id
  snapshotted at pruning time (I-X6, and D-0018's `snapshot_source` argument); and a
  fused propagator that reaches a joint internal fixpoint over several rows and then
  cannot say which row produced a given trail entry (point 3's "decompose where it
  decomposes" is exactly this, and the trail still records no propagator identity).
- Asserted, not measured: that `all_different`'s Hall inference cannot be decomposed into
  one propagator per row. That is a claim about the constraint, taken from GCS's
  implementation and from the structure of the Hall argument, and nothing here tried it.
  If someone finds a per-row decomposition that propagates as strongly, point 3's default
  applies to `all_different` too and no harm is done.

## D-0028  A justification's size is proportional to declared domain width
Status: DECIDED
Date: 2026-09-16
Task M1-T27. Records a cost D-0010 creates, D-0005 does not cover, and M1-T25 does not
fix. No code changed; the interval restatement is M4 work.

Context: D-0010 requires a bound fact to be stated in the same currency as the model row
it combines with — the order encoding's own expansion — which makes it a *chain* of
order literals rather than one literal. `docs/GCS-COMPARISON.md` flagged the consequence
("every bounds-consistency path must be independent of domain width", and reason-side
width is the subtler hazard) and the roadmap row names `order_reason.ml:38-43`.

Reading the code first changed what this record says, twice.

**1. The lines the roadmap names are not on the live path.** `order_reason.ml:38-43` is
`lower_bound_terms`; with `upper_bound_terms` it builds the declared-to-current chain
that *asserts* a fact. Neither has a caller anywhere in `lib/` — only
`test/unit/test_prop.ml`. Nothing in `lib/` constructs `Explanation.Linear` or `Cut` any
more either; the census of explanation constructors used in `lib/` is `combine` x2 and
`weaken` x1 in `linear.ml`, `trivial` x1 there, and `clause` in `ne.ml` and `search.ml`.

**2. What does reach a proof is worse than the roadmap's description.** The live chain is
`Order_reason.weaken_declared`, and it spans the variable's **whole declared width**, not
the prefix between the declared and current bound. Its own header says why: there is
nothing "current" about a weakening chain, it is valid regardless of what the variable
turns out to be, which is the point of using it instead of a fact. So the size is
Θ(declared width) *per other term of the row, per pruning, no matter how small the
pruning* — and, as the measurement below shows, even when no pruning has happened at all.

Measured here, in this worktree, against VeriPB 3.0.2. The model is two variables
declared `0..w` and one row `a + b = 5w/2`, which is infeasible on the declared bounds
alone, so the solver refutes it at the root having pruned **nothing**:

| w | `.opb` | `.pbp` | axiom literals in the one `pol` line | solve | verify |
|---|---|---|---|---|---|
| 9 | 984 B | 303 B | 18 | — | — |
| 99 | 11.5 kB | 2.29 kB | 198 | — | — |
| 999 | 126 kB | 23.9 kB | 1 998 | — | 42 ms |
| 9 999 | 1.36 MB | 258 kB | 19 998 | — | 130 ms |
| 99 999 | 14.6 MB | 2.78 MB | 199 998 | 4 s | 1.3 s |
| 999 999 | 156 MB | 29.8 MB | 1 999 998 | 72 s | 12 s |

The whole `.pbp` is six lines at every width; one of them is 29.8 MB at the bottom row.
veripb verifies every one of them — `s VERIFIED UNSATISFIABLE`, including the 30 MB line.
So the roadmap's "a variable declared `0..1000000` carries million-literal reasons" is no
longer a prediction: it is two million literals, in a single line, for a two-variable
model that is infeasible by inspection, and the checker accepts it. **The failure mode is
not rejection. It is a correct proof that nobody can store, read or review.**

Three things the measurement separates, which the roadmap row runs together.

- **Reasons are already width-independent; justifications are not.** Under D-0026's split,
  `linear.ml`'s `facts_of_snaps` — the reason — is one literal per *cited term*, and
  D-0018's trace lines are O(terms). The width lives entirely in the `Weaken` chains
  inside a `Combine`, which is the justification. M2-T8 therefore does **not** fix this,
  and the roadmap's title for this row names the half that is cheap.
- **The width is inherited from the encoding, not invented by `order_reason.ml`.** The
  model row *is* the order encoding's expansion, Θ(w) literals per variable
  (`Encoding.expand_int_lin_le`), and an axiom chain that cancels a variable's
  contribution to that row cannot be shorter than the row's own literals for that
  variable. No rewrite confined to the reason layer can shorten it.
- **Today the cost is paid on exactly one path.** A `Combine` is emitted only at a root
  conflict: `search.ml`'s under-decision arm writes the trace and the nogood and never
  emits the derivation. Measured: `offset_unsat`, which branches and refutes both children
  at every level, contains 31 `rup` lines and **0** `pol`. D-0018 point 2 reserves a
  per-bound-push `pol` at a scratch level for prunings that are not plain RUP over the
  row; nothing exercises it yet, and M4's Hall intervals are the first thing that will.
  When they do, this cost is multiplied by the number of prunings.

Decision: three parts.

1. **The project accepts width-proportional justifications, and does not weaken them to
   escape.** A propagator may not narrow a domain without justifying it (`CLAUDE.md`'s
   standing rule, I-P4), so D-0005's remedy — decline the work, stay sound, propagate
   more weakly — is structurally *unavailable* on the proof side. The only sound options
   are to refuse the model or to make the justification cheaper. M1 does neither, and
   that is stated here rather than left to be discovered by whoever first points the
   solver at a wide domain.
2. **A width policy belongs to the encoding, and to SPEC, not to the reason layer.**
   M1-T25 (lazy ladder atoms) addresses the `.opb` half of the same root cause and its
   roadmap row already says it does not fix this. The coupling runs the other way too and
   is easy to miss: `Order_reason.weaken_declared` and `Encoding.expand_int_lin_le`
   perform the same substitution and, in that module's own words, "the two must agree on
   the constant or the pieces don't combine". **If M1-T25 changes the row's shape, the
   weakening chain must change in the same commit.** Neither row may be done alone.
3. **There is no cap today, and D-0005's is not one.** D-0005 caps hole punching above
   2^20 *values* and says bound movements are never affected — true, and exactly why it
   does not cover this: this cost is paid by bound movements only, and it is already
   unpleasant at w = 10^4, two orders of magnitude below D-0005's threshold. If a cap is
   wanted, it belongs where M1-T23 caps declared domains for overflow — one check at
   compile time — and refusing a model the FlatZinc standard allows is a SPEC change that
   needs its own record. Not taken here.

What a future interval restatement must preserve. D-0010's chain requirement is
load-bearing *for the checker*, so a cheaper reason still has to convince it:

- **Currency.** D-0010's arithmetic is not a convention, it is what the checker computes:
  an order literal is 0/1, so `a * x_ge_b` tops out at `a`, never `a * b`. Whatever stands
  in for the chain must still cancel the variable's contribution to the row *exactly*,
  which means it arrives with a derived line relating it to the chain sum. A shorter
  statement that does not cancel leaves a residue and the `pol` does not close.
- **Declared offsets.** Measured against the declared bound, never the raw value — the
  constant lives on the row's right-hand side (D-0010's central mistake, twice found).
- **Citation by id (D-0009).** A bare literal in a `pol` is the trivial axiom `lit >= 0`.
  An interval atom is usable only if some line establishes it *and* the derivation can
  name that line: that is M2-T9's literal to defining-line index, and it is why GCS pins
  boundary atoms to persistent top-level lines.
- **I-X6.** The restated reason must still render the derivation as of the moment of the
  pruning, not as of the moment it is forced.
- **I-X2.** An atom minted mid-proof by `red` must be retired exactly once before
  `conclusion`; D-0019's last consequence already records that `ensure_direct` has no
  retirement path.
- **Both axes, measured.** GCS measured a 5.9x smaller proof that took 3.5x *longer* to
  check at an identical search tree. M3-T5 is the instrument; a restatement that shortens
  the file and lengthens verification has not obviously won.

Consequences:

- **Nothing in the gate can see this.** The widest declared domain in `test/models/` is
  `var 0..9`; the whole suite runs at w <= 9, where the chain is nine literals and
  invisible. That is this project's signature failure mode in its purest form — the
  instances chosen cannot watch the thing break. The shape that does is recorded above
  and is cheap: two variables, one row, infeasible on the declared bounds, zero prunings,
  w around 10^3. Adding it is a `test/models/` change, which this record does not make.
- A neighbouring cost, measured in passing and explicitly **not** covered here: on a
  *satisfiable* wide model (`a + b = w+1`, `b - a = 1`, `var 0..999`) the proof is 1.7 MB
  with **no `pol` at all** — 5 495 lines whose largest is a 6.4 kB nogood carrying ~500
  decision literals, because `indomain_min` descends one value at a time and search depth
  is therefore Θ(w). That is a branching-strategy cost, not a reason cost, and no interval
  restatement touches it. It is recorded so that a future measurement of "proof size
  versus domain width" does not attribute it to this record's problem.
- `Order_reason.lower_bound_terms`/`upper_bound_terms` and `Explanation.Linear`/`Cut` have
  no producer in `lib/` (census above). They are D-0010's *fact* chain, which D-0026's
  `Reason.t` is about to take over. This record deletes nothing and asks that whoever does
  M2-T8 decide their fate deliberately, rather than find them unreferenced and assume they
  were always dead.
- **Asserted rather than measured**, and named so it can be falsified: the claim that the
  chain cannot be shortened without changing the row. It is an argument from the
  encoding's shape, not an experiment. What would falsify it is a hand-written proof that
  cancels a variable's contribution to an `expand_int_lin_le` row using fewer than `w`
  axioms and that veripb accepts. Nobody has tried it, and this project has been wrong
  about a proof-layer "cannot" three times already (D-0009's `pol`, D-0012's nogood,
  D-0019's direct encoding), each time corrected by someone running the checker instead
  of arguing.

## D-0029  An arithmetic limit, enforced at compile time, and why declining to prune is not an option
Status: DECIDED
Date: 2026-09-16
Task M1-T23. Closes the only soundness gap the GCS comparison found. Adds a normative
paragraph to SPEC 2.1, which is why this record exists.

Context: nothing in `lib/` checked for integer overflow. OCaml's native `int` is 63 bits
and wraps silently.

**The gap, reproduced by the orchestrator before this record was written** (not taken from
the implementing session's report):

    array [1..1] of int: c = [-2305843009213693952];   % -2^61
    var 3..4: x;
    constraint int_lin_le(c, [x], 0);
    constraint int_le(x, 3);

`x = 3` satisfies this: `-2^61 * 3 <= 0`. baguette printed `=====UNSATISFIABLE=====` and
exited 0. The emitted row was

    @c1 +2305843009213693952 x_ge_4 >= 2305843009213693952 ;

— a row that *forces* `x = 4`, where the true row is vacuously true on `3..4`, because
`Encoding.linear_terms_int_lin_le` folded `-2^61 * 3` and it wrapped to `+2^61`. With
`x <= 3` that model really is unsatisfiable, so veripb 3.0.2 answered
`s VERIFIED UNSATISFIABLE`. A wrong answer shipped with a proof the checker accepts.

**Why this class is different from an ordinary bug.** The usual safety net is that the
proof disagrees with the solver. Here it cannot: the propagator and the `.opb` expansion
compute the same products with the same wrapping `*`, so they agree *because* they are
both wrong. I-S1's independent oracle does not catch it either, since
`Model.check_assignment` evaluates the sum with the same operators; and on an UNSAT answer
there is no assignment for it to check at all. The failure is invisible from inside.

Decision, three parts:

**1. Overflow raises; it never wraps and never silently declines.** `lib/core/checked.ml`
raises `Checked.Overflow` from every operation where a coefficient meets a bound. The
tempting alternative — detect the overflow and decline to prune — is sound for a
propagator in isolation and **not sound here**, because by the time any propagator runs,
the `.opb` row for that constraint has already been written from the same arithmetic.
There is no "decline" available for an artefact that must exist. Declining would leave a
corrupted file on disk and say nothing. This is the asymmetry that makes proof logging
different from plain solving, and it is why D-0005's "decline the work, stay sound"
remedy does not transfer.

**2. A compile-time cap, so the raise is a backstop rather than the mechanism.**
`Compile` checks every declared bound and every posted row against
`Checked.limit = max_int / 16`, and rejects with a positioned diagnostic and exit 3. The
factor of 16 is derived, not chosen: the worst path is the `.opb` A/B pair for an
`int_lin_ne`, which bounds everything by `9M + 6`, and 16 leaves a margin. The derivation
is in `checked.ml`'s header and is asserted as a test, so raising the limit turns the
suite red.

**3. The cap is about overflow. It is NOT a width cap, and does not become one.** It
permits a declared width of 5.7 x 10^17, thirteen orders of magnitude above where D-0028
measures proof size becoming unusable. The two questions are deliberately kept apart: an
overflow cap refuses models whose *arithmetic* cannot be computed, while a width cap would
refuse models whose *proof* is too large to store — a different justification, a different
bound, and its own SPEC change. D-0028 nominates this same check as where a width cap
would live; that remains open and is not decided here.

Consequences, recorded so they are not rediscovered:

- **`lib/proof/encoding.ml` and `lib/proof/opb.ml` still compute unchecked** and now rely
  entirely on `Compile`'s cap. The invariant is "Compile is the only door", and nothing
  states or enforces it. A second entry point — a future front end, or a test calling
  `Encoding.add_int_lin_le` directly — can still write a corrupted row. Filed as M1-T32.
- **`Model.check_assignment` shares the failure mode** with the propagator it is supposed
  to check independently. Under the cap it cannot overflow, but an oracle that wraps the
  way its subject wraps is not independent, and I-S1's value rests on that independence.
  Filed as M1-T33.
- `ceildiv` no longer routes through `-(floordiv (-a) b)`; that negation has no answer at
  `min_int`, i.e. it was a second wrap on the very path this record is about.

## D-0030  A mutation lane must judge a derivation, not a grammar -- and `root_unsat` cannot
Status: DECIDED — **IN FORCE.** Its rule is format-independent and is the one M2-T14 applied. Its 2026-09-18 amendment, comparing how `drop-line` fails under each format, is **HISTORICAL** as of D-0046: one format remains, and under it dropping a line is always a parse error. The rule itself is untouched.
Date: 2026-09-16
Task M1-T26. Extends D-0020. Adds no constraint on propagators; it constrains what the
mutation harness is allowed to count as a passing lane.

Context: D-0020 built the harness on the principle that a lane is worthless unless the
corrupted proof is rejected *for the reason the lane is about*. M1-T26 audited every lane
by reading veripb's actual message rather than its exit code, and found two distinct ways
a lane can be green while testing nothing.

**1. `drop-line` rejects on the grammar, in BOTH formats.** Deleting a derivation step
un-defines its label, so a later citation fails to parse: under 3.0 the message is
"The label `@c3` is not assigned to a constraint ID", under 2.0 it is "Accessing the
database out of bound with index 3". The roadmap's M1-T26 row and D-0023 describe this as a
**3.0 quirk**; it is not, and that is corrected here. (**Correction, 2026-09-16:** this
record originally also named `docs/PROOF-FORMAT.md` §5 as carrying the claim. It did not —
`drop-line` appeared nowhere in that file until M1-T25 added the corrected statement. The
error was the orchestrator's, found by agent-lazy2 when it went looking for a sentence
that was never there.) The knob is
unfixable in text: a step is deleted precisely because something later cites it.

The fix is not to delete the lane -- that is the same failure mode in a new costume. It
is re-registered as `Unevaluated`, still run, still asserted to reject on the grammar, so
the day it starts judging a derivation the suite says so. Its derivation coverage is
carried by a new `Truncate_derivation` knob on the same step, which keeps the leftmost
operand so the step still **binds its label** and the checker must judge the inference.

**2. `root_unsat` is not a valid test instance for load-bearingness, and the orchestrator
confirmed this independently.** Its `.opb` is two rows:

    @c1 +1 ~x_ge_3 +1 x_ge_2 >= 1 ;
    @c2 +1 ~x_ge_2 +1 ~x_ge_3 >= 3 ;

`@c2` asks two coefficient-1 literals to sum to 3. It is **infeasible on its own**, so the
model is refuted by a single row and every derivation above it is decoration. Verified by
hand, outside the harness: a proof containing no derivation whatsoever --

    pseudo-Boolean proof version 3.0
    f 2 ;
    output NONE ;
    conclusion UNSAT : @c2 ;
    end pseudo-Boolean proof ;

-- returns `s VERIFIED UNSATISFIABLE`. So `root_unsat/truncate-derivation` is ACCEPTED,
and its sibling `pol-coeff`/`pol-cite` lanes reject only because `conclusion UNSAT : @c3`
names `@c3` by hint and the corruption makes *that* row non-contradicting. That is a
strictly weaker claim than "the derivation was load-bearing", which is how those lanes
have been read.

The instance was chosen because its margin is one. A margin of one in the *derivation*
does not help when a *model row* is independently contradictory.

Decision:

- A lane that is rejected without the checker ever judging an inference is **not a pass**.
  The harness classifies this explicitly (script exit code 5) from a listed set of
  checker messages, rather than treating any non-zero exit as success.
- A control lane is **mandatory and unskippable**. It is enforced twice: the script
  refuses to report on an instance whose clean proof does not verify, and the test makes
  it a type error -- a lane takes a `controlled` token that only the control gate
  produces. A lane without a control is not an expression the test file can write. When a
  control fails, every declared lane fails **by name**; "waiting" lanes are gone.
- Mutation knobs live in the emitter as typed corruptions of the `Pol.t` AST, not as text
  edits. Text mutation must re-derive from the output what the emitter already knew, and
  that is where M1-T22's `del range` off-by-one lived.
- A knob must be structurally incapable of firing in a normal run. `Writer`'s mutation
  field is immutable, `create` cannot set it, `create_mutated` reads **no** environment
  variable (deliberately unlike `audit` and `format`), nothing in `lib/` or `bin/` names
  it and a test greps the tree to keep it that way, and every corrupted proof carries a
  `% DELIBERATELY CORRUPTED PROOF` banner.
- `root_unsat`'s accepted lane is registered as `Known_slack` in D-0020's existing
  mechanism -- reported every run, red if it ever starts rejecting -- and **not** weakened
  away. Replacing it with an instance whose model rows are each individually satisfiable
  is M1-T38.

This is the ninth time in this project that the instance chosen to test a property could
not observe that property failing. The recurring shape is worth naming: **a test is not
evidence until something has been seen to break it.** The eight earlier instances are in
D-0020, D-0023, D-0025, M1-T16, M1-T17, M1-T20, M1-T24 and M3-T5.

### Amendment, 2026-09-18: under format 2.0 `drop-line` *can* judge a derivation, because ids are positional

D-0030 concluded that `drop-line` fails on the **grammar in both formats** and recorded the
two messages as the measurement. That is true of the line it measured. It is **not** true in
general under 2.0, and M2-T14 surfaced the difference by running the mutation harness under
`BAGUETTE_PROOF_FORMAT=2.0` with the Python 2.2.2 checker — a configuration nothing had
exercised, because the gate runs 3.0 only.

The reason is structural. Under **3.0** a constraint id is a **label** (`@c3`), so deleting
the line that defines it leaves every later citation naming a label that was never assigned
— a parse error, always, whichever line you drop. Under **2.0** ids are **positional**, so
deleting a line **renumbers** everything after it. The citations still resolve; they just
resolve to *different* constraints. The checker therefore reads a well-formed proof and
judges an inference — and rejects it on the derivation.

Measured on two instances, `triple_unsat` and `lin_unsat`, both dropping line 5 (a `pol`):
under 2.0 veripb answers **rejected-on-the-derivation**, where the lane is registered
`Unevaluated` (rejecting without judging).

**What this does not change.** D-0030's rule stands untouched and is the reason the
discrepancy was visible at all: *a lane rejected without the checker ever judging an
inference is not a pass.* The harness reports the mismatch as a **failure** rather than
silently re-registering the lane, and its message says so in as many words — "the lane has
found something: say what, do not re-register it to match". That is the behaviour to keep.

**What it opens, and is deliberately NOT decided here.** Whether a lane's `expect` should be
**format-dependent** — `Unevaluated` under 3.0 and evaluated under 2.0 for the same knob on
the same instance. Arguments exist both ways: a per-format expectation is honest about what
each checker does, but it doubles the registration surface and makes a lane's meaning depend
on an environment variable, which is how this class of bug arose in the first place. Recorded
as **M2-T15**. Until it is decided, a 2.0 run of `test_mutation` has **two expected failures**
and they are findings, not regressions.

## D-0031  The order encoding's ladder stays in the `.opb`: lazy by `red` is quadratic
Status: DECIDED
Date: 2026-09-16
Task M1-T25. **Answers a roadmap row rather than implementing it.** No code changed; the
`.opb` and every emitted proof are byte-for-byte what they were. Companion to D-0028,
which owns the justification half of the same root cause.

Context: `Encoding.declare_int` writes `hi - lo - 1` consistency clauses -- the "ladder",
`x_ge_(v+1) -> x_ge_v` -- into the `.opb` for every declared variable, eagerly and
uncapped. M1-T25 proposed to defer them: the `.opb` carries the bounds and a rung enters
the proof by `red` "only when something cites them", following `Encoding.ensure_direct`,
which is already that pattern for the *direct* encoding. The motivation is real:
`width_root_unsat` emits a 126 kB `.opb` of which 76 kB is ladder, and M1-T23's arithmetic
cap permits a declared width of 5.7 x 10^17.

Reading the code first supported the row, and measuring it overturned it.

**1. Nothing cites a rung, and the ladder is load-bearing anyway.** `Encoding.consistency_id`
has no caller in `lib/` or `bin/` at all, and `derive_at_most_one`, the one function in
`lib/` that reads the id table, is itself called only from `test/unit/test_proof.ml`. So
"only when something cites them" would have deferred every rung of every variable for ever.

That reading is wrong, because the demand is not citation -- it is the **checker's own unit
propagation**, which is invisible at the emission site. A model row is the order encoding's
expansion, in which every literal of one variable carries the *same* coefficient, so the row
constrains only *how many* of `x`'s literals hold. Nothing but the ladder ties "`x_ge_k`
holds" to "at least `k - l` of them hold", and without that a D-0018 trace line is not RUP.

Measured, not argued: strip every ladder row from each shipped model's `.opb` and re-run
3.0.2 -- **13 of 20 still accepted, 7 rejected** (`chain_sat`, `guess_wrong_sat`,
`ne_conflict_sat`, `near_limit_ne_sat`, `near_limit_unsat`, `offset_unsat`,
`width_sat_depth`), and in all seven the **first** line to fail is the first trace line.
The orchestrator reproduced this independently on two models before this record was
written: `chain_sat` fails RUP with the ladder stripped, `lin_sat` still verifies.

The split is "does this run's proof contain a RUP check that needs a count" -- a property
of the *run*, not of the model text, and therefore **not knowable when the `.opb` is
written**, because the `.opb` is complete and closed before the first propagation (I-X5).

**2. A rung can be introduced mid-proof, and the obvious witness is wrong.** Both measured:

- **Swap** (`x_ge_v -> x_ge_(v+1)  x_ge_(v+1) -> x_ge_v`) is the natural witness, since a
  row counts literals and swapping two leaves every row invariant. Accepted for a
  variable's *first* rung, refused for its second: "Proofgoal 2 could not be autoproven."
  The goal it fails on is the neighbouring rung's image, which is genuinely **false**, so no
  explicit subproof rescues it. On real models: 5 of 6 rejected.
- **Rotation** works: introduce rungs in increasing `v`, cycling the already-laddered prefix
  down by one. Every existing rung's image is the rung below it, and the bottom rung's image
  is satisfied by the negated claim. Accepted on all 8 models tried.

**3. The rotation is Theta(w^2) against the `.opb`'s Theta(w).** On `width_sat_depth`
(w = 99, a model whose ladder *is* used): today 16 153 B `.opb` + 29 859 B `.pbp` = 46 012 B;
lazy 9 237 B + 221 525 B = 230 762 B. **Five times larger for the same search tree and the
same answer.** That is a committed model, so shipping the lazy default would have shipped a
regression.

Where deferral *does* pay is the case where the ladder is never used. D-0028's shape, with
the eager loop skipped by a throwaway local patch:

| w | `.opb` eager -> lazy | solve RSS kB | verify RSS kB |
|---|---|---|---|
| 999 | 125 941 -> 49 623 | 9 080 -> 8 068 | 18 624 -> 16 480 |
| 9 999 | 1 359 943 -> 535 627 | 33 164 -> 22 264 | 43 272 -> 36 964 |
| 49 999 | 7 199 944 -> 2 855 630 | 139 688 -> 86 332 | 125 136 -> 75 856 |

Consistently -60% `.opb`, -38% solver RSS, -39% checker RSS, about 2x on both timings. A
**constant factor, not an asymptotic one**: the `.opb` stays Theta(w) because the row itself
is (D-0028, "the width is inherited from the encoding"). The roadmap's framing --
"`var 0..1000000: x` is a million-row `.opb`" -- is true and incomplete; removing the ladder
leaves a 2.9 MB `.opb` at w = 5 x 10^4, not a small one.

Decision, three parts:

1. **The ladder stays in the `.opb`, for every declared variable, and that is now normative**
   (SPEC 4.2). It is stated there rather than left in `declare_int` because the reason is
   invisible from the emission side: no rule cites a rung, so the next person to read the
   census will reach for the same deletion.
2. **"Lazy by `red`" is rejected as a default, and the recipe is kept.** It is a bet that the
   ladder will not be used, paid for by a quadratic if it is, and the bet cannot be settled
   when the `.opb` is written. A width threshold does not rescue it: eager costs ~38w bytes
   and lazy-if-used ~4.5w^2, so the crossover is w ~ 8, two orders of magnitude below where
   the eager cost is worth attacking. The rotation witness is recorded in PROOF-FORMAT 3
   anyway, because it is a measured fact about the checker that cost a session to establish.
3. **Nothing about the row's shape changed, so D-0028's coupling is untouched.**
   `lib/proof/encoding.ml` and `lib/core/prop/order_reason.ml` are byte-identical to their
   state before M1-T25 started. Recorded so the next attempt knows those two files move
   together or not at all -- a shipped M1-T25 would also have shifted every model row's id
   and `@cN` label, which is the half of that coupling easiest to miss.

Consequences:

- **The ordering hazard.** A rotation witness permutes a variable's literals, and a *trace
  line* mentioning them is not invariant under that permutation. So a lazy ladder can only be
  materialised while the database is still just the `.opb` rows -- i.e. "on demand" can only
  ever mean "all variables, at the first demand". A per-variable scheme materialised after
  the first trace line is not merely costlier, it is **rejected**.
- **The same is true of the direct encoding, and today it is latent.** `ensure_direct`
  channels `x_eq_v` to `x_ge_v`, likewise not permutation-invariant, and `derive_at_most_one`
  cites rungs by id. Nothing in `lib/` reaches either yet; M4 will.
- **What would reopen this.** A witness for a rung that is O(1) in the declared width and
  that the checker accepts against a database already holding the neighbouring rungs. The
  argument above says the cascade is forced, but that is an argument, not an experiment, and
  this project has been wrong about a proof-layer "cannot" three times (D-0009's `pol`,
  D-0012's nogood, D-0019's direct encoding) -- each time corrected by someone running the
  checker instead of reasoning. The swap-versus-rotation measurement is where a fourth
  attempt should start.

## D-0032  A test scene must not hold its facts as model rows
Status: DECIDED
Date: 2026-09-16
Task M2-T1/M2-T2. Sibling to D-0030 and D-0016. A rule about how a proof-checking test is
built, not about any propagator.

Context: M2-T1/M2-T2's break-it pass deleted the facts from `bool2int`'s justification, so
that a reason claimed its bound **unconditionally** -- a plainly broken justification. It
**passed all 332 unit checks and all 28 models.**

The cause was in the test file, not in `lib/`. `bool_clause_scene` and `bool2int_scene`
established their setup bounds as `.opb` **model rows**, copying the shape of the existing
integer builders. A model row is part of the formula the checker is handed, so the model
itself entails the claim, and a reason with no facts at all is still *true*. veripb accepts
it, correctly. The test was asking "is this reason valid?" when the property that matters
is "is this reason valid **because of the facts it cites**?".

This is D-0009's "restating a constraint is trivially valid" and D-0016's valid-but-useless
generalisation arriving together, in a new place. It is the **tenth** instance of this
project's signature failure mode, and the first found by a deliberate break rather than by
a later session tripping over it.

Decision:

- **A test scene establishes its facts in the store, never as `.opb` model rows.** That is
  also the faithful arrangement: in a real run a bound comes from a decision or from another
  propagator, and neither is a model row. A scene that posts its setup as rows is testing a
  different thing from the one the solver does.
- **Every propagator's justification test needs a factless control** -- a `rup` that claims
  the bound citing nothing -- which the checker must **reject**. Without it, the test cannot
  distinguish a justification that works from a model that makes any justification work.
  M2-T1/M2-T2 adds two such controls; they are meaningless under the old scenes and
  load-bearing under the new ones.
- **A break-it pass is part of delivering a propagator, not an optional extra.** Thirteen
  breaks were run here; four of them (a clause that checks but never unit-propagates, and
  `bool2int` missing either direction) are **completely invisible to the model suite** --
  the search recovers the same answer by branching and the output is byte-identical. Only
  direct push assertions see them. Conversely, corrupting the *trace facts* is invisible to
  the unit tests and caught only by models, because trace lines are written during a real
  search. Neither layer alone is sufficient, and that is now measured rather than asserted.

Known and deliberately not fixed here: `test_prop.ml`'s **integer** veripb builders
(`build_int_lin_eq_multi`, `build_int_le_multi`, `build_int_lt_multi`, `build_int_eq_multi`
and the `int_ne` builders) have the same construction. Whether it actually weakens them
depends on each row's shape and **has not been measured**; a blind edit would be a guess.
That is M1-T42.

## D-0033  Division rounds toward zero as a relation and outward as a bound; dividing by zero is unsatisfiable, not an error

**Status**: accepted, 2026-09-16. **Decides**: SPEC §2.1 "Integer division, modulo and
absolute value". **Unblocks**: M4-T4b, which the roadmap gated on exactly these two
additions. **Context**: M4-T4a (`lib/core/interval.ml`) is on master and already carries a
header warning about the first half of this.

### The two questions

M4-T4b cannot start without answers to these, because both decide which assignments are
answers, and an implementation that guesses differently is wrong rather than merely
different.

**1. Which way does `int_div` round?** Toward zero, with the remainder taking the
dividend's sign. `-7 div 2 = -3`. This is MiniZinc's choice and GCS's, and the cost of
disagreeing with it is that our answers to a standard FlatZinc file differ from every
other solver's, silently.

**2. What happens when the divisor can be zero?** Nothing special: it is unsatisfiable,
not an error. The value 0 has no support in the divisor's domain, so it is pruned with a
justification like any other value, and a model whose only solutions need it is UNSAT with
a proof.

The alternative — rejecting the model, or aborting the search on `y = 0` — is worse than
it looks. It is not a safety measure; it is a refusal to answer a question that has a
perfectly good answer, and it converts a provable UNSAT into an unproved error exit. The
whole point of this solver is that "no solutions" is a claim we can *prove*. An error exit
proves nothing, and a checker cannot audit it.

### The trap this decision exists to prevent

These two roundings are different, they disagree only on negative operands, and in our
codebase they will live a few functions apart:

- The **relation** truncates toward zero. It answers "is `(x, y, q)` a solution?"
- A **bound** rounds outward — floor below, ceiling above. It answers "what is the widest
  range this constraint permits?"

`Interval.div_floor` and `Interval.div_ceil` are the second kind and are *not* the first.
Using the relation's rounding to compute a bound prunes values that have support: with
`x` in `1..10` and `2x <= -3`, the largest admissible `x` is `floor(-3/2) = -2`, while
truncation answers `-1` and silently drops a supported value.

This is a pruning that cannot justify itself — the `.opb` row permits what the propagator
removed — so it is the shape of bug that this project treats as a soundness bug rather
than a precision bug, even though "it only rounds the wrong way" sounds cosmetic.

Note the asymmetry with D-0029. There, propagator and `.opb` wrapped *identically*, so the
checker agreed with a wrong answer. Here they would disagree, so the checker would catch
it — which makes this the *less* dangerous of the two failures, and the reason it is
recorded as a trap to be tested for rather than as an open soundness gap. M4-T4b must
include a test that watches the wrong rounding produce a rejected proof, not merely a test
that the right rounding produces an accepted one.

### What this does not decide

Whether `quotient_filter` should be made exact. M4-T4a measured it as inexact in 40 of
4095 small cases (~1%), inherited from JaCoP via GCS. Tightening it is a different and
larger algorithm; M4-T4b decides whether it wants one, and the suite prints the gap so
that the decision is made against a number rather than an impression.

## D-0034  A wake trigger is a property of what a propagator READS, not of what it promises

**Status**: accepted, 2026-09-16. **Decides** the question M2-T5 put to the orchestrator
explicitly: derive the wake mask from `Propagator.consistency`, or amend the glossary so
that `Bounds` means "reads only bounds"?

**Neither, as stated. The trigger becomes its own declaration on `Propagator.instance`.**

### Why not the glossary amendment

`docs/GLOSSARY.md` defines "bounds consistent" as a promise about a propagator's *output*:
what it will and will not prune. The mask needs a statement about its *input*: which parts
of a domain it reads. Those are different properties of different ends of the same
function, and they coincide today only as a matter of fact.

M2-T5 checked that fact by reading every propagator in the tree rather than assuming it —
`linear.ml` and its four re-exports, `bool2int.ml`, `bool_clause.ml`, `ne.ml` — and all of
them do line up. But an audit is not a theorem, and this one expires silently the moment
someone writes a `Bounds` propagator that reads a hole. Redefining the glossary term to
make the audit true by fiat would give one word two jobs, and the failure it permits is
invisible: the propagator is simply never woken, prunes less, and the proof still verifies
because everything derived was derived correctly.

This project has been bitten by exactly this shape before — two things that must agree,
with no mechanism keeping them in agreement, is how D-0009 started.

### What the evidence actually says

The mask is worth **nothing measurable today**: M2-T5 instrumented the classifier and
found `masked = 0` on all 29 models, across 970 propagator runs and 1210 wakes. Not one
`Domain.Holes` change occurs in the whole suite, because `int_ne` is the only propagator
that removes a value and in these models that value always sits at a bound, where `settle`
turns it into a bound move.

And the suite cannot see the mask being wrong. With `Domain` consistency deliberately
starved of hole wakes, **all 29 models pass** — orchestrator reproduced this directly:
29 passed, 0 failed, with only the new unit scenes going red (4 FAIL). So the mask's
entire value and its entire risk lie in the future, and its only present instrument is the
`BAGUETTE_DEBUG` I-P2 re-run check that shipped alongside it.

### The decision

1. The derived default (`trigger_of_consistency`) **stays for now**, because it is correct
   for every propagator in the tree and that has been checked by reading them.
2. It is a **stopgap with an expiry condition**, and the condition is the arrival of the
   first propagator whose input set and output promise differ — in practice `all_different`
   or `element` in M4. At that point the trigger becomes a field on `Propagator.instance`,
   supplied by the author, and `trigger_of_consistency` is deleted rather than extended.
3. Until then, **`BAGUETTE_DEBUG` is the net and must stay cheap enough to leave on** in
   development. It has no coverage on the 6 models that conflict at the root, because
   `propagate` never returns a fixpoint there; that gap is recorded, not closed.

The alternative of flipping the default to `wake_on_any` — sound by construction, and a
one-line change — was considered and rejected: it would leave the machinery in the tree
with nothing exercising it outside the unit scenes, and an unexercised mechanism is how
this project's signature failure mode starts. The mask is exercised, the audit is written
down, and the expiry condition is named.

## D-0035  An explanation must justify the bound as RECORDED, not the bound the propagator asked for

**Status**: accepted, 2026-09-16. **Arose from** M1-T44, a correct UNSAT answer whose proof
the checker rejected. **Records a premise that was load-bearing and had never been written
down.**

`Domain.set_lo` does not stop where the propagator asks. It re-establishes I-D2 by
**settling** — walking the new bound past any hole it lands on. So a trail entry's recorded
`lo` can be strictly *stronger* than the bound its own explanation derives, and the
difference is exactly the holes the settle walked over.

`linear.ml` cited such an entry as the reason for the entry's **recorded** bound. The
premise "the cited entry's explanation establishes the entry's bound" is false for precisely
these entries, and it appeared nowhere in the documentation. The hole's own `Clause` reason
was therefore cited nowhere in the proof, and the chain fell **exactly one unit short** —
`0 >= 0` where a contradiction was claimed.

**The rule, stated once so it is not rediscovered**: a reason list that cites a trail entry
must justify the entry's bound *as recorded*. Where a settle strengthened that bound, the
reasons of the holes it walked over are part of the justification and must be cited with it.

Two things worth keeping about how this was diagnosed:

- **The rival diagnosis was refuted rather than argued down.** "The derivation is fine, the
  route is wrong" would have been fixed by re-routing the conclusion. It is wrong because
  the three rows the chain cites are **jointly satisfiable** at `v0 = v1 = 0`: no ordering
  or discriminator over that set of rows could ever produce a contradiction. The route was
  wrong *as a consequence* of the derivation being wrong.
- **The tempting narrow fix was correctly declined.** Discriminating on "is this chain
  `0 >= k` with `k >= 1`" would route this instance correctly while leaving the explanation
  still lying about what the bound rests on — and `Explanation.lits` feeds M2-T3 conflict
  analysis, where a learned clause built from a reason set that omits the disequality would
  be **unsound**. Testing the symptom would have bought a green suite and a worse bug later.

The fix needed no new rule: a hole's reason is a `Clause`, so `Search.rests_on_a_clause`
answers "yes" and D-0022's existing path closes the conflict over the trace. D-0022 reaching
a case it previously could not see, not a new mechanism.

**Scope, measured**: 59 of 60 model artefacts byte-identical; only the new model's proof
differs. Post-fix sweep of ~111,600 solver runs across 62 seeds, zero rejections, with the
two known reproducers (seeds 133, 151) shown to *fail* with the fix reverted — so the sweep
is a demonstrated detector rather than a silent pass.

## D-0036  A dependency that cannot be inverted in `lib/` can still be pinned from `test/`

**Status**: accepted, 2026-09-16. **Arose from** M1-T32: `lib/proof/encoding.ml` must not
commit a row whose arithmetic wrapped (I-X8), but `Encoding` cannot name
`Baguette_core.Checked` — `lib/proof` does not depend on `lib/core`, and inverting that is
not on the table.

Three routes were considered and two rejected for reasons worth keeping:

- **Move `Checked`'s primitives into `lib/proof` and have core re-export them.** Rejected
  because `Checked` is not only arithmetic: it carries `limit`, `row_fits`, `bound_fits`
  and the derivation of the factor 16 — that is FlatZinc **compile-time policy**, which
  does not belong in the PB emitter. Splitting the module would separate the operations
  from the envelope argument whose entire value is being in one place.
- **A type only a validated constructor can build.** Rejected because it changes
  `add_int_lin_le`'s signature, which a standing cross-session request forbids, and more
  substantively because it only *relocates* the check: the type would be defined in
  `lib/proof` and constructed in the front end, which already has `Checked`.
- **Accepted**: a local `Arith` in `encoding.ml` — an unavoidable copy — **pinned by a
  test that asserts it agrees with `Checked` operation by operation**, over a table that
  straddles `mul`'s fast-path boundary.

The general point, which is the reason this is a decision record and not a comment:

> **The test layer depends on both libraries although neither depends on the other.** That
> is what makes a duplication *checkable* rather than a second source of truth.

A copy nobody compares is two implementations drifting. A copy with an equivalence test is
one implementation with a redundant encoding, and the test fails the moment they disagree —
which is exactly what a break confirmed: widening `Arith.mul`'s fast path reddened the
equivalence pin *and* two behavioural checks.

**Only the arithmetic half is copied.** `Checked`'s policy half — the limit and the
envelope — is not, and must not be: the emitter has no business deciding which models the
front end accepts.

**Why implement rather than document.** D-0031 is the precedent for answering a question
without implementing it, because implementing measured worse (Θ(w²), 5× on a committed
model). Here implementing costs ~60 lines, fires on nothing the CLI accepts, and changes
no emitted byte — all 87 artefacts byte-identical. D-0029's asymmetry decides the rest:
there is no "decline" available for an artefact that must exist, and that applies with more
force to the module that *writes* the artefact than to the propagators, where it was
already accepted. A documented-only invariant would have left the hole the roadmap row
names — `test_matrix.ml` calls `Encoding` directly — genuinely open.

## D-0037  A decision is an assumption, not the model row: `Trivial` is deleted and the ambient row becomes unrepresentable

**Status**: accepted, 2026-09-16. **Required by** `CLAUDE.md` ("do not add a constructor
without a decision record"). **Delivers** M1-T31 and M1-T50, which could only go out
together — the `?row_id` fallback *is* `Trivial`, and removing it breaks every test file's
compile in the same commit that removes it.

### The change

`Explanation.Trivial` is **deleted**. A decision now carries `Explanation.Decision of Lit.t`.
`Justify.ctx` loses `model_id` and `for_constraint` entirely; `Linear.make`'s `?row_id`
(and `Lin_eq`/`Int_eq`'s `?le_id`/`?ge_id`) are **required**.

### Why this is a mislabel, not a rendering bug

M1-T50 observed `linear.ml` emitting `pol <own row> <own row> +` — deriving twice the
propagator's own row where the fact belonged. The mechanism was `Trivial -> ctx.model_id ()`.

The root cause is that `Trivial` means "the model constraint itself justifies this", and
that sentence is **false of a decision**. A decision is an assumption the search made, not
a consequence of any row. Once the reason says so honestly, the rest follows without
invention:

- A decision **has no constraint id and structurally cannot**. D-0009 already settles it: a
  `pol` cannot assert a literal, a `rup` cannot derive a non-consequence, and `search.ml`
  never logs a decision as a constraint. So it is not citable, ever.
- `linear.ml` gains a third snapshot branch, `Snap_assume`: the term is **weakened** out of
  the row with the declared-width axiom chain (sound whatever the variable turns out to be),
  while its bound literal is **still** contributed to the D-0018 trace line. The two
  projections diverge deliberately — it renders like `Snap_weaken` into the `pol` and like
  `Snap_cite` into the facts. Dropping the fact would make the trace line an unconditional
  claim, which is exactly the I-P5 failure `int_ne` shipped between M1-T9 and M1-T17.
- `Explanation.term` and `cut` **refuse** a `Decision` where the citation is built, rather
  than leaving `Justify` to discover it.

**Effect on `Explanation.lits`, which D-0035 says becomes soundness once M2-T3 lands:**
strictly improved. `Trivial`'s `lits` was `[]` — so a reason set resting on a decision named
**no dependency at all**, precisely the omission D-0035 warns of. `Decision lit` gives
`[lit]`, and `Snap_assume`'s weaken chain spans the declared width and therefore contains
the decision's own literal. The `lits` of a decision-sourced `Combine` is a superset of what
it was, never a subset.

### On "a type error, not a raise" — what was and was not achieved

**The ambient row is genuinely unrepresentable.** `Justify.ctx` has no field to hold one,
`create` takes two arguments, and no constructor means "the current row". That is a
type-level change; it reddened ~30 call sites across 10 files, and `bin/main.ml`'s failing
`model_id` thunk is deleted because there is nothing left to guard.

**`Justify.emit` on a `Decision` still raises, and that is stated rather than dressed up.**
The fully type-level form needs two types — a trail `reason` and an emittable `derivation` —
and all three routes to it leave the task's file set: `Store.outcome`'s
`Conflict of Explanation.t` forces the split through `store.ml`, `engine.ml` and
`propagator.ml`, with ~74 test call sites needing an explicit wrap; a `private` abbreviation
needs the same 74 coercions; and `emit : … -> cid option` pushes a spurious `None` onto
every honest caller. What was done instead is to move the refusal to *construction* and make
`linear.ml` discriminate structurally, so nothing builds one. Strictly better than a silent
**wrong** `pol`, but it is a raise. The type-level version is a real task, not a tidy-up.

### The blind spot this exposed, which is the most useful part

Pushing the **wrong** decision literal (`lit` instead of `Lit.negate lit` in `explore_le`)
left the entire suite **green**: 30 models, every unit binary. Nothing read the literal —
the `pol` weakens the term away without it and the trace fact is computed from the store.
`test_matrix.ml` now walks the trail on every propagation and checks, at each
`Store.is_level_start` entry, that the reason is `Decision l`, that `l` names the variable
that moved in the direction it moved, and that the bound **as recorded** entails `l` — with
`>=`/`<=` rather than `=`, because a settle can strengthen it (I-X9). The same break now
reddens 13 matrix checks. Matrix checks 239 → 252.

**Artefact delta: zero of 30 models change, all 90 hashes identical** — the predicted
result, since a `Combine` is emitted only at a root conflict where no decision is in force.

## D-0038  Should an `Explanation` carry the bound it concludes, so a `pol` can be checked against it?

**Status**: **RESOLVED by D-0043** (2026-09-17) — was OPEN, raised out of M1-T51. **Blocks** the
adoption of `Writer.pol_concluding`, which exists and is demonstrated but has no caller in
`lib/`. Interacts with **D-0003** (still open) and with **D-0026**'s propagator interface v2
(M2-T8). Not to be decided in passing: it touches `lib/core/explanation.ml`, the central ADT
every propagator depends on, and `CLAUDE.md` forbids a new constructor there without a record.

### What M1-T51 established, and why that is not enough

`pol` writes a derivation and nothing else. Its conclusion is whatever the reverse-Polish
expression evaluates to, so a `pol` that computes something strictly **weaker** than the
bound the propagator then pruned to is a *sound proof line under an unsound prune*, and the
checker has nothing to object to. Measured, on the production writer with the existing
`Truncate_derivation` knob: a `pol` truncated to derive a disjunction instead of a bound is
**accepted** by 3.0.2 bare, and **rejected** once the conclusion is stated as an `ia`. The
old guards did not catch it — they are regexes over emitted text and never run against a
corrupted writer at all. This is why M1-T42 could only reach 8 of its 9 cells.

So the *rule* was never the obstacle. `ia` was there all along, in both checkers (see
PROOF-FORMAT §2a, which was silent on it until M1-T51 and is now corrected). **The obstacle
is that the claim does not exist to pass.** `Explanation.Combine of summand list * int` and
`Cut of t * t * int * int` record how a bound was derived and not what was derived, so
`Justify.emit_cut` and `emit_combine` have no conclusion in hand at the moment they call the
writer.

### The routes, and what each costs

1. **`Explanation` gains the conclusion.** Most direct, and it makes the mismatch a type
   error at construction rather than a checker rejection. But it widens the hotspot ADT, and
   D-0003 is open and expected to reshape it — doing this first risks doing it twice.
2. **Propagators supply the claim at the emission site.** Leaves `explanation.ml` alone.
   But it puts the conclusion *beside* the explanation rather than in it, so nothing forces
   the two to agree — which is most of the property we wanted.
3. **Fold it into M2-T8's interface v2**, where D-0026 already separates a declarative
   `Reason` from a `Justification`. The conclusion is naturally the `Reason`'s business.
   Costs the most delay; is the only route that does not pre-empt a decision already queued.
4. **Adopt `ia` only where the claim happens to be available**, and say where it is not.
   Partial by construction, and a control with holes in it invites the assumption that it
   has none.

### What is NOT in question

- **The hint is mandatory.** An unhinted `ia` searches the whole database, so it can pass on
  an order-encoding ladder clause rather than on the derivation above it. `Writer.implied`
  requires the hint and PROOF-FORMAT §2a now records that a *misplaced* hint fails **open**
  and silently — `ia C ; @NOPE` verifies clean, because after the `;` a label belongs to the
  next rule.
- **The cost is not the reason to hesitate.** Projected adoption everywhere: `width_sat_depth`
  +0 lines (it emits no `pol` at all), `width_root_unsat` 1 -> +2, whole suite +20 lines
  (+2%). `pol` is rare here because D-0009 routes `int_lin_le` through `rup`.
- **The coverage that exists today is real but narrow.** The suite emits only ~10 `pol` lines
  across the model set, all on small unsat instances where the `pol` feeds the cited
  contradiction. It says nothing about a pruning the conflict never cites, which is what
  dominates any real search — and that is precisely the case M2-T3's clause learning creates.

## D-0039  A trace line is RUP in sequence, not standalone: the individual-derivability property is retired

**Status**: accepted, 2026-09-17. **Forced by** M1-T56 and M1-T57 landing together.
**Corrects** `docs/PROOF-FORMAT.md` §4, which stated the retired property as normative.
**Adds** invariant **I-S4**. **Read together with** D-0018 and D-0021, whose nogood story
this does *not* change, and with D-0035, whose "justify the bound as RECORDED" is what
forces it.

### What changed, and why it had to

M1-T57's defect was that `Trace.claims` read `e.now` — the **settled** bound — while the
facts on the line came from the propagator. `Domain.settle` walks a bound past holes to
re-establish I-D2, so the recorded bound can be strictly stronger than the one the
propagator asked for, and the line then claimed more than its facts justified. On
`root_hole_unsat` it claimed `v0 >= 1` with an **empty** tail: unconditional, and false.
That is I-P5's worst case, and D-0035 says the explanation must justify the bound as
recorded, so weakening the claim back to the asked bound was not an option.

The fix is for the line to also cite the facts of the holes the settle crossed. Those holes
have lines of their own only because of M1-T56 — which is why the two tasks could not be
split, and why T56 is T57's *prerequisite* rather than its sibling.

### The consequence, stated plainly

A settle line is no longer derivable from the `.opb` alone. Measured on
`test/models/trace_settle_holes_sat.fzn` against 3.0.2: of eight trace lines, six verify
standalone, and **two are refused**. The settle line is accepted the moment its hole line
precedes it. So §4's "a trace line must verify this way (it is decision-free)" is **false**
and is retired.

**This is not a soundness loss.** VeriPB checks each `rup` against the database as it stands
at that line, which is precisely RUP-in-sequence; a proof of this shape is exactly as valid
as before. What is lost is *auditability of a line in isolation*, which had been convenient
and had become an assumption. What is kept is the property the nogood story actually needs:
a trace line mentions **no decision** and is globally valid, so the decisions still appear
only in the nogood and the nogood is still RUP along the trace.

### What this costs, and the part that is not yet checked

1. **Deletion order becomes load-bearing** — I-S4. A cited hole line must outlive the line
   citing it. It does today by the level discipline (a settle at level `l` cites only holes
   at levels `<= l`; `w l` retires levels `>= l`), but that is an argument, not a check, and
   **the argument does not cover M2-T3's learned clauses**, which will cite across levels.
2. **Tests must stop asserting standalone validity universally.** A suite that asserts it
   for every line is asserting something false. `test_trace.ml` asserts the refused count
   per model instead — 0 for models with no settle, 1 for `trace_settle_holes_sat`.
3. **The cited hole run is an over-approximation** — contiguous holes adjacent to the new
   bound, empty exactly when no settle happened. Extra facts only weaken the clause, so it
   costs precision and never soundness. The exact set needs the propagator's *asked* bound
   on `Store.entry`, a new record field; not needed today, and that is the route if
   precision is ever wanted.

### What was rejected

Making the claim the *asked* bound rather than the recorded one. It would restore standalone
validity, and it is what D-0035 exists to forbid: the line would then justify a bound that
is not the one on the trail, and the mismatch is exactly the drift D-0009 cost a round to.

## D-0040  `all_different` does NOT force the direct encoding; it forces an explicit derivation

**Status**: accepted, 2026-09-17. **Establishes** invariant **I-X10**. **Corrects** the
`M1-T60` roadmap row, which I wrote, and the conclusion it invites. **Governs** M4-T1,
M4-T2, M4-T3 and M4-T4b. **Read with** D-0019 (a `rup` target is a clause; point 3 is the
test of when the direct encoding is genuinely forced), D-0027 (cutting-planes
justifications are permitted), and D-0039/I-S4.

### The property, and why it had gone unstated for a milestone

Every trace line this solver emits is RUP against the `.opb` because **every M1 pruning
follows from a single model constraint**, whose rows unit-propagate the claim once the
line's own facts are assumed. That is a property of the propagator set that happens to
exist — not of the order encoding — and it was written down nowhere. It is also why
M2-T11 measured 2051 hole splits with zero rejections, and why M1-T57's *false* trace
line survived ~111k fuzzer runs.

### What I got wrong, and why the error mattered

M1-T60's row said M4's `all_different` ends the property because "a Hall-interval pruning
removes values with no disequality row behind them". **The conclusion is right and the
mechanism is wrong.** Bounds-consistent Hall pruning removes no value: it pushes a bound
out of a saturated interval. That is what makes it *bounds* consistent.

The error is not cosmetic. An invariant phrased about **holes** would have let M4-T1
through silently — the exact failure M1-T60 exists to prevent — because Hall's first
violation is a **bound move**. I-X10 is therefore phrased about *how many model
constraints a pruning rests on*, and says so.

Measured against 3.0.2, on a satisfiable four-variable scene where `x, y, w ∈ 2..4`
saturate `{2,3,4}` and `z ∈ 2..5` (17 rows):

| line asserted against the `.opb` | 3.0.2 |
|---|---|
| `rup +1 z_ge_5 >= 1` — the Hall **bound move** (M4-T1) | **refused** |
| `rup +1 ~z_ge_3 +1 z_ge_4 >= 1` — Régin's **hole** (M4-T2) | **refused** |
| `rup +1 ~z_ge_4 +1 z_ge_5 +1 ~x_ge_4 >= 1` — an `int_ne` line, same `.opb` | **verified** |

and both pruned values are genuinely entailed: restricting `z` to `2..4` is UNSAT, and so
is pinning `z = 3`. These are *true* claims the checker will not take on a `rup`.

### The decision

**M4-T1 does not force the direct encoding.** Hall's reason is a sum of n disequality
rows, and its justification is a cutting-planes derivation, which **D-0027 already permits
outright**. M4-T1's obligation is therefore only to emit that derivation as explicit
`pol` lines *ahead of* its trace line, so the line is RUP in sequence — D-0039's move, one
step further. **No encoding change at all.**

This is stated as its own decision because "`all_different` forces the direct encoding" is
the wrong conclusion to draw from I-X10, and it is precisely the conclusion the roadmap row
invited. Getting it wrong would mean paying for the direct encoding — which is
width-proportional, and D-0028 is the record of what that costs — to buy something a `pol`
already provides.

**M4-T2 and M4-T3 are different and the direct encoding *is* forced for them**, by D-0019
point 3's own test: whether a reason must mention a hole. Régin's reason ("these k values
are covered by these k variables") and `element`'s ("i is one of these indices") both do.
**M4-T4b violates more basically than any of them**: the `.opb` carries no row for a
product, so there is nothing to unit-propagate at any consistency level. (M4-T4a is out of
scope — `interval.ml` is pure arithmetic and prunes nothing.)

### What is argued rather than measured

That **M3's reification preserves** the property: `int_ne_reif` under a true selector should
punch a hole whose clause is the M1 hole clause with `~b_ge_1` appended — structurally the
move `_neN` already makes. I-X10 is phrased to permit a reification literal among the facts.
Untestable today because M3-T1's `red` definitions do not exist; re-check when they do.
M4-T3 and M4-T4b are likewise inferred from M4-T1's and M4-T2's measured shapes.

## D-0041  A declared width limit, because a proof nobody can store is not an answer

**Status**: accepted, 2026-09-17. **Delivers** M1-T54. **Adds a normative paragraph to
SPEC §3.1**, which is why this record exists, and a cross-reference in §2.1. **Supersedes**
the "no such limit exists today, and that is deliberate" of D-0028 part 3 and D-0031 —
that stance reserved this decision pending evidence, and the evidence arrived.

*(Numbered 41 rather than 40: the agent that proposed it and I were both writing a record
on 2026-09-17 and both reached for 40. D-0040 is the `all_different` decision.)*

### The evidence that had been asked for

D-0028 part 3 declined to cap width and said what would change its mind. On 2026-09-16
three memory-ceiling incidents happened in one day, all the same shape: a `test_prop.exe`
run reached **14.9 GB RSS** with zero free and the box swapping and had to be killed by
hand, and two further test binaries were killed at the ceiling afterwards. Each disrupted
the user, not only the session responsible.

Three defences were then built, and all three are the wrong kind. `ulimit -v`, `Mem_guard`
(M1-T53) and `scripts/check_test_widths.sh` either **kill or fail after the allocation is
under way**, or see only the syntactic form of a width in a test file. A refusal at the
declaration is different in kind: nothing is allocated, and the diagnostic can name the
variable and the line.

### The decision, in four parts

1. **The limit is `hi - lo <= 10_000`, per variable, owned by `Encoding.declare_int`.**
   Bracketed by D-0028's own table rather than picked: 10 000 is the last width whose
   artefacts fit in a review (1.36 MB `.opb`, 258 kB `.pbp`, 130 ms verify), and it is an
   order of magnitude below w=99 999, the first row with a multi-second solve and an
   eight-figure `.opb`. It leaves **10×** above `test/models/width_root_unsat.fzn`'s
   deliberate w=999, which is measured, load-bearing, and must keep passing.

2. **Two layers, one constant.** `Encoding.declare_int` raises `Width_too_large` before the
   Hashtbl and before the ladder loop, so a refused declaration allocates nothing and
   leaves no trace. `lib/flatzinc/compile.ml` names that same constant and carries the
   positioned diagnostic and **exit 3**. The constant is **not copied**: `flatzinc` may
   name `proof`, so unlike D-0029's `Arith` there is no excuse for a second statement of
   the envelope. The check is overflow-safe by construction — `min_int..max_int` has width
   2^64−1 and a naive `hi - lo` computes −1 and would *accept* it, so the test never
   subtracts until it has established it may.

3. **No escape hatch, and this is the part most likely to be revisited.** `MEM_CAP_KB` is
   a knob on a test harness's resource limit; this is a **normative acceptance limit**. A
   knob would make the accepted language environment-dependent, so two runs of the same
   binary on the same `.fzn` could disagree about whether it is a legal model — the one
   thing a normative statement must not allow. Three more reasons: exceeding it has no
   partial mode, since D-0028 measured the outcome as a 30 MB proof line that *verifies*,
   so raising the cap hands out the incident; any knob is a guard that can be found
   disabled, and M1-T45's `if true || ...` is this tree's own example; and the legitimate
   need ("my model really is `0..86400`") is not served by a bigger ladder but by a
   different encoding, which M4's intervals are. A knob would let that work be deferred
   indefinitely while users hit the ceiling. **What would change my mind**: a real model
   that needs w > 10 000, is not served by rescaling, and whose proof someone actually
   checks.

4. **It is not `Checked.limit` and does not merge with it**, per D-0029 point 3. Different
   justification (that one refuses models whose arithmetic cannot be *computed* and is a
   soundness requirement; this one refuses models whose proof cannot be *stored*),
   different value (~15 orders apart), and different exit code. Reusing `Unrepresentable`
   was considered and rejected: its arm exits **4** and tells the reader that baguette's
   own invariant failed, which is actively misleading for a legal FlatZinc model. An
   over-wide domain is a model problem and gets exit 3. A test asserts the width message
   does **not** contain "arithmetic limit", so the overflow cap cannot be what fires.

### Consequences, including one filed rather than decided

- **The cap is per variable, so a model's total ladder is still unbounded**: 1 000
  variables at w=9 999 each still blows up. Filed as a roadmap row, not decided here,
  because an aggregate budget has to name a variable to blame for a total that no single
  variable caused, and that is a separate design question.
- `Direct_too_large` / `max_direct_values = 100_000` becomes unreachable under this cap.
  Kept, exactly as D-0029 kept `Encoding`'s arithmetic guard: the door checks its own
  precondition regardless of who is standing in front of it (I-X8).
- `bin/main.ml` gains a `Width_too_large` arm at **exit 4** — the sibling of
  `Unrepresentable`'s, by the same argument, and with no "do not use the proof" warning
  because nothing was written. Verified by injecting the raise, not by reading the code.
- The declared-width lint needed teaching: it matches `~lo:`/`~hi:` labels and cannot tell
  a *predicate* on a width from a *declaration* of one. And ocamlformat and the lint
  disagree about one line — a one-liner with a trailing `(* width-ok: *)` marker passes
  fmt and silently stops being marked, so the function keeps a two-statement body on
  purpose. Both are commented in place.

## D-0042  No aggregate width budget yet — the cost is Θ(total width), and that is not the same as a limit being due

**Status**: **DECLINED**, 2026-09-17, with the evidence that would reverse it stated below.
**Closes** M1-T65, which **D-0041** filed rather than decided. **Deliberately mirrors
D-0028 part 3**, which declined the per-variable cap in this same register and named its
trigger — and was right to, because the trigger arrived on 2026-09-16 and D-0041 is the
result.

### What was measured, and it settles the mechanism

D-0041 capped `hi - lo` **per variable** at 10 000 and filed the obvious gap: 1 000
variables at w=9 999 each still blow up, and the cap does not see it. The question was
whether an aggregate budget is due. Measured on 2026-09-17 against the committed solver,
emitting real artefacts:

| vars | width | total width | `.opb` | bytes per unit of total width |
|---|---|---|---|---|
| 1 | 10 000 | 10 000 | 576 kB | 57.6 |
| 20 | 500 | 10 000 | 421 kB | 42.1 |
| 100 | 100 | 10 000 | 403 kB | 40.3 |
| 1 000 | 10 | 10 000 | 367 kB | 36.7 |
| 2 | 10 000 | 20 000 | 1.01 MB | 50.7 |
| 200 | 500 | 100 000 | 4.43 MB | 44.3 |
| 1 000 | 100 | 100 000 | 4.31 MB | 43.1 |

**The governing quantity is the total, not the maximum.** Four different shapes summing to
10 000 land within 1.6× of each other, and the per-variable cap bounds only one term of the
sum. The residual spread is explained rather than left as noise: bytes per unit rise with
*per-variable* width because the literal names get longer — `x0_ge_9999` costs more than
`x0_ge_9`. So the mechanism D-0041 filed is real and is now quantified at **≈40–58 bytes
of `.opb` per unit of total declared width**.

### Why a limit is nevertheless not due

1. **The artefact stays tractable far past anything plausible.** Total 100 000 is a 4.4 MB
   `.opb`, ~1 s to solve and ~0.3 s for 3.0.2 to verify. D-0028's condemned case — "a proof
   the checker accepts and nobody can store or review" — is 156 MB. The distance between
   them is a factor of 35.
2. **A cap at D-0041's 10 000 would refuse ordinary models.** 1 000 variables declared
   `0..10` is a total of 10 000 and a perfectly normal CP model; it produces a 367 kB `.opb`
   in 142 ms. Refusing that would be plainly wrong, and it is what the naive "reuse the
   per-variable number" answer does. This is the concrete reason not to pick a constant by
   analogy.
3. **Every observed incident was a single wide domain**, and D-0041's per-variable cap
   catches all three. The aggregate gap has produced no incident, and reaching it needs
   deliberate construction: with each variable capped at 10 000, a total of 10^6 requires at
   least 100 variables at the cap. Nobody writes that by accident.
4. **The suite is nowhere near it.** The widest model by total declared width is
   `width_root_unsat` at **1 998** (2 × 999). The next is `width_sat_depth` at 198. A cap
   would be guarding a region no test occupies.
5. **A guard for a non-risk is not free.** It is one more thing that can be found disabled
   — M1-T45's `if true || ...` is this tree's own example — and it would be normative, so it
   would need a SPEC paragraph asserting a limit nothing has yet required.

### The trigger that reverses this

Any one of:

- a total declared width above **500 000** reached by a model somebody actually wants to
  run (≈22 MB `.opb` on the constant above), or any `.opb` past ~25 MB from width alone;
- an incident — a killed run, a swap event, a verify that does not finish — traced to
  **total** rather than to a single variable's width;
- M4's interval or direct encodings changing the per-unit constant materially, since the
  whole argument rests on ≈40–58 bytes per unit;
- a second front end or an API caller that declares variables in a loop, where "nobody
  writes 100 variables at the cap by accident" stops holding.

When it reverses, the number should come from the artefact size someone is willing to
review, not from the per-variable cap. **The measurement above is the input, so whoever
reverses this does not have to re-derive it.**

### What is NOT claimed

That the gap is harmless in general — only that it is not reachable by accident today and
that no artefact size observed so far is a problem. D-0041's per-variable cap remains the
control that matters, and the `.pbp` side of this was not measured separately; the table is
`.opb` bytes, which is the term the ladder dominates.

## D-0043  D-0038 resolved: the conclusion is a `Reason.fact`, carried on `justified`, in `reason.ml`

**Status**: DECIDED, 2026-09-17. **Resolves D-0038**, which had four routes and no verdict
because the evidence was not in yet. **Route 3** is chosen — fold it into the D-0026 split
— and the implementation lands in `lib/core/reason.ml`, **not** `lib/core/explanation.ml`.

### Why the verdict waited, and what arrived

D-0038 was raised out of M1-T51, which built `Writer.pol_concluding` and `Writer.implied`
and could give them **no caller in `lib/`**, because `Combine`/`Cut` record *how* a bound
was derived and not *what*. The blocker was never the checker rule — `ia` and `e` exist in
both checkers — it was that the claim did not exist to pass.

Two sessions then converged on the same answer independently, from opposite ends, which is
why this is now decided rather than argued:

- **M2-T8** (the D-0026 split) reported that `Reason.fact` — `At_least`/`At_most` over a
  name, a value and a declared flag — **already *is* a bound claim**, so the conclusion
  type exists and needs no invention. It recommended `reason.ml` over `explanation.ml`.
- **M2-T9** (the defining-line index) found a **second, independent use**, and it is the
  one that settles it. The index it built is structurally limited to the clause-shaped
  half of the proof: it can key a `rup` line because `Justify` knows that line's claim,
  but **a `pol` line's content is computed by the checker and unknown to us**, so
  `Combine`/`Cut` cannot be indexed at all. A conclusion on the explanation is *exactly
  the key those lines would be indexed under* — the same value `pol_concluding ~claim`
  wants.

One use is a feature request. **Two unrelated consumers needing the same missing value is
a type that is absent**, and that is the argument.

### The decision

A `Reason.justified` gains a conclusion expressed as a `Reason.fact`. The exact spelling is
the implementing task's to choose; what this record fixes is *where it lives* and *what it
is*.

**Not in `explanation.ml`.** That file is a contention hotspot `CLAUDE.md` protects, every
propagator depends on it, and M2-T8 got through the whole D-0026 split **without a new
constructor there** — reaching for one now, for a value that is already `Reason`'s
vocabulary, would spend that protection for nothing.

**On `justified`, not beside it.** D-0038's route 2 was "propagators supply the claim at
the emission site", and it is rejected for the reason route 2 itself names: nothing would
force the conclusion and the reason to agree, which is most of the property wanted. The
whole point of D-0026's `justified` is that it is the single value every mutator takes, so
the field rides along with no new plumbing and cannot be supplied inconsistently.

### On the conclusion being optional

D-0038 worried that an optional conclusion reintroduces route 4's "partial by
construction" weakness. It does not, and M2-T9's finding is why: the partition is
**principled and already exists in the code**. A conclusion is meaningful exactly where a
*pruning* happened. A **decision** has none — D-0037 settled that a decision is an
assumption, not a derived bound — and a **conflict** concludes falsity rather than a bound.
`Trace.claims` already draws that exact line, writing a line for a pruning and none for a
decision. An optional conclusion tracks a distinction the solver already makes, rather than
marking coverage the design failed to reach.

### What this unlocks, and what it does not

**Unlocks.** `Writer.pol_concluding` and `Writer.implied` get their first caller, closing
M1-T51's adoption gap — and with it the defect M1-T51 measured, that a `pol` deriving
something strictly weaker than the claimed bound is **accepted** bare and **rejected** once
the conclusion is stated. M2-T9's index extends to `pol` lines. And M2-T8's agreement check
becomes exact instead of "…or the fact has a support", which is the looser of its two arms.

**Does not unlock**, and M2-T9 was explicit about this so it is recorded rather than
discovered: it does **not** give `defining_lit` a caller. That needs a *citation* slot in
`Combine`/`Cut` — D-0009's other, separate missing field — and that is a different decision.

### Sequencing

This is **not** a precondition of M2-T3 and must not be folded into it; M2-T3 is already
the largest remaining task and D-0011's lesson was that preconditions close *before* a big
task starts, not during. It is a natural companion to **M2-T9's follow-up** and to M4-T1,
which D-0040 requires to emit an explicit `pol` ahead of its trace line — precisely the
`pol` whose conclusion this makes checkable.

## D-0044  The learned object is a PB inequality; a clause is its degenerate case

**Status**: DECIDED, 2026-09-18. Sets the architecture for M2-T3, which is split into
**M2-L0 … M2-L9** in `docs/ROADMAP.md`. Does **not** re-open D-0026, D-0037 or D-0043.

### The question

M2-T3 said "clause learning from conflicts (1UIP)". Lazy Clause Generation is the
successful approach and clauses are what it learns, but committing the *learned-constraint
type* to a clause is a decision that is expensive to reverse: every later wish for
cardinality or linear learning then has to bridge two representations. The question raised
was whether we can learn pseudo-Boolean constraints instead, and how far "instead" can go.

### The decision

**The learned-constraint type is a PB inequality `sum a_i l_i >= b` over `Lit.t`. A clause
is the degree-1, unit-coefficient case of it, not a separate type.** The first conflict
analysis we build (M2-L3) emits only the clause case; the type does not know that.

**The reduction rule is a named, swappable component** (M2-L5), not code inlined into
conflict analysis.

**The arbitrary-constraint route is rejected** — see below.

### Why this costs us nothing here, and would cost Pumpkin a lot

This is the load-bearing argument and it is a property of *our encoding*, so it is worth
stating rather than assuming.

Pumpkin's LLG (Baauw, Flippo & Demirović, CP 2025) reports that its largest single cause of
failed linear analysis is **hitting a clause**, and says why: it deliberately does not
create 0-1 variables for atomic constraints, so a clause is a set of atomic constraints
rather than of Boolean variables, and converting one to a linear inequality would mean
minting an auxiliary variable per literal.

**D-0028 gives us the opposite.** The order encoding is eager, so every atomic constraint
already *is* a 0-1 variable in the `.opb`, and a clause over order literals already *is*
the PB constraint `sum l_i >= 1` over those same variables. There is no conversion, no
auxiliary variable, and no fallback cliff between the clausal and the linear path.

So "clause learning" and "PB learning" are not two regimes for this solver; they are the
same regime at two coefficient profiles. Sequencing clauses first (M2-L3) is therefore a
*staging* decision, reversible at any point, and not the lock-in it would be elsewhere.

The price of that encoding is width — it is Theta(total width), which is D-0041 and D-0042,
and it is why the test suite keeps declared domains in the single digits. That price is
already paid for other reasons; this decision spends none of it.

### Why the reduction rule is a separate component

PB conflict-analysis strength is an active research area whose results are **dominance**
results, not benchmark wins, so the upgrade path is known in advance:

- division beats saturation, exponentially (Elffers & Nordström, *Divide and Conquer*,
  IJCAI 2018, and *On Division Versus Saturation*);
- `roundToOne` — weaken literals, then divide so the reduced reason has slack zero —
  is RoundingSat's stronger reduction;
- Lomis, Devriendt, Bierlee & Guns (SAT 2025) give two further reductions, each shown
  *at least as strong* as the existing ones;
- MIR-based reduction (Mexi et al.) returns an equally strong or stronger reason than
  division.

The ceiling is known too: Vinyals et al. (SAT 2018) show what such solvers implement sits
strictly *between* resolution and cutting planes, because every intermediate constraint is
forced to stay conflicting. Strengthening the reduction moves us inside that gap; it does
not close it. Nobody should expect a silver bullet from M2-L5 or M2-L7.

**Measured against our own code, 2026-09-18:**

| Reduction | Expressible today |
|---|---|
| division-based | **yes** — `Combine (summands, divisor)` is weaken-then-divide |
| `roundToOne` | **yes, no ADT change** — `Weaken lits` then `Combine` with the divisor |
| saturation-based | **no** — `Writer.Pol.saturate` exists and emits ` s`, and PROOF-FORMAT §2a documents it, but `Explanation.t` has no `Saturate` constructor, so `Justify` cannot reach it. That is M2-L7 and it needs its own record |
| MIR | **no** — and Koops et al. note MIR is not the same as CG division. Out of scope |

The reduction we can already express is the one that is provably stronger. That is luck,
not design, and it is why M2-L5 needs no ADT change.

### That this is loggable at a sane cost is measured, by someone else

Koops, Le Berre, Myreen, Nordström, Oertel, Tan & Vinyals, *Practically Feasible Proof
Logging for Pseudo-Boolean Optimization* (CP 2025) log the **full** conflict analysis of
RoundingSat and Sat4j — division, saturation, weakening, core-guided search, LP integration
— in VeriPB with a CakePB backend. RoundingSat: proof-logging overhead **median 2.7%**,
95th percentile 21.1%, worst 46.2%; checking **median 1.43x** solve time, 95% within 9.22x,
worst 19.17x.

This is the single most important external fact for this plan, and it is *their*
measurement, not ours: it says the emission path we are about to build is known to be
affordable, and it removes "proof logging will make learning unaffordable" from the list of
reasons not to try. Their partial-weakening-before-division technique (for divisions that
are not in normalised form) and their merging of adjacent weakening steps on `pol` lines
should be read before M2-L6's emission path is designed, not after.

### The arbitrary-constraint route, and why it is rejected

Veksler & Strichman (*Learning General Constraints in CSP*, CPAIOR 2015 / AIJ 2016) go
past signed clauses to direct inference between general constraints: `Infer(c1, c2) -> c*`
subject to (i) `c1 /\ c2 -> c*`, (ii) `c*` under the pre-propagation domains propagates to
false — the same conflicting invariant — and (iii) explicitly, the strongest `c*` **that is
easy to propagate**. They give rules R1–R7 satisfying (i) and (ii), R8–R9 satisfying only
(i) and applied speculatively, and a meta-rule for disjunctions. Their examples do learn
strictly stronger constraints than resolving the corresponding explanations.

Rejected for us on cost, not on merit:

1. The rules are **per ordered pair of constraint types**, not per constraint. Nine rules
   bought them a handful of pairs; our nine propagator families are up to 45.
2. Their own requirement (iii) is the wall: a learned constraint must be something the
   solver can already propagate. For us each new learned *shape* needs a propagator, an
   I-X10 classification and a justification.
3. They still need a clausal fallback for unhandled pairs — as do IntSat and LLG. Three
   independent systems, same fallback. **That is the argument for keeping M2-L3's clause
   path permanently, and it does not rest on any one paper's benchmark table.**

Recorded here so that M4-T2 (Régin) does not re-open it by accident.

### Status register

**Measured**: what our ADT and writer can express (the table above, read off
`explanation.ml` and `writer.ml` on 2026-09-18). **External, measured by others**: the
Koops overheads, the reduction dominance results. **Argued, not measured**: that the
order-encoding argument makes the clause/PB regimes genuinely one for us — it follows from
D-0028 and from `Encoding`'s literal naming, but no code has yet built a `Learned.t` from a
clause and propagated it as a PB row. **M2-L1's test (b) is what converts it**, and if it
fails, this record's central claim is wrong and the staging in M2-L3 must be revisited.

### Amendment, 2026-09-18: the cut is a second pluggable axis, and 1UIP is not settled

Added the day this record landed, because the original text treated 1UIP as given and one
of its test obligations (M2-L2's) encoded that assumption as a general invariant of the
cut. It is not one.

**The theorem that justifies 1UIP does not carry over.** Learning the first assertive
clause gives the highest possible backjump *in a SAT solver*; Le Berre et al., *On
Improving the Backjump Level in PB Solvers* (arXiv 2107.13085), state there is **no such
guarantee in the presence of PB constraints**, so deriving an assertive constraint is no
longer a sufficient stop condition, and they study continuing the analysis past the 1UIP to
get a better backjump. A PB constraint propagates by slack, not by "all but one literal
falsified", so a derived constraint can carry several conflict-level literals and still be
asserting. The clausal stopping rule is not merely suboptimal there; it measures the wrong
thing.

**It is not settled in SAT either.** Feng & Bacchus, *Clause Size Reduction with all-UIP
Learning* (SAT 2020), apply all-UIP under the constraint that LBD does not increase over
the 1UIP minimum, with a measured improvement; Fleury & Biere (SAT 2021) made it efficient.
Zhang et al.'s 2001 comparison that made 1UIP standard was CNF with VSIDS and restarts, and
we have neither VSIDS nor (per SPEC §3.4, M2-L9) restarts.

**So the stopping criterion is a named component, exactly as the reduction rule is.** The
clause path (M2-L3) uses 1UIP; the PB path (M2-L6) uses the slack-based criterion. Neither
is written into the analysis.

**The proof-cost structure of the two paths is opposite, and this appears to be ours to
discover.** A learned clause is a single `rup` line — intermediate resolvents are never
logged, the checker re-derives them by unit propagation — so on the clause path the cut
choice costs **nothing** in proof size and is a pure search question, revisable for free.
On the PB path RUP does not work, which is the difficulty Koops et al. exist to solve, so
every combination and reduction step is a `pol` operand and the cut choice **directly sets
proof size and verify time**. The literature pulls toward cutting *later* for a better
backjump; our proof cost pulls toward cutting *earlier*. M2-L8 is the row that can measure
which wins, and no existing solver can have measured it, because none logs PB learning over
integer variables.

**Register**: the two citations are external and measured by others. That the proof-cost
asymmetry favours an earlier cut on the PB path is **argued, not measured** — it follows
from `rup` needing no intermediate lines and `pol` needing one per step, but no byte of ours
has been counted. M2-L8 converts it or refutes it.

### Amendment, 2026-09-18: the claim is CONFIRMED in the proof and BOUNDED in the store

M2-L1 converted D-0044's central claim from a bet into a measurement, and found the edge of
it at the same time. Both halves are recorded because the second one steers M2-L3.

**Confirmed, in the proof.** A degree-1 unit-coefficient `Learned.t` over order literals
propagates **exactly** as `Bool_clause` does, on all 27 scenes tried, conflicts and domains
alike — with a negative control proving the comparison can separate a *different* clause,
so the agreement is a measurement and not a vacuous pass. The bet behind it held too: the
runtime instance is a `Linear` instance, and **no new propagator family** was added.
`lib/core/learned.ml` builds a `Linear.t` and hands it to `Propagator.pack`.

**Bounded, in the store, and this is the part to read before M2-L3.** In the `.opb` an
order literal *is* a variable, so a `Learned.t` is written out with no conversion. In the
solver's **store** order literals are not variables at all — the store holds the model's
integer variables, and `x >= v` is a *question about a domain*, not a handle. So a runtime
instance exists only where the PB row reads back as a linear row over integer variables,
and `Learned.to_linear_row` is exactly that predicate. It succeeds on a clause over `var
bool`s (D-0007 order-encodes a Boolean on `[0,1]`, so its ladder has one rung) — **but
"Boolean" is too narrow, and the correction matters: the real condition is DECLARED WIDTH 1,
which is broader. `ne_eq_unsat` (`x, y : 1..2`) and `trace_settle_sat` (`y : 2..3`,
`z : 0..1`) both convert and contain no Boolean at all; 3 of the 13 converting clauses come
from non-Boolean width-1 variables. Anyone restricting a cut "to Boolean shapes" on the
strength of the original sentence would restrict it too far. Measured and corrected
2026-09-18, see D-0050** — on a model
row's own expansion (every rung gets the same coefficient, so a uniform run is
`a_i * (x - lo_i)`), and on a threshold outside the ladder, which is a constant.

It returns **`None`** on a threshold strictly *inside* an integer variable's ladder:
`x >= 3` for `x` declared `0..5` is not any linear function of `x` over that box, and
neither is a sum of two such. **There is no rounding of this, and it matters because a 1UIP
cut over integer variables produces exactly those literals** — so M2-L3 must expect `None`
from `to_linear_row` on its own output, and must either restrict the cut to the shapes
above or accept that the learned constraint is **proof-only** until a propagator for it
exists.

This does **not** refute D-0044. The learned object is still a PB inequality and the
*proof* side is unqualified — a proof-only learned constraint is still sound, still
deleted correctly, and still does its work in the derivation. What is bounded is where a
**runtime propagating instance** can exist today. Recorded here rather than discovered in
M2-L3.

## D-0045  SPEC §3.4 and restarts: the question raised, with the finding it turned up

**Status**: **OPEN — a question, not a decision.** Raised 2026-09-18 by the orchestrator as
**M2-L9**, whose row says in terms: *raise it; do not decide it unilaterally.* `docs/SPEC.md`
is the authority (CLAUDE.md), so a change to §3.4 goes through a record with a verdict in
it. This record has no verdict. It exists so that whoever writes one is not starting from a
blank page, and because **raising it turned up something that bears on M2-L1/L3/L4 right
now**, whether or not restarts are ever enabled.

### The question

SPEC §3.4 fixes the default as *"first-fail variable selection, min-value branching,
depth-first, with restarts disabled"*. M2-L0 … M2-L8 add clause and then PB learning. In
CDCL, learning and restarts are complementary rather than independent: much of a learned
constraint's value is realised on a **different** region of the search tree from the one
that produced it, and restarting is the mechanism that reaches that region. With restarts
off, a learned constraint mostly prunes within the subtree it was learned in, and the
sequence recovers a fraction of its benefit. Nogood-recording-from-restarts (Lecoutre et
al.) is unavailable to us for the same reason — its entire premise is the restart.

So: **should §3.4 keep restarts disabled once learning works?** Not answered here.

### What the proof would cost — less than expected

The instinct is that restarts fight **I-X4** (*the proof is append-only and never rewound;
backtracking becomes deletion, not truncation*). They do not. A restart is a backjump to
level 0 — the operation the solver already performs and already logs. `Writer.wipe_level l`
retires every constraint tagged at level `>= l`, so a restart is `wipe_level 1`, and
`del_run` already bounds the number of lines that costs (M1-T29, D-0024). **I-S3** (level on
return equals level on entry) is satisfied for the same reason: a restart from depth *d* is
*d* levels of the unwinding that already exists. And §3.4's own second sentence — *"every
branching decision and every backtrack MUST be reflected in the proof"* — already covers a
restart normatively, because a restart **is** a backtrack.

The cost is therefore not in the proof machinery. It is in completeness, below.

### Where the real cost is: I-S2

**I-S2** says `=====UNSATISFIABLE=====` is printed only after the space is exhausted, and
the proof must independently establish it. Restarts with a fixed cutoff make search
**incomplete** — a restart discards the remaining subtree without refuting it. Completeness
is restored by an increasing restart limit (Luby, geometric), or by learning, because the
accumulated learned constraints stop the search re-entering what it has already refuted.

That gives a sequencing argument worth recording even before the verdict: **restarts must
not be enabled before learning works.** Enabled earlier they would not be a tuning
parameter, they would be a soundness bug against I-S2, and one the model suite would very
likely not catch — 34/34 can pass while an UNSAT answer has stopped being earned.

### The finding this raised, which does NOT wait for the verdict

`Writer.wipe_level l` deletes every constraint **tagged at level `>= l`**. A learned
constraint exists precisely to outlive the conflict that produced it. So:

> **A learned constraint tagged at the decision level it was learned at is deleted by the
> very backjump that follows learning it.** It must be a level-0 object, or the `del` that
> retires its level takes it with it.

This is not a restart problem; restarts only make it obvious. It is a constraint on
**M2-L1** (proof-side introduction and deletion), **M2-L3** (attach the clause at the
backjump level, not the level being retired — the row already says so, and this is *why*)
and **M2-L4** (the retention policy must own the constraint's lifetime; if `wipe_level`
also owns it, the two will double-delete and break **I-X2**, which M2-L4's test (a) asks
about). Recorded here rather than left to be discovered in a rejected proof.

### What decides it, and what a verdict owes

**M2-L8's measurement**, not this record and not a citation. Deciding it now would be
deciding it without the numbers, which is the sequencing M2-L9 was given last place for.

A verdict that enables restarts owes: the named policy and its parameters in §3.4 (a policy,
not a constant); the I-S2 completeness argument written out for *that* policy; a
determinism argument, since the gate requires two runs of one binary to be byte-identical
and a restart schedule driven by anything but a deterministic counter breaks it; and a proof
artefact from a model that actually restarts, verified by both checkers.

A verdict that keeps restarts disabled owes only the measurement and a sentence in §3.4
saying it was considered against learning and declined — so the next session does not
re-raise it from scratch.

**Register**: the proof-cost analysis above is **argued from the code** (`wipe_level`,
`del_run`, I-X4, I-S3), not measured — no proof containing a restart has ever been emitted
or checked. The `wipe_level` finding **is** grounded: `lib/proof/writer.ml:764` computes its
doomed set as every id tagged at level `>= l`.

### Addendum, same day: the finding is sharper than stated above, and it is a tension, not a caution

Followed up in the code rather than left as a caution, because it steers three rows.

**Every id is tagged automatically, with no opt-out.** `Writer.fresh t ~origin`
(`lib/proof/writer.ml:547`) does `Hashtbl.replace t.tags t.next_id t.level` under 3.0 — it
tags the new id with the writer's **current** level, unconditionally. There is **no
`~level` argument** on `fresh`, and `set_level` (`:593`) is the only thing that moves
`t.level`. So a learned constraint does not merely *risk* being tagged at the conflict
level; it **is** tagged there, automatically, by the act of allocating its id.

**That collides head-on with M2-L3's own emission rule.** M2-L3's row requires the learned
clause's derivation be emitted *"while the trace lines supporting it are still live"* —
that is, **before** the level is retired. Survival requires the learned id **not** be
tagged at a level the retirement wipes. Today those two cannot both hold:

| requirement | forces |
|---|---|
| M2-L3: derive while supports are live | emit **before** `wipe_level` |
| the constraint must outlive the conflict | id tagged **below** the wiped level |
| `Writer.fresh` | tags at `t.level`, **no override** |

The only lever in the current API is `set_level t 0` before emitting, and that is not a
free move: `set_level` is *"the only thing that writes a level marker"*, so it would emit a
`% level 0` into the middle of a derivation and change the proof's level state around it.

**So M2-L1 almost certainly owes `lib/proof/writer.ml` a new entry point** — an id
allocated at a chosen level (`fresh ~level`, or a `fresh_persistent` that tags 0) — rather
than a call-ordering trick in `lib/core`. That is a *proof-side* change, in a file the
learning rows would otherwise never open, and it is the kind of thing that is cheap now and
expensive once three rows have each worked around it differently.

**And it must work in both formats.** Under 2.0 `t.tags` is not maintained at all — the
checker holds the level stack and `w l` retires against it (`:876`). So the same hazard
exists under 2.0 but is enforced by the *checker* rather than by our table, and a fix that
only adjusts `t.tags` would be green under 3.0 and wrong under 2.0. Both wordings, both
formats — the M1-T46 discipline applied to a data structure instead of a message.

**Register**: this paragraph is read off the code (`fresh` at `:547`, `set_level` at `:593`,
`wipe_level` at `:764`, the 2.0 note at `:876`) and is **not** measured — no learned
constraint has ever been emitted, so no proof has yet been rejected this way. The
prediction to falsify is: emit a learned constraint at the conflict level, and the backjump
that follows deletes it.

### Resolved, 2026-09-18, by M2-L1 — and the addendum guessed the wrong shape of fix

The prediction above was *"emit a learned constraint at the conflict level and the backjump
deletes it."* **It holds, exactly as written**, and it was measured through both checkers
before anything was changed — which is the order this project asks for and the order that
makes the fix trustworthy:

| format | the checker's own words |
|---|---|
| 3.0 | `Trying to access constraint with ID 3 that has already been deleted` |
| 2.0 | `Rule 6 is trying to access constraint (constraintId 3), that was marked as safe to delete` |

**The fix is `Writer.with_level t l f`, a bracket — not the `fresh ~level` this addendum
proposed.** The addendum's own 2.0 paragraph is why, and I did not follow my own reasoning
to its conclusion when I wrote it: under 2.0 `t.tags` is **not maintained at all**, so
nothing written into our table ever reaches the checker. The level therefore has to move
**in the proof**, not in our bookkeeping. `with_level` emits `# 0`/`# 1` under 2.0 and
`% level 0` under 3.0, and restores the level on exception. `Justify.with_level` wraps it,
and the memo and M2-T9's claim index stamp `current_level`, so they follow for free.

Both formats accept the fixed proof; eight checks cover the broken and the fixed direction
in each format. The lesson is a small one and worth keeping: **an addendum that reasons
correctly about a constraint can still propose a fix that violates it.** The 2.0 sentence
was right and the suggested entry point contradicted it in the next paragraph.

**One more finding, recorded because it bounds a guard rather than a feature**: the
`BAGUETTE_PROOF_AUDIT=1` live-set audit **cannot see a double delete** — a second `forget`
is a no-op, so the set is already clean. I-X2 says ids are deleted *exactly* once, and the
audit only witnesses the *at least* once half. M2-L1's test counts `del` lines in the proof
text instead. **M2-L4 is where this bites**, because its whole subject is a retention
policy that may want to delete something a backjump also wants to delete.

## D-0046  Proof format 2.0 is removed from the project entirely

**Status**: **DECIDED, 2026-09-18, by the project owner.** Not an orchestrator judgement
call — this record exists because `docs/SPEC.md` is normative and CLAUDE.md requires a
change to it to go through a decision record. Supersedes the dual-format arrangement
D-0025 set up when 3.0 became the default.

### The decision

The solver emits **VeriPB 3.0 and only 3.0**. Format 2.0, the `BAGUETTE_PROOF_FORMAT`
switch, and the Python VeriPB **2.2.2** checker leave the project.

### Why now

D-0025 made 3.0 the default and the checker of record and kept 2.0 alongside it. That was
right at the time; what has changed is the measured cost of keeping it.

**M2-T14 (2026-09-18) is the argument.** It found **four** test lanes passing for the wrong
reason, every one of them on the 2.0 path, all the same defect: two artefacts disagreeing
about format, the checker refusing the file on the **grammar**, and a lane asserting
REJECTION taking that refusal as evidence. The worst was `test_mutation.ml`'s
`rows_that_refute_alone` — **D-0030's own certification that an instance is not hollow, and
it was itself hollow**, reporting "no row refutes alone" for every instance.

The root cause is structural and does not get better with more sweeping: **the gate runs 3.0
only**, so nothing routinely exercises 2.0, and a second format that nothing exercises is a
place where vacuous passes breed unobserved. The options were to add a 2.0 leg to the gate —
roughly doubling checker time to protect a format nothing ships — or to delete the format.
Deleting it removes the bug class rather than sweeping it periodically.

### What this costs, stated plainly

**We lose a second, independent implementation as a cross-check.** Two separately written
checkers agreeing that a proof verifies is stronger evidence than one, and several findings
this project is proud of — M1-T46 itself, D-0030's measurements, D-0023's correction — came
from the two disagreeing. After this, **veripb 3.0.2 is the sole oracle**, and a bug in it
is a bug we have no way to see.

That cost is real and was accepted. It is recorded here so that nobody later rediscovers it
and assumes it was overlooked. If a second 3.0-capable checker ever exists, wiring it in
recovers the property without bringing 2.0 back.

### What goes

`Writer`'s `V2_0` and every `v3 t` branch; `BAGUETTE_PROOF_FORMAT`; the 2.2.2 entry in
`Checker.find` and `scripts/checker.sh`; `Opb`'s unlabelled mode and `Encoding.write_opb`'s
`?labels` (labels become unconditional, and `write_opb_for` collapses into `write_opb`);
`PROOF-FORMAT.md` §2, the 2.0 rule contract; `SPEC.md` §4.1's mention of the switch;
`bench`'s `-F` flag; and every 2.0 lane and format matrix in the suite.

### What stays, and this is not negotiable

**History is not rewritten.** D-0023, D-0024, D-0025, D-0030 and the parts of
`PROOF-FORMAT.md` that *record what 2.0 did and what it cost us to learn* stay exactly where
they are, marked historical. Several of them are the evidence for decisions still in force —
D-0024's account of why `wipe_level` reproduces `w l` explains code that survives this
change. Deleting the reasoning because the format went would throw away the expensive half.

### Consequences to handle deliberately, not by leaving stale text

- **M1-T46's rule collapses.** "Never match on one checker's wording alone" exists because
  two checkers worded rejections differently. With one checker, matching its wording *is*
  correct. Every such site must be **simplified deliberately**, not left carrying a comment
  about a checker that no longer exists. There are many.
- **M2-T15 dissolves.** Whether a mutation lane's `expect` should be format-dependent is not
  a question once there is one format. Close it.
- **The two deliberately-red mutation lanes disappear** with it.
- **Part of M2-T14's work is deleted by this**, hours after it landed. Its format-pairing
  fixes become moot; its *format-independent* strengthenings — the wording assertions added
  to twenty blanked-trace controls, and resolving the claim-index id by **content** rather
  than by label — survive and are keepers. Said plainly because the sequencing was mine, not
  a failure of that session.

## D-0047  M2-L6's negative result is a *prediction*, and this is its falsifier

**Status**: **RECORDED as a prediction, with a falsifier that is being run right now.**
Written 2026-09-18 by the orchestrator, at the request of `docs/EXPLANATION-REVIEW.md` §4,
**before** M2-L11 reports. The order matters: a prediction written down after the
experiment reports is not a prediction.

### Why this needs a record at all

M2-L6 returned an honest negative, and the finding currently lives in **one commit message
and one module header**. That is not enough to stop the next session re-running the
experiment and re-deriving the same negative from zero — which is a real risk, because the
row that would do it (M2-L7, `Saturate`) reaches for the same machinery. A session that
starts from this record starts from *"carry the ladder rows into the reason"* instead.

### The finding

PB conflict analysis works: where the PB path succeeds it derives the **empty
contradiction**, which is strictly stronger than the clause it replaces — it entails it,
and the clause path has no route to it. But it is **degenerate as a propagation result**.
Measured over the suite: `pb-stronger` at **36 of 36** learned rows, and every one of those
36 is the degenerate case. A scene where a non-trivial learned inequality outpropagates its
clause **was looked for and not found**.

### The cause, and the prediction that follows

**Our integer propagator is stronger than PB propagation on the same row.** `3a + 2b <= 14`
with `lo(b) = 4` lets `Linear` deduce `a <= 2`; the row *alone* has slack 6 against pivot
coefficient 3, so PB propagation on it deduces nothing. The strength is not in the row — it
is in the **order-encoding ladder implications, and D-0028 puts those in separate `.opb`
rows**. `Linear` already builds model-row-plus-ladder-chain as an `Explanation`
(`Order_reason.weaken_declared`, D-0010); it never builds it as a *row*, so the PB analysis
never sees it.

> **The prediction, stated so that it can fail.** PB learning will keep producing degenerate
> rows **for exactly as long as a reason is the model row without its ladder chain** — no
> matter which reduction rule, stopping criterion or elimination order is used. The
> degeneracy is a property of the *reason*, not of the analysis.

### The falsifier

**M2-L11**: carry the ladder rows into the reason, then count learned rows that are not the
empty contradiction. Two outcomes, and both are informative:

- **Non-degenerate rows appear.** The prediction holds, the cause was the reason, and
  M2-L6's expected gain was simply banked in the wrong row.
- **They do not.** The prediction is **wrong**, and that is the more interesting result: it
  would locate the weakness in the elimination or reduction step rather than in the reason,
  and it would make M2-L7 (`Saturate`) the next thing to try rather than a detour.

Whoever closes M2-L11 should come back and mark this record with which one happened.

### Scope

This is a statement about **this solver's encoding** (D-0028), not about PB learning in
general. D-0044 already makes that distinction for the learned-object type and it applies
here unchanged: the degeneracy is downstream of the order encoding, so nothing here
generalises to a solver whose propagators and whose PB rows express the same strength.

### AMENDED the same day, 2026-09-18: the figure this record was built on is wrong

**The prediction above was anchored to M2-L6's headline — `pb-stronger` "36 of 36 learned
rows, every one degenerate". That figure does not hold.** M2-L11 found it while building the
counter this record asked for, and the orchestrator re-measured it independently on `main`
*before* merging M2-L11, by counting the emitted `ia` rows across the 38-model suite rather
than by reading any counter:

| | |
|---|---|
| learned rows, suite-wide | **36** |
| of those, **carrying terms** (non-degenerate) | **26** |
| genuinely degenerate | **10** |

The 10 are **exactly the `int_lin_eq` family** — `backjump_lineq_unsat` 3,
`near_limit_unsat` 3, `offset_unsat` 4 — and `width_sat_depth` **alone** contributes 24
non-degenerate rows of the shape `+2 a_ge_1 +2 a_ge_2 … >= k`.

**How the error was made, because it is the reusable part.** M2-L6's test (a) inspected the
`int_lin_eq` family, where the rows really are `0 >= k`. The conclusion was true of what was
looked at and was then stated of the suite, and **nothing counted**, so nothing contradicted
it. That is precisely the gap M2-L11's row existed to close — and the counter arrived one row
too late to stop the claim being written into a decision record first.

### What survives, and what is withdrawn

- **WITHDRAWN**: "PB learning keeps producing degenerate rows" as a *suite-wide* claim. It
  was never suite-wide. Most rows already carried literals.
- **SURVIVES, and is now measured**: the mechanism. Where the reason is the model row
  **without** its ladder chain, certain conflicts yield **no row at all** and fall back. On
  the fixture built for it, the lift turns **2 fallbacks into 2 non-degenerate learned rows**
  (`pb_ladder = false` gives 0 learned / 2 fallbacks). So the ladder chain was the missing
  ingredient for *those* conflicts — the effect is real, it is just smaller and differently
  located than the withdrawn figure implied.
- **Also corrected** (M2-L11, in `pb_analysis.ml`'s header): `Postcondition_failed` was
  called "the dominant non-`No_row` fallback". Of 50 fallbacks it is **2**; `No_pivot` is
  **26** and `No_row` **21**. The dominant case is conflicts whose conflict-level literals all
  rest on decisions, where there is simply nothing to resolve.

### The lesson this record now carries

D-0047 was written to stop the next session re-deriving a negative from zero. Written on an
uncounted figure, it would instead have handed them **a wrong number with a decision record's
authority** — worse than the commit message it was promoted from, because records are trusted
more. **A headline figure with no counter behind it is a claim, not a measurement**, and a
record inherits the confidence of whatever it cites. The orchestrator wrote this record citing
M2-L6's number without re-measuring it; the number was checkable in about two minutes with
`grep` over emitted proofs, which is how it was eventually checked.

## D-0048  Is a reified explanation a research output? D-0003's (a)-claim is coupled to an unrecorded answer

**Status**: **OPEN — a question, not a decision.** Raised 2026-09-18 by the orchestrator out
of `docs/EXPLANATION-REVIEW.md` §2, which reaches a **different conclusion from
`GCS-COMPARISON.md` §6** on the same evidence. This record follows D-0045's pattern: it has
no verdict, and it exists so that whoever writes one is not starting from a blank page.

D-0026 already settled the part that was settleable — (a) and (b) are **layered, not
alternatives**: reasons are declarative data, justifications stay the reified cutting-planes
expression. What is left open is narrower and is stated below.

### The two documents disagree

`GCS-COMPARISON.md` §6 puts it sharply:

> we have a reified cutting-planes expression on the trail where the mature solver has a
> closure, and nobody has yet said what the reified form buys. That is evidence against (a)
> being the productive axis.

`EXPLANATION-REVIEW.md` §2 answers that this **follows only if explanations are a solver
internal**, and that there is an answer from the literature side which is not a performance
argument:

> A closure cannot be printed, diffed, compared against a published explanation, lifted into
> a schema, or shipped anywhere. A reified `Combine` tree can.

Every use of explanations *outside* a solver's own conflict analysis needs them as data:
comparing a generated explanation against Schutt et al.'s hand-written `cumulative`
explanation; cataloguing explanation schemas per constraint; handing a derivation to an
external justifier; step-wise explanation systems consuming solver output (Bogaerts/Guns,
and the 2025 certifying-solvers work that replaces MUS search with proof-log reading). GCS's
own "higher-order" content is a typed serialisable witness for an external justifier — they
reified theirs too, at a different boundary.

### The coupling, which is the actual content of this record

> **Retiring `Deferred` / `Combine` in favour of a closure on runtime grounds is only sound
> if the project has *also* decided that explanations are not a research output.** Those are
> two decisions. Only one of them has ever been discussed, and it is the wrong one to decide
> first.

The failure mode this record exists to prevent is specific and quiet: a future session
profiles, finds the reified tree costs more than a closure, and retires it — thereby
deciding the research question **by accident, in a performance commit**, with nothing in the
tree recording that a question was decided.

### What would close it

Either direction is fine; leaving it implicit is not.

- **Close (a) by argument**: name at least one consumer of explanations outside conflict
  analysis that this project intends to serve, and the form it needs them in. Exportability
  then becomes a stated requirement, and any later profiling argument has to beat it rather
  than ignore it.
- **Abandon (a) explicitly**: record that explanations here are a solver internal and that
  the proof log is the only artefact anyone outside is meant to read. `Deferred`/`Combine`
  then stand or fall on runtime alone, and D-0003's (a)-claim is withdrawn rather than left
  hanging.

**It should not be settled by a profiler**, which is what will happen by default.

### AMENDED 2026-09-21: the goal is stated, and this record blocks nothing

The project's owner has stated the goal plainly: **implement explanation in a proof-logging
solver.** Not produce a research artefact. That settles the half of this record that was
speculative — the exportability argument (a `Combine` tree can be printed, diffed and shipped
where a closure cannot) is **not a reason this project holds**, so it must not be cited as one.

What survives is narrow and technical, and it is not a question anyone needs to answer now:
**if** a future session proposes replacing the reified cutting-planes expression with a
closure on runtime grounds, it needs a measurement, because D-0026 layered reasons-as-data
under justifications-as-expression deliberately. That is a guard against an unexamined
refactor, nothing more.

**This record was briefly cited as a blocker on M4-T1. That was an orchestrator error and it
is struck.** The dependency ran backwards: M4-T1 is the first derivation that actually
exercises `Combine`/`Weaken`/`Model_row`, so it is the **evidence** that would inform this
question, not something waiting on it. Nothing blocks M4-T1.

### Bearing on scheduled work

**M4-T1 is where this stops being abstract** and is the reason for raising it now rather
than later. It is the first derivation that actually needs `Combine` / `Weaken` /
`Model_row` (see that row, and `EXPLANATION-REVIEW.md` §3): a Hall justification cites many
model rows in one tree. If the reified form is ever going to demonstrate what it buys, that
is the row where it does — and equally, if it is going to look like expensive ceremony, that
is where it will. Deciding this *before* M4-T1 means the row is read as evidence; deciding
it after means the row is read as a verdict already reached.

## D-0049  The ladder chain as a row: the substitution rule, and why it lifts only non-falsified terms

**Status**: **ACCEPTED**, implemented by M2-L11 (2026-09-18, agent-ladder), `lib/core/ladder.ml`.
Written after the fact at the implementing session's request, because the row landed with
four design choices in it that are not obvious from the code and that a later optimisation
would plausibly undo.

### The problem

D-0028 encodes an integer variable as an order ladder, and the ladder implications live in
**separate `.opb` rows** from the model row. So a `Linear` pruning's true reason is *model row
+ ladder chain*, while PB conflict analysis was resolving against the model row alone. The
consequence M2-L6 measured: for conflicts of that shape, eliminating a pivot yields **no row
at all** and the analysis falls back to the clause path.

`3a + 2b <= 14` with `lo(b) = 4`: `Linear` deduces `a <= 2`, but the row alone has slack 6
against pivot coefficient 3 and PB propagation on it deduces nothing. Lifted onto `L_1` (×3)
and `L_2` (×6) the coefficient is 9 against the same slack 6, and it propagates.

### The four decisions

**1. The substitution rule is one rung, one term, degree-neutral.** One ladder row moves one
term one rung. Degree-neutrality is what makes the lift checkable: a chain counted twice
would move the degree, so the test asserts the degree is unchanged, the cited ids are
duplicate-free, and the cited set equals the antecedent set. That is the double-counting guard
M2-L11's test (c) demanded, and it is cheap precisely because of this rule.

**2. Lift only *non-falsified* terms.** This is the one that looks like a missing case.
Lifting a **falsified** term adds the same amount to the slack as it adds to the pivot
coefficient — so it buys **nothing**, and leaves a larger absolute slack to reduce afterwards.
A later session reading the code will see an unhandled case and be tempted to "complete" it.
It is not incomplete; it is the argument. Anyone changing it must show a scene where lifting
a falsified term strictly helps.

**3. Retry, do not replace.** The bare model row is tried **first**, and the ladder lift runs
only if that fails. So every conflict M2-L6 already handled takes M2-L6's derivation,
unchanged, and the lift is reached only where the old path produced nothing. This is why the
suite's artefacts move on exactly one model. It also means the lift can never make a proof
worse — the worst case is that it is not reached.

**4. I-S4 is discharged structurally, not by checking.** Ladder cids are **level-0 `.opb`
rows**, retired by nothing, so a learned constraint that cites them still rests only on model
rows. There is no new way for a learned row to depend on something that gets deleted under it.

### What it bought, stated honestly

On the fixture built for it (`test/models/ladder_lift_unsat.fzn`): 2 conflicts, **2 rows
learned, 0 fallbacks, both non-degenerate, 2 rungs cited**; with the lift off, **0 learned, 2
fallbacks**. Suite-wide it fires on **one model of 39**, converting 2 fallbacks into 2
non-degenerate rows.

**That is a small number and it should be read as one.** The large claim this row was expected
to support — that PB learning was producing degenerate rows across the suite because the
reason lacked its ladder chain — **turned out to rest on a mis-measurement**; see D-0047's
amendment. What is established here is narrower and solid: where the reason genuinely lacks
its chain, the analysis produced **nothing**, and now it produces a real inequality.

### Where this is likely to be picked up next

M2-L7 (`Saturate`) and M2-L4 (deletion) both touch this path. The lifted rows are
non-degenerate but, on the fixture, **do not convert** to a propagating linear row
(`pb-convert 0`), so the next honest question is not "lift more" but **what a learned PB row
has to look like before `Learned.to_linear_row` accepts it**. That is a better-posed question
than the one this row started from.

## D-0050  `to_linear_row` is the right predicate being used as the wrong gate

**Status**: **the measurements are SETTLED; the design question is OPEN.** Produced
2026-09-18 by a read-only study (agent-convert, wave seventeen) and re-measured
independently by the orchestrator before recording. It answers the question D-0049 closed
on, and the answer is not the one that question assumed.

### First, the premise that prompted the study was wrong, and the error was mine

D-0049 ended by observing `pb-convert 0` on M2-L11's own fixture and asking what a learned
row must look like before `Learned.to_linear_row` accepts it. D-0049 stated that carefully,
as a fact about its fixture. **The orchestrator then generalised it** — into a wave briefing
and into a report — as though learned rows do not convert in general. Suite-wide,
**`pb-convert` is 36 of 38**. The two refused rows in the entire suite are precisely the two
that M2-L11's ladder lift produced.

That is the second time in two waves that a figure true of one model or one constraint family
was restated as a property of the suite (the first was M2-L6's "36 of 36 degenerate", see
D-0047's amendment). **The pattern is the finding**: this project's counters are per-run and
summed by hand, so a number read off one model looks exactly like a number read off the
suite. Say which you have.

### The predicate, stated so a test can assert it

`lib/core/learned.ml:362`, via `ladder_form` (:292) and `linear_of_rungs` (:329). A learned
row converts iff, **for every integer variable it mentions, the row carries that variable's
entire ladder at one uniform coefficient and one uniform polarity** — nothing partial, no
gap, no second coefficient. A single `Lit.Eq` refuses outright (:298).

Two corollaries carry the weight:

- **For clauses it collapses to declared width 1.** Every clause coefficient is 1, so
  uniformity is free and the rule becomes "the thresholds mentioned are the whole ladder".
  `Learn.minimise` (`lib/core/learn.ml:201`, `Strongest`) deliberately keeps one threshold per
  variable per direction, so a variable of declared width ≥ 2 can never have its full ladder
  present. **Our own minimisation is a strengthening step that is simultaneously a
  convertibility-destroyer.** Not a bug — but it is a designed-in ceiling nobody had stated.
- **It tests an algebraic identity, not entailment.** `[x≥3] ≥ 1` is refused although it
  entails `x ≥ 3`, a perfectly good linear row.

### Where conversion actually fails (39 models, re-measured)

Totals: `learned 88`, `convertible 13`, `pb-learned 38`, `pb-fallback 50`, `pb-convert 36`,
`pb-nondeg 28`, `pb-stronger 36`.

| PB path, 38 rows | rows | where |
|---|---|---|
| degenerate, converts **vacuously** | 10 | `backjump_lineq_unsat` 3, `near_limit_unsat` 3, `offset_unsat` 4 |
| non-degenerate, converts **usefully** | 26 | `width_sat_depth` 24, `guess_wrong_sat` 1, `near_limit_ne_sat` 1 |
| non-degenerate, **refused** | 2 | `ladder_lift_unsat` only |

**There is no single blocker; there are two, in different places.** The PB path is not
blocked (36/38). The clause path is blocked hard: 13 of 88, all width-1, and the two paths
are perfectly disjoint because `Propagator.pb_row` has no row for the `array_bool_or` /
`bool_clause` / `bool_eq` / `bool_not` / `int_ne` families, so the PB path never runs there.

### The ladder lift and `to_linear_row` are mutually exclusive, structurally

`Ladder.lift` substitutes a rung for a higher one and accumulates multipliers, so source rungs
vanish and the target's coefficient grows (`lib/core/ladder.ml:59`). **If the lift moves any
rung of a variable of declared width ≥ 2, the result is necessarily incomplete or non-uniform
on that variable, hence non-convertible.** So "lift more" moves rows *out* of the convertible
class. D-0049's instinct was right; this is the reason, and it is sharper than D-0049 stated.

### The recommendation, and what is open

**Keep `to_linear_row` as it is, and stop using it as the clause path's gate.** It is the
honest predicate for "is this PB row literally a linear row over the box", and on the objects
it was designed for it succeeds 95% of the time. It is being *used* as a universal test of
"can this learned object propagate", which it is not.

1. **OPEN — needs its own record.** Give the clause path a clause instance over order
   literals (watched literals over `Lit.t`). It would convert 88 clauses from proof-only to
   propagating against 13 today, and touches neither `to_linear_row` nor `explanation.ml` nor
   the minimiser. **But it spends D-0044's central bet — "no new propagator family" — which
   has held three times.** The half-rebuttal is that `lib/core/prop/bool_clause.ml` already is
   a clause propagator, so this may be a *widening* of an existing family rather than a new
   one. That argument has to be made, not asserted. **Not decided here.**
2. **Do not relax `to_linear_row` to entailment.** Sound, tempting, and strictly weaker than
   (1), plus it costs a new `Justify` obligation to derive the relaxed row via the ladder rows.
3. What is **not** defensible is the status quo unexamined: 75 of 88 learned clauses are
   proof-only, and the backjump they justify re-derives the conflict they came from — which is
   M2-L3's own stated regret (`lib/core/learn.ml:212`).

### M2-L7 (`Saturate`) is NOT the next row

D-0047's chain promoted it conditionally on M2-L11 failing to produce non-degenerate rows.
**M2-L11 succeeded**, so the condition was never met. Worse for it: saturation
(`cᵢ := min(cᵢ, d)`) is **uniformity-preserving**, so it cannot rescue a refused row — the
refused rows are refused for missing rungs or mixed coefficients, neither of which saturation
undoes. It changes nothing in the taxonomy above.

If it is taken anyway for coverage, scope it narrowly: the constructor plus the `Reduce.t`
plug, with a **pinned prediction in its record that no suite `pb-*` figure moves**, and a test
asserting that prediction rather than a benchmark hoping for a win.

## D-0051  A learned constraint has one owner, and retention is dominated by keeping everything

**Status**: **ACCEPTED**, implemented by M2-L4 (2026-09-18, agent-del), `lib/core/retention.ml`.
Two decisions in one record because the second only makes sense given the first.

### 1. Ownership: `Retention` owns a learned constraint's lifetime, alone

`Writer.wipe_level l` deletes exactly `{id | tag(id) >= l}` and is the only bulk deleter in
the tree. A learned id is tagged **0** — `Learned.introduce` and `Pb_analysis.introduce` both
emit inside `Justify.with_level ctx 0`, which moves the level for real so the tag and the
proof agree (I-X3). Levels are non-negative, so only `wipe_level 0` could reach a level-0 tag.

**`Writer.wipe_level` now refuses `l <= 0`** with an `invalid_arg` naming `Retention` and
`Trace`. That is an API narrowing and it is the point of the decision: previously single
ownership held only because `Search`'s four call sites all happen to pass a decision level. A
fifth passing 0 would have deleted every learned constraint on the page — **silently from our
side**, because a second `forget` is a no-op and the I-X2 audit cannot witness it, and loudly
from the checker's, a long way from the mistake.

### The collision that would really have happened was not the one D-0045 predicted

D-0045 warned of a **two-owner** collision: the backjump and the policy both deleting. The
real one is **one-owner**. `Search.solve` retired learned ids from `stats.learned_rev` —
*every id ever introduced* — so a policy that evicts mid-search while that list is swept
double-deletes from a single owner. D-0045's warning does not cover that shape.

`learned_rev` is now an audit trail only; the sweep is `Retention.retire_all`, which deletes
what the database **holds**. Measured by restoring the old sweep: **18 of 65 checks redden and
the checker rejects** — *"Trying to access constraint with ID 16 that has already been
deleted"*.

### 2. The policy is `keep_all`, and that is a result

The machinery is built, named, swappable and exercised (`BAGUETTE_RETENTION=off|fifo:N|lbd:N`
keeps the sweep re-runnable). It is **off because the measurement says off**, which is what
the row asked for — a policy justified by a measurement, not a citation.

- **Activity is the constant zero.** Nothing propagates a learned constraint:
  `Learned.instance` builds a `Linear` instance and **has no caller in `lib/`** (verified
  independently). So an activity policy over a constant is FIFO, and `Retention.fifo` is that
  policy under its honest name.
- **LBD is degenerate here too**: over 39 models, **72 clauses at LBD 1, 16 at LBD 2, none at
  ≥ 3**. Glucose's glue exemption would retain 100% of that, so it is deliberately not
  implemented.
- **The cap sweep on `width_sat_depth`** (73 learned constraints), reproduced independently by
  the orchestrator:

| policy | evicted | `.pbp` bytes | `del` rules | checker |
|---|---|---|---|---|
| `off` | 0 | 48145 | 124 | VERIFIED |
| `lbd:16` | 57 | 48658 | 181 | VERIFIED |
| `lbd:0` | 73 | 48793 | 196 | VERIFIED |

**Eviction monotonically increases proof bytes and `del` rules.** Every policy is dominated by
keeping everything. A ~10% verify-time slowdown was also measured, but at a ~15 ms workload
that is weak evidence and **the decision does not rest on it** — the deterministic columns
carry it.

At the default, all **117 artefacts across 39 models are byte-identical** to the pre-M2-L4
binary, with the two binaries genuinely different (`ae157416` → `05aaf5c4`).

### What would reverse this

The verdict is a fact about **this suite**, not about retention. It reverses when a learned
constraint is actually propagated — i.e. when the clause path gets a runtime instance
(D-0050's open question). At that point activity stops being constant, eviction starts saving
propagation work rather than only adding `del` lines, and the sweep above must be re-run
before `keep_all` is defended again. **Do not cite this record as "retention does not help";
cite it as "retention does not help while nothing propagates a learned constraint".**

Note also that the proof verifies at **every** cap including `lbd:0`, so nothing in it depends
on a learned constraint staying live. That is consistent with the zero citations and is why
eviction is safe here at all; it would not be in a solver whose later `rup` lines lean on a
learned unit.

## D-0052  A clause over order literals is a WIDENING of `bool_clause`, not a new family — and watched literals are a separate question

**Status**: **the analysis is ACCEPTED; the implementation is NOT scheduled here.** Produced
2026-09-18 by a read-only study (agent-clause, wave seventeen) answering the one question
D-0050 left open, and verified in the tree by the orchestrator. D-0050 recorded that this
argument "has to be made, not asserted". It is made here.

### Verdict: widening. D-0044's bet is not spent

Three checkable facts decide it:

1. **The explanation side is already generic.** `Explanation.Clause of Lit.t list`
   (`lib/core/explanation.ml:110`) is over `Lit.t`, not over Booleans — verified.
   `Justify.validate_lits` (`justify.ml:277-286`) checks only that a literal's owner is a
   declared variable, nothing about the threshold. `Bool_clause` reaches this generic
   machinery through `Lit.bool_true`/`bool_false` (`bool_clause.ml:118`), which are literally
   `Lit.ge x 1` / `Lit.le x 0` — the **threshold-1 instance of a general constructor**.
2. **`bool_clause.ml` is specialised, and every specialisation site is a constant
   substitution, not a structural assumption**: the literal record omits the threshold
   because it is always 1 (`:104`); `status` tests `lo >= 1` / `hi <= 0` (`:198-204`);
   `assign` sets 1 / 0 (`:229-242`); `falsity_fact` hardcodes `~decl:1 0` / `~decl:0 1`
   (`:185-187`); `make` rejects any variable not declared `[0,1]` (`:147-153`, verified). All
   five become `k` / `k-1` with a declared-bounds lookup. `Store.set_lo/set_hi` and
   `Reason.at_least/at_most` already take arbitrary values.
3. **No new `Explanation` constructor and no new `PROOF-FORMAT` §4 row.** `Clause` already
   exists and already renders to `rup`.

### The refinement that matters: D-0050 bundled two separable things

**Watched literals are NOT part of the widening, and should be dropped from the proposal.**
`bool_clause` has no watches today (`survey_from`, `:212-218`, is a full walk with early
exit), and **no propagator in `lib/core/prop/` has a single `mutable` field** — verified by
grep, the grep returns nothing. Watch pointers would be the first search-dependent mutable
propagator state outside `Store`'s undo trail. That is a genuinely new thing, it is a
data-structure optimisation **orthogonal** to the widening, and at this suite's clause widths
it buys nothing. Decide the widening; leave watches alone.

### The real cost: the declared consistency level drops, and that is the honest counter-argument

`Bool_clause` declares `Domain` (`:112`) on an argument its own header spends nine lines
making (`:12-20`): for a clause, unit propagation *is* domain consistency, because **"Booleans
have no interior"**. Order literals over integers **do**. `bool_clause.ml:120-128` leaves a
variable occurring at both polarities alone because "the clause is then a tautology" — true
for `b ∨ ¬b`, **false for `x≤1 ∨ x≥3`**, which is a hole. And `Learn.minimise`'s `slot`
(`learn.ml:154-155`) keys on `(variable, polarity)`, so opposite-direction pairs survive
minimisation **by design**. This is not hypothetical: at least **9 learned clauses of width
≥ 3** carry an opposite-direction pair on one variable (width ≥ 3 excludes `Ne` hole lines,
which are exactly width 2), so it is roughly 10% of real traffic.

So the honest declared level for a clause over order literals is **`Bounds`**, not `Domain`.
Chasing the hole instead would need `Store.remove_with_facts`, of which I-X10 records `Ne` is
the **sole** caller in `lib/`, and would trip D-0019 point 3. Do not.

**The strongest case against this record's own verdict** is exactly that: a widening that
cannot preserve the widened module's declared level is arguably not one, and
`bool_clause.ml`'s central soundness argument has to be rewritten. The reason the verdict
stands anyway is that the alternative is worse — two modules sharing nothing is the "second
implementation to keep in step" that `bool_clause.ml:284-286` explicitly refuses for
`Array_bool_or` et al. **One module, one clause semantics, declared honestly at `Bounds`,
with `Bool_clause` retained as a sub-module that declares `Domain` because its `[0,1]`
restriction makes that true** — the `Ne` / `Ne.Int_ne` pattern the same file already uses at
`:271-322`.

### A new obligation this creates, and it lands on D-0051

A trace line from a learned-clause instance is RUP-in-sequence against the learned constraint
on the page — the same shape as I-X10's existing `Bool_clause` entry, not the Hall/Régin shape
it refuses. **But it is RUP only while that learned constraint is LIVE.**

Today nothing propagates a learned constraint, so retention policy and propagator set are
independent — and **D-0051 was written on exactly that independence**. If a learned
constraint gains a registered instance, retiring it silently stops every subsequent trace line
from that instance being RUP. **D-0051's "what would reverse this" section anticipated this;
this record is the other half of that link.** Whoever implements the widening must revisit
`Retention` in the same change, not after it.

### Recommended sequencing, if it is taken

1. **Apply unit learned clauses as level-0 bound tightenings first.** A unit 1UIP clause has
   backjump level 0 — it is a permanent global bound tightening and needs **no clause
   propagator at all**: no watches, no survey, no two-open logic. Its justification is the
   existing `Clause` `rup`. This appears to capture the large majority of the 75 proof-only
   clauses for a small fraction of the work, and it requires none of the consistency-level
   argument above.
2. **Then widen `bool_clause` to a threshold** for the multi-literal remainder, declaring
   `Bounds`, keeping `Bool_clause` as the `Domain`-declaring `[0,1]` sub-module.
3. **Not watched literals.** Max observed clause width is 4.

### Figures, and which of them you may rely on

**Confirmed independently, suite-wide over 39 models**: `learned 88`, `convertible 13`,
`pb-learned 38`, `pb-fallback 50`, `pb-convert 36`, `pb-nondeg 28`, `pb-stronger 36` —
matching D-0050 exactly.

**PROVISIONAL, do not build on it**: the clause-width histogram behind step 1 ("roughly 70 of
88 learned clauses are unit") is ±5, extracted by parsing level-0 `rup` lines out of proof
text, which also catches `Ne` hole lines and other level-0 `rup`s. The study said so itself.
An independent cruder parse by the orchestrator measured a **different population** (all `rup`
lines including trace chains) and therefore neither confirms nor refutes it. **Re-derive this
from an instrumented run before step 1's priority is defended on it.** The `≥ 9 opposite-pair
clauses of width ≥ 3` figure *is* exact, being a lower bound that excludes hole lines by
construction.

**One claim in the study was wrong**: it reported `CLAUDE.md`'s module map as saying "34 .fzn
models". At its own base commit that map already said **39**. Checked rather than relayed —
which is the standing rule here, and it applies to a study's incidental observations as much
as to its headline.

## D-0053  Reification has two doors, and `red` is vacuous over a contradictory database

**Status**: **ACCEPTED**, implemented by M3-T1 (2026-09-18, agent-reify). Two findings in one
record: the first is a design rule, the second is a **hole in the sole oracle** and reaches
far beyond M3.

### 1. The two doors, and which one is forced

A reifier is an ordinary order-encoded bool (D-0007). Its definition against a condition
normalised to `Σ aᵢlᵢ >= k` (all `aᵢ > 0`, `A = Σ aᵢ`) is exactly two rows:

```
FWD   b -> C     Σ aᵢ  lᵢ + k·~b        >= k          witness  b -> 0
BWD   C -> b     Σ aᵢ ~lᵢ + (A-k+1)·b   >= A-k+1      witness  b -> 1
```

Both big-Ms are the smallest that work; a larger one is sound but weakens what a propagator
can cut from the row, and "one too small" is a pinned rejection lane. `reif_rows` is **pure
and shared** by `add_reif` (eager, `.opb`) and `define_reif` (lazy, `.pbp`), so the two doors
cannot disagree about the encoding.

> **`red` cannot give a model-declared reified bool its meaning.** `red` preserves
> satisfiability *of the database*. If `b` already occurs in a loaded row, the witness
> `b -> 0` must discharge that row under substitution, and for a model that genuinely
> constrains `b` it cannot. **Measured, not argued**: the checker rejects such a case on
> *"Proofgoal 3 could not be autoproven"*, and goal 3 **is** the model row the witness failed
> to discharge.

So `define_reif` carries a freshness precondition (`Reif_not_fresh`, raised before any line is
written), and model-stated reification — `int_le_reif` and friends — goes through the `.opb`
door. `red` is for conditions **the model never named**: the ones a propagator wants to carry
as a single literal after the `.opb` was already written.

### 2. `red` is vacuously accepted over a contradictory database — and this is not an M3 fact

**Reproduced independently by the orchestrator on veripb 3.0.2**, on hand-written two-line
fixtures, because it is the kind of claim that must not rest on one agent's test:

| the `red` line | over a **satisfiable** `.opb` | over a **contradictory** `.opb` |
|---|---|---|
| witness that does **not** discharge its claim | rejected, `Proofgoal #1 could not be autoproven`, exit 1 | **`s VERIFIED`, exit 0** |
| **no witness at all** | `Warning: A witness must be specified for the red-rule`, then rejected, exit 1 | `Warning: …`, then **`s VERIFIED`, exit 0** |

Two consequences, and the second is the dangerous one:

- **"veripb accepted the `red` line" is not evidence unless the model is satisfiable.** A
  redundance goal discharges trivially from a contradictory database, so *every* witness is
  accepted there, including a wrong one. M3-T1's acceptance lanes were reshaped onto a
  satisfiable model after its first attempt found exactly this, and the vacuity is pinned as
  its own passing check so it cannot quietly stop being true.
- **A missing witness is a `Warning`, not an error.** Combined with the row above: **a `red`
  with a missing or misplaced witness, emitted after the search has already derived a
  contradiction, is accepted with nothing but a line on stderr.** Nothing in this project
  reads the checker's stderr warnings.

**This is a standing caveat on any future `red` emitted during search**, not a quirk of M3.
D-0046 made veripb 3.0.2 the sole oracle and accepted that a bug in it is invisible here; this
is the same shape one step out — a *silence* in it is invisible here. Any row that emits `red`
after a conflict must justify itself by something other than the checker's acceptance.

### The related trap, and why the wording is what gets asserted

`Opb`'s own comment (`opb.ml:74-75`) records that VeriPB 3.0's `red` ends at the **first `;`**,
so the witness must come before one: `red <body> : <witness> ;`. `Writer.red` emits that shape
by construction. A witness after the `;` is therefore not a witness — and by the table above,
what happens next depends on the database rather than on the mistake. **An exit status cannot
tell a judgement from a parse error** (M2-T14 found four lanes green for exactly that reason),
which is why these lanes assert the checker's wording at full strength.

### What M3-T2 inherits

**Can**: name any linear `Σ aᵢxᵢ <= c` over declared variables with one literal, mid-search,
and cite `reif_fwd`/`reif_bwd` in a `pol`. All five M3-T4 dispatcher cases over a `<=`
condition are cutting-planes steps over exactly these two rows.

**Cannot**: `int_eq_reif` / `int_ne_reif` are **not one pair** — `b <-> (Σ = c)` needs
`p <-> (Σ<=c)`, `q <-> (Σ>=c)` and `b <-> p ∧ q`. `reif_rows` gives `p` and `q`; **the
conjunction channelling is deliberately not built**, and where `p`/`q` live is an open choice.
Nor is anything wired into search yet: `ensure_direct`, the pattern this extends, has **no
production caller today**, and a reifier registry needs an `Encoding.t` and a `Writer.t`
together at pruning time — `justify.ml:146` is the only place in core that already holds a
writer.

## D-0054  A proof line and a propagation explanation are different objects, and this project has been building one of them

**Status**: **ACCEPTED as a framing; it re-scopes the M2L sequence.** Raised 2026-09-18 by
the user, who put it in one sentence: *PB lines for proof logging are different from PB
explanations for solving — the first must be complete and sound, the second must be useful to
propagation.* This project has not made that distinction, and three results in the M2L
sequence are that omission showing up as measurements.

### The two objects

| | **proof line** | **propagation explanation** |
|---|---|---|
| answers | why is this pruning *valid* | what should the solver *do next* |
| criterion | sound + complete; the checker accepts | **conflicting under the live assignment**, and it prunes after the backjump |
| must be | citable (`r_cid`), static | as strong as possible; need not be citable, need not be static |
| lives in | `.opb` / `.pbp` — `pol`, `rup`, `red`, `ia` | the engine, as a propagator instance |

### The codebase builds the first and calls it the second

`Propagator.pb_row` (`lib/core/propagator.ml:61-83`) is explicitly a **proof** object, and its
own comment says why:

- `r_cid` is **required** — *"a row nobody can cite is a row no `pol` can be built from"*.
- it is *"**emphatically not** a function of the store because it reads live domains"*; it
  reads the **declared** bounds frozen at `make` time, because *"a row that moved with the
  search would be the wrong side of I-X6"*.

Both are correct for proof logging and disqualifying for propagation: propagation strength
lives in the **live** domain at the moment of pruning. PB conflict analysis resolves over
these rows, so what it learns is a proof object — and `Learned.to_linear_row` then decides
whether it may propagate by testing an **algebraic identity over the declared box**. D-0050
called that *"the right predicate used as the wrong gate"* without naming why it is the wrong
gate. This is why: **a proof-side test is standing in for a solving-side one.**

### Three results that are this omission, reinterpreted

- **The PB analysis derives the empty contradiction** (M2-L6): *"strictly stronger than the
  clause — it entails it — but degenerate as a propagation result."* That sentence **is** the
  distinction. It was filed as a defect in the analysis; it is a category error in the
  objective. Sound and complete for the proof, worthless for propagation.
- **The ladder lift** (M2-L11, D-0049) exists because the strength that makes `Linear` prune
  lives in the **live** bounds (`lo(b) = 4`), while the row cited in the proof is frozen at
  declared bounds. The lift smuggles live information into a static row. That is the
  conflation showing up as labour.
- **Learned clauses now propagate and change nothing** (M2-L12). Measured: with learned-clause
  propagation on versus off across all 39 models, the search visits **231 nodes either way**,
  prunes **0 times** from a learned constraint, and emits **byte-identical proofs** (95332
  bytes). A clause is the degree-1, static, citable case of a PB row — a **proof-logging
  shape**. Making a proof shape propagate achieved nothing, which in hindsight is what it
  should have done.

Note that **D-0026's split is a different axis**: `Reason.t` (which facts justify) versus
`Explanation.t` (how the checker is convinced). Both are proof-side. The proof/propagation
split has never been made in this tree.

### Why 1UIP and clauses are the default, which was never decided

D-0044 fixed the learned object as a PB inequality with the clause as its degree-1 case. The
clause path arrived as M2-L3 *"fork (ii), proof-only"* and D-0044 made it a **permanent**
fallback. But the fallback rate is **50 of 88 conflicts**, and per D-0050 most of those are
not PB analysis failing — `Propagator.pb_row` is `None` for `bool_clause`, `array_bool_or`,
`bool_eq`, `bool_not` and `int_ne`, so there is no row to resolve against at all. **Clauses
dominate because the PB side is unimplemented for half the constraint families**, and 1UIP is
the SAT-shaped criterion that came attached to the clause path.

The tree already half-knows 1UIP does not transfer: `pb_analysis.assertive_slack` cites Le
Berre et al. for *"assertiveness gives no backjump guarantee over PB"*, and the clause path
uses a 1UIP cut regardless.

### The inspiration for the solving-side object: RoundingSat (Wietze Koops' line of work)

`lib/core/reduce.ml`'s header **already states the key idea**, and confines it to the analysis:

> adding two PB rows does not in general keep the result conflicting: the resolvent's slack
> can go non-negative and the analysis then has nothing left to learn from. The fix, **from
> RoundingSat on**, is to REDUCE the reason first — derive a weaker-but-conflict-preserving
> row in which the resolved literal has coefficient 1 — and then resolve.

**"Conflict-preserving" is a solving-side criterion, not a proof-side one.** RoundingSat's
rounding is chosen to keep the constraint *useful*, and that is exactly the property a
propagation explanation must have. Already cited here and now load-bearing rather than
background:

- **Elffers & Nordström**, *Divide and Conquer* (IJCAI 2018) — division, and why it beats
  saturation exponentially (`DECISIONS.md:2649`).
- **Koops, Le Berre, Myreen, Nordström, Oertel, Tan & Vinyals**, *Practically Feasible Proof
  Logging for Pseudo-Boolean Solvers* (CP 2025) — RoundingSat and Sat4j under VeriPB with a
  CakePB backend (`DECISIONS.md:2677`). Read for the **emission** side previously; it should
  now be read for how RoundingSat keeps a learned constraint propagating.

`Reduce.division` and `round_to_one` are therefore already the right machinery pointed at the
wrong end of the pipeline: they preserve conflictingness **during** analysis, and then the
result is handed to a proof-side gate to decide whether it may propagate.

### AMENDED 2026-09-18, same day: the third result was the INSTRUMENT, not the framing

The framing above stands, and one of its three pieces of evidence does not. M2-L12's zero —
learned clauses propagating and changing nothing — was read here as "a proof shape made to
propagate, so of course it achieved nothing". **That reading was at most half right.**

M2-L14 built models on which learning can show, and the same ablation now moves hard:
`php_wide_unsat` **297 nodes with propagation on against 1439 off, 4.85×**; `php_unsat`
2.23×; `php_escape_sat` 2.06×. The control is what makes it evidence: **the 39 models that
existed when M2-L12 was measured total exactly 231 nodes on both sides, and not one of them
moves.** The old suite was structurally incapable of showing learning — its largest search
was a 99-node width spine and everything else was ten nodes or fewer.

So: **learned-constraint propagation was already worth up to 4.85× and nothing in the tree
could see it.** The clause propagator M2-L12 delivered is doing real work.

**What this does and does not change.** It does **not** rescue the proof-object/solving-object
distinction from being real — `pb_row` is still frozen at declared bounds for I-X6 reasons,
`to_linear_row` is still an algebraic identity over the declared box doing a solving-side job,
and M2-L13 is still the right row. What it changes is the *expected size of the prize* and the
reason to believe it: the solving-side object is worth building because the weaker, proof-shaped
version of it is already worth 4.85×, not because the proof-shaped version was worthless.

**And the transferable lesson is about measurement, not about PB.** A null result from an
instrument that cannot produce a positive is not a null result. This one survived a full wave,
a merge, and a decision record before the user asked whether the examples were hard enough.
Before reporting that a mechanism does nothing, show that the measurement *could* have shown
it doing something.

### The fix

**Propagate the learned PB row as a PB constraint over order literals, and delete
`to_linear_row` from the propagation path.** The conversion back to an integer linear row
exists only because D-0044 bet "no new propagator family". A counter/slack-based PB propagator
over `Lit.t` is what a PB solver has, the order encoding (D-0028) means those literals already
exist, and the clause propagator delivered by M2-L12 is its **degree-1 case** — which is what
D-0044 said the type relationship was all along. The proof obligation is unchanged and already
discharged: the row is on the page as an `ia` line with its `pol` derivation behind it.

Sequenced as **M2-L13**, and **it supersedes the "register the convertible rows" idea**, which
would only have propagated whatever the proof pipeline happened to emit.

## D-0055  D-0044's "no new propagator family" bet is lost, deliberately — and the slack rule must read the ladder

**Status**: **ACCEPTED**, implemented by M2-L13 (2026-09-18, agent-pbprop), `lib/core/prop/pb.ml`.
This overturns a recorded decision on evidence, so it says plainly what was bet, what was paid
and what was bought.

### The bet, and why it is now paid

D-0044 fixed the learned object as a PB inequality with the clause as its degree-1 case, and
bet that **no new propagator family** would be needed: a learned row would be instantiated as
a `Linear` instance via `Learned.to_linear_row`. The bet held three times (M2-L5, M2-L6,
M2-L11 each left `explanation.ml` untouched) and D-0052 confirmed the clause widening did not
spend it either.

**D-0054 is what breaks it.** `to_linear_row` is an algebraic identity over the *declared*
box — a proof-side test — and it was standing as the gate on whether a learned row may
propagate. Removing a proof-side gate from the solving path means propagating the PB row **as
a PB row**, and that is a propagator family.

`lib/core/prop/pb.ml`: counter/slack over `Lit.t`, **reads live domains** (the whole point —
the proof row stays frozen and citable, the solving object does not), declares `Bounds`, no
mutable state, no watched literals. `Learned.to_linear` and `Learned.instance` are **deleted**;
`to_linear_row` survives only as a MEASURED-ONLY counter.

### What it bought, measured and independently reproduced

Nodes over the 44-model suite:

| | learning off | clause propagation (M2-L12) | **PB propagation** |
|---|---|---|---|
| all 44 | 2265 | 847 | **479** |
| the old 39 | 231 | 231 | **179** |
| `php_wide_unsat` | 1439 | 297 | **77** |
| `width_sat_depth` | 99 | 99 | **53** |

`php_wide_unsat` is **18.7× end to end**. And the "231 either way" figure that M2-L12 pinned
on the old 39 models — the one that motivated M2-L14 — **moves, to 179**: the `int_lin_eq`
models where the empty contradiction finally has a consumer. So the old suite was not entirely
inert; it was inert *to clauses*.

**Test (a), which M2-L6 looked for and did not find, is answered.** `2·[a≥1] + [b≥1] + [c≥1] ≥ 2`
with `a` fixed to 0: slack 0, both remaining coefficients beat it, **both forced**. The clause
`a ∨ b ∨ c` over the same literals on the same store moves nothing. On real solves: **207 PB
prunings** over the suite where the clause path measured 0.

### The refactor is behaviour-preserving, and that is evidenced not asserted

`clause.ml` is now literally `type t = Pb.t` with `propagate == Pb.propagate` — the clause is
the degree-1 **face**, one implementation, which is the relationship D-0044 asserted all along.
With learning propagation **off**, all 44 models emit byte-identical `.opb`, `.pbp`, stdout and
stderr against the previous `main`, with the two binaries genuinely different (`78e1f187` vs
`dc78e99a`). A comparison whose sides shared a binary would have been no evidence at all.

### The second finding: the plain slack rule is ladder-blind

**The textbook slack rule prunes 0 times on integer variables suite-wide.** `width_sat_depth`'s
rows are `+2 a_ge_1 … +2 a_ge_99 >= 98`: slack 100, and no coefficient exceeds 2, so nothing is
ever forced.

Read **with the ladder** it is a different constraint. Falsifying `[x≥3]` falsifies `[x≥5]`
with it (D-0028), so **a rung's effective coefficient is the suffix of its variable's rungs,
not its own** — and the row then says `a ≥ 49`. That is where `width_sat_depth`'s 99 → 53 comes
from.

This is the ladder insight of M2-L11/D-0049 arriving on the **solving** side: the strength was
never in the row alone, and a PB propagator that ignores the order encoding is measuring the
wrong slack. It costs nothing in the proof — still one `rup` — because the extra inference is
the **checker's own unit propagation over the ladder rows**, which are model rows retired by
nothing.

### Consequences to carry

- **`Retention`'s "activity is the constant zero" argument is spent for the second and last
  time.** `keep_all` now rests on M2-L12's argument alone; an activity policy is computable
  and unwritten. Do not cite D-0051's original reasoning again.
- **`cfg.pb = off` is no longer a proof-side-only switch.** Turning the PB path off now changes
  the search, not just the emitted derivation.
- **Backjumping still rests on the clause's decision closure** (`pb_analysis.ml:757`), whose own
  note said "a PB row that propagates at runtime would change that calculation". It does now.
  That question is open and is the natural successor row.

## D-0056  The backjump rests on the decision closure, and a PB row cannot supply one

**Status**: **ACCEPTED, and it closes the question `pb_analysis.ml:757` handed on.** Answered
by M2-L15 (2026-09-21, agent-backjump), verified in the tree by the orchestrator. The short
version: **the decision closure is not the safe candidate among several — it is the only one in
the right currency.**

### Why the question was live

M2-L6 wrote, in `pb_analysis.ml`, that it deliberately does not backjump on the PB row: the
backjump rests on `learn.ml`'s decision closure, "because the levels a derived row names are
not a dependency set any more than a 1UIP cut's are". It then noted that **M2-L13 made the
premise of its last sentence true** — a PB row does propagate at runtime now — so *"that would
change the calculation"* stopped being hypothetical.

### The answer: three different questions, and only one of them is the backjump's

The backjump in this solver is **not** "undo to level B and resume". `search.ml:branch` is a
recursive DFS, and the backjump is the arm `NFail (ng1, cid1) when not (mentions_level ng1 lvl)`:
**a sibling is skipped exactly when the branch nogood does not name that level.**

So the backjump is a **filter on the nogood**, and the nogood is a clause over **decision**
literals that veripb RUP-verifies. Dropping a level asserts *the conflict does not rest on that
decision* — a claim about the decision closure and nothing else.

| | answers |
|---|---|
| `Learn`'s decision closure | which decisions the conflict rests on — **the backjump's question** |
| `Pb_analysis.levels` | at which levels this row's literals became falsified |
| `asserting_level` | how far down the row still propagates — Le Berre et al.'s subject, the one with **no** backjump guarantee over PB |

Neither of the last two is a rewording of the first.

### The levels differ, and in the dangerous direction — measured

Over the 44-model suite, independently reproduced by the orchestrator:

| | conflicts |
|---|---|
| both analyses produced a set | **103** |
| sets equal | 26 |
| **PB set a strict SUBSET of the closure's** | **76** |
| PB set wider | 1 |
| incomparable | 0 |
| PB row is the empty contradiction, level set `{}` | 3 |

**Narrower is the unsafe direction**: filtering by a set that names fewer decisions drops
literals the conflict genuinely rests on, licensing a jump that is not justified. The 3
empty-contradiction cases are the limit — filtering by `{}` leaves **the empty clause**. The
single wider case is the clearest picture of the mismatch: `width_sat_depth`, closure `{26}`,
one decision, while the PB row names all 26 levels.

### The break is the evidence, and the checker catches it

With `config.backjump_on_pb` filtering the nogood by the PB set: the tree is **smaller** (20
nodes / 3 skipped against 35 / 0 honest), the answer is still UNSAT, every `Search.stats`
counter is plausible — **and veripb rejects.** A wrong backjump here is a soundness bug that
does not look like one from inside the solver; it looks like an improvement.

Asserted at full strength on the checker's whole sentence, and M2-L15 also widened M2-L13's
existing degree break from the bare fragment *"reverse unit propagation"* — which any other RUP
failure would match — to the same sentence.

### What M2-L13 genuinely did change

The note was right to flag something. A learned PB instance's pruning is an ordinary trail
entry carrying reason facts (`prop/pb.ml:reason_clause`), so `Analysis.analyse ~scope:Everywhere`
resolves straight through it and **the closure already accounts for the row's antecedents**. The
calculation *was* redone by M2-L13 — by the closure walk, without a line of code. What could not
change is which set drives the filter.

### Consequences

- **The measurement ships and is inert.** The default build compares the two sets and acts on
  neither: 479 nodes, 242 decisions, 15 skipped, unchanged and asserted as a control. `lvl-cmp`,
  `lvl-same`, `lvl-narrow`, `lvl-wide`, `lvl-incomp`, `lvl-empty` are on `--stats`.
- **`skipped` moves only on the unsound build.** If a future row makes it move on the honest
  one, that is a real result — and it will not come from this direction.
- **Do not reopen this by observing that the PB row "knows" which levels it depends on.** It
  knows where its literals were falsified. That is the narrower set, and narrower is unsound
  here. The 76/103 measurement is the counter-example, and `lvl-narrow` keeps it live.

## D-0057  Reification: big-M `int_lin_le` rows, one dispatcher, and `int_eq_reif` without `p ∧ q`

**Status**: **ACCEPTED**, implemented by M3-T2 + M3-T4 (2026-09-21, agent-reif). It closes the
two things D-0053 left open and records a test-quality finding that is not about reification at
all.

### The dispatcher (M3-T4)

`lib/core/prop/reif.ml`, 158 lines of which 45 are code. An author supplies three closures —
**enforce-hold / enforce-not-hold / entailment** — all of type `Store.t -> Propagator.result`,
which is the signature of `propagate` itself. So **the author's common piece is an existing
propagator over an existing row, not new code.**

The framework supplies: **the collapse** (reads the reifier once, runs at most one of the
three); **the contrapositive** (an author writes only the forward form — case 3 is case 2's,
case 4 is case 1's); and **the polarity** (`~positive` is the whole of `int_ne_reif`; neither
author mentions the difference).

It declares **no** consistency level and **no** `pb_row`: it has no propagation of its own, and
an instance stands for 2 or 4 rows while `Propagator.pb_row` promises exactly one — the same
answer `Ne` already gives. Prunings are stamped with the **dispatcher's** id, i.e. the builtin
the model wrote.

**Measured cost of a second builtin beyond the first of its kind: 21–22 lines**, none of them
propagation and none of them justification. `int_ne_reif` against `int_eq_reif` is **one
argument**.

### The `<=` author needs no new propagation

`b <-> (Σ a x <= c)` is **two ordinary `int_lin_le` rows** at the smallest big-M:

```
FWD   Σ a x + K  b <= c + K       K  = hi − c
BWD  −Σ a x − K' b <= −c − 1      K' = c + 1 − lo
```

The five cases are two `Linear` instances over them. With `b` fixed each row *is* its side of
the equivalence; with `b` open neither can touch a condition variable — the cushion is exactly
the row's span — and the only term either can push is `b`.

**These are literally M3-T1's rows**, and that is pinned rather than asserted:
`test_reif_big_m_rows` compares the big-M expansion against `Encoding.reif_rows`' pair,
normalised and canonicalised, on four shapes including mixed signs and a domain not starting at
0 — identical, forward and backward. It also means the rows are in the form a propagator can
**cite** (`Linear.pb_row`), which matters to the learning vertical.

### `int_eq_reif` does not need `p ∧ q`, and the argument is two-sided

D-0053 left this open: `b <-> (Σ = c)` seemed to need `p <-> (Σ<=c)`, `q <-> (Σ>=c)` and
`b <-> p ∧ q`. It does not.

1. **Redundant.** Four rows in the `.opb` (`Encoding.add_int_lin_eq_reif`): LE and GE guarded
   to speak only when the reification literal is **true**, plus **A/B —
   `expand_int_lin_ne`'s own pair over its `.opb`-only auxiliary with one extra guard term** —
   speaking only when it is **false**. The conjunction's sole purpose was the direction
   `(Σ = c) -> b`, and **A/B are already its contrapositive** `~b -> (Σ ≠ c)`, as PB rows.
2. **Not reachable as stated.** `p`/`q` would have to be *propagated*, hence *store* variables,
   and `bin/main.ml:390` (`assignment_values`) fails on any solver variable outside the model's
   own. Adding them is a change on the far side of that bridge, not a change in `lib/`.

So `p`/`q` live nowhere, and the four rows live in the **`.opb`** — which D-0053 forces for
model-stated reification anyway, since `red` cannot give a model-declared reifier its meaning.

**No new `Explanation` constructor was needed.** `Combine`/`Weaken`/`Model_row`/`Clause` cover
both authors; `explanation.ml` untouched. D-0044's table holds again.

### The finding that is not about reification: a `pol` nobody cites is decorative

**The first two breaks reddened nothing** — a justification citing the wrong row, and a big-M
one too small, both went unnoticed by the whole model suite.

The cause: with the reifier forced by a `bool_clause`, `Search.rests_on_a_clause` closes the
refutation the D-0022 way with `rup >= 1`, and **every `pol` in the file becomes decorative —
veripb accepts a `pol` whatever it derives.** The four `<=` refutation models were rewritten to
force their reifier with a **unit linear row**, so `conclusion UNSAT` cites a `pol` chain rooted
at FWD/BWD and the citation is load-bearing.

**This generalises.** A model whose refutation rests on a clause cannot test any `pol` the
propagator emits. When you add a propagator and its justification, check that some model
actually *cites* it — a green suite does not.

### A real bug, found by the new branching model

`test/models/reif_eq_branch_unsat.fzn` is **the first model in the suite where a reifier is
decided by branching** rather than settled at level 0. The eq author's all-fixed conflict
recorded only the reifier's fact — copying `Ne`'s `Reason.none` **without `Ne`'s licence for
it** — so the trace line came out as `rup ~b_ge_1 >= 1`: true of the model, and not
reverse-unit-propagable from it. veripb rejected. The reason now carries the fixed-value facts.

### What is still not wired

**Nothing new reaches search, and nothing needed to.** Every row here goes through the `.opb`
door. `Encoding.define_reif` and `ensure_direct` still have **no production caller**, and a
reifier registry would need an `Encoding.t` and a `Writer.t` together at pruning time
(`justify.ml:146`). That gap is unchanged, and now belongs to whoever wants a propagator to name
a condition **the model never wrote**.

## D-0058  A view is a rendering onto its base's literals, not a variable with literals of its own

**Status**: **ACCEPTED**, implemented by M4-T0 (2026-09-21, agent-views), `lib/core/view.ml`.
It answers in the **negative** the question M4-T0's own roadmap row left open — *"each view
needs its own range literals"* — which matters because that premise is what M4-T3 would
otherwise have inherited.

### The decision

A view `s·x + k` (s = ±1) gets **no PB variables of its own**:

```
y = x + 3 :   [y >= 5]  IS  x_ge_2
z = 7 − x :   [z >= 5]  IS  ~x_ge_3     (a lower bound on the view is an upper bound on the base)
```

Both right-hand sides were **already expressible** — `Lit.t` carries a `positive` flag and
`le x v` is `~(x >= v+1)` anyway — so the `.opb` does not change. Measured: all 57 models emit
byte-identical `.opb`, `.pbp` and stdout against the previous `main`, with genuinely different
binaries.

### What decided it

Minting `y_ge_v` costs, **per view and per unit of declared width**: one Boolean, one ladder
rung, and one channelling row tying `y_ge_v` to `x_ge_(v−k)`.

**The ladder rungs are not optional.** `PROOF-FORMAT.md` §3 measured that stripping them
rejects **7 of 20** models, because nothing else makes a trace line RUP. And D-0028 already
measured what declared width does here — a two-variable model at w=999999 emits a **29.8 MB**
`pol` line. **A view is precisely the construct that multiplies that**, and it buys nothing:
the two literal families would then have to be re-related by exactly the channelling that
renaming makes unnecessary.

**Rejected**: fresh literals per view, on that cost — and because the aux-variable failure
M4-T0's row warns about (GCS "silently downgraded every value-pruning propagator behind it")
has **the same shape one layer down**: an object that looks equivalent, costs consistency or
size, and does it quietly.

### One value, two readers

`Lit.affine` in `view.ml` is the same record `Lit.view_ge` and `Encoding.view_ge` render from —
not two copies of a rule. A propagator sees `View.lo/hi/mem/value` (O(1), allocation-free, no
`Domain.t` built on the read path) and prunes with `View.set_lo/set_hi/remove/fix`, which are
the base's ordinary `Store` mutators at the translated bound. The checker sees the **base's**
literal.

**The M2-T9 trap is avoided by construction, not by care**: a view has **no name**, so there is
nothing to sanitise and no table to key on. (`Lit.sanitize` is non-injective; keying on rendered
names is a silent bug, which M2-T9 found the hard way.) Pinned by a test where two bases `a-b`
and `a_b` render the same OPB name and remain distinct literals.

### The finding: two lanes could not see their own break

Worth recording because it is this project's recurring failure and the session caught it in its
own work:

- The **hole** checks ran against a base already narrowed to two values, so every "hole"
  assertion was passing against a **bound move**. The break reddened **0**.
- The **constant-conflict** lane handed in `Reason.none`, under which `Store.conflict` and
  `Store.unattributed_conflict` return the **identical value**. The break reddened **0**.

Both were rewritten — a real interior hole, and a reason carrying a real fact — and both now
redden. **A break that reddens nothing is not a passing test, it is an absent one.**

### Downstream

- **M4-T3 (`array_int_element`) is unblocked.** A 1-based index is
  `View.shift (View.of_var i) (-1)`, pruning `i` directly through `View.set_lo`/`remove` with
  **no channelling step at which to lose value consistency**. No `.opb` change for the index.
- **Newly constrained**: a view's `=` is the **base's** `=`. `Encoding.view_eq` raises
  `No_direct_encoding` naming the *base*, so M4-T3 introduces the direct encoding for the base
  variable, not for the view.
- **Not wired in.** No propagator or front-end path uses views yet — that is M4-T3's work.

## D-0059  The consistency tag is now checked, and today it does no separating work

**Status**: **ACCEPTED**, implemented by M2-T10 (2026-09-21, agent-oracle). The harness is the
deliverable; **the coverage finding is the useful half** and it tells the next two rows exactly
where they are the first real test.

### The harness

`Engine.check_consistency`, called from `propagate`'s Fixpoint arm — **in the engine, not
search**. "At a fixpoint" is a property that loop knows and its caller can only assume, and
search calls `propagate` once per node, so per-fixpoint **is** per-node.

**Semantics come from the propagator itself, at total assignments**, where SPEC §3.2's
*checking* obligation pins the answer exactly. So there is **no second implementation of any
constraint family** — the classic way a consistency oracle rots — and a propagator written
after this file is covered automatically. The dual limitation is stated in its header: a
*wrong* checking verdict is invisible here. That is soundness, and `test_random.ml` owns it.

Support searches run on **scratch stores**, so the audit cannot perturb the search, trail,
reason arena or proof. Gated by `BAGUETTE_CONSISTENCY` (off by default, **+40%** solver time),
with `BAGUETTE_CONSISTENCY_CAP` and a separately-gated trace — separate because M1-T49 forbids
stderr without `--time` and `run_model_tests.sh` enforces it per model. Over-budget scopes are
**skipped and counted**, and the trace says *"a SKIP IS NOT A PASS"*.

### The result, and then the finding

Over all 57 models, uncapped: **286 fixpoints, 8060 instance-checks, 101 456 oracle tuples,
ZERO violations.** No propagator is weaker than it declares.

> **But a probe forcing the `Domain` obligation onto *every* instance, regardless of what it
> declares, also finds zero.** That is not the oracle being blind — it is a property of what
> ships. **Every `Bounds` instance today is a single linear inequality** (`Linear` is
> `int_lin_le`; `int_le`/`int_lt`/`lin_eq`/`int_eq` are all `Linear.t`; `Pb` and the learned
> rows are single PB inequalities), and **for one inequality over finite domains, bounds
> consistency *is* domain consistency** — the support for a value sits at an *end* of another
> domain, never at a hole.

So the `Bounds`/`Domain` distinction **does no separating work on anything currently shipped**.
It starts doing so at a **product, a quotient, or an `all_different`** — that is, at M4-T4b's
`int_times`/`int_div`/`int_abs` and at M4-T1. Pinned as lane 9: **a red there means a `Bounds`
instance has appeared that this argument no longer covers.**

### The lane that proves it tests the declaration, not soundness

`ne.ml` declares `Value` deliberately, and **passes** — as it must. The control: a scene where
`Ne` genuinely is weaker than domain-consistent (`2x ≠ 4` over `x ∈ 0..3`, posted unmerged, so
`Ne` sees two unfixed terms, declines, and `x = 2` survives). **The same instance relabelled
`Domain` — one field of the `Propagator.instance` record, no edit to `lib/core/prop/` — is
caught, naming `x = 2`.** A third lane *measures* rather than assumes `ne.ml`'s header claim
that on **distinct** variables it is stronger than it declares.

### It caught a break nobody built for it

Running the unit suite under the gate fired on `test_engine.ml`'s
`test_hole_wake_starved_is_caught`, a lane that **predates M2-T10** and deliberately starves
`eq_dom` of its hole wake. That lane now asserts the oracle's verdict as a third instrument
beside the I-P2 re-run.

### Normative consequence

**SPEC §3.2 did not say whether `Bounds` meant bounds(Z) or bounds(D)**, and the oracle made
the difference load-bearing. It now says **bounds(Z)**, for two checkable reasons: `GLOSSARY.md`
defines `Bounds` as saying nothing about interior values, which forces it; and under bounds(D)
the harness would report `Linear`, `Int_le`, `Int_lt`, `Pb` and `Bool2int` as violations, **none
of which is a bug**. Tested directly, on a scene where the two readings differ.

### Open, handed on

`reif_lin_eq.ml` declares `Value` for `int_eq_reif` / `int_ne_reif`, so **the oracle is silent
on it by design**. If that level is conservative rather than intended, the harness buys nothing
there — a question for whoever owns D-0057.

## D-0060  `int_times` / `int_div` / `int_abs`: the case split lives in the model, not in the proof

**Status**: **ACCEPTED**, implemented by M4-T4b (2026-09-21, agent-arith), `lib/core/prop/arith.ml`.

### The design

**For each value `v` of the case variable, the `.opb` carries ordinary linear rows guarded by
big-M terms over Booleans defined by the M3 reification machinery.** So every instance *is* a
`Linear` (or a `Reif_lin_le` for the guard definitions), every pruning is `Linear`'s own D-0013
`Combine` over `Explanation.Model_row`, and it cites a row the `.opb` really contains.

**No new `Explanation` constructor, and `justify.ml` unchanged.** `PROOF-FORMAT.md` §4's row for
all three is "as `int_lin_le`". That is the point of putting the split in the model. D-0044's
table holds again.

All three declare **`Bounds`**. The six faces exist only so an instance reports `int_times` /
`int_div` / `int_abs` rather than `int_lin_le` — the `Ne.Int_ne` device.

### Exactness, as measured rather than as first claimed

The propagation test compares a root fixpoint against the enumerated hull, and **it corrected
the module header twice**:

| | claim |
|---|---|
| `int_abs` | **exact** at the declared box and once the sign of `x` is settled. `z >= x` and `z >= -x` do **not** give `z >= 0` one row at a time |
| `int_times` | **sound**; exact once the sign of `x` is settled — while `x` straddles, both sign families are cushioned |
| `int_div` | **sound**; exact once `y` is fixed **and** the sign of `x` is settled. Fixing `y` alone is not enough: with `y = −2`, `x ∈ −7..7` gives `q ∈ −4..4` where the hull is `−3..3` — truncation's asymmetry |

### A trap D-0033 does not warn about

**`Interval.quotient_filter` is *wrong* for `int_div`, and is not called there.** It filters the
exact relation `x·y = z`; for `x ∈ [1,1]`, `y ∈ [2,2]` it returns **empty**, while `1 div 2 = 0`
is a solution. Asserted as a test. `Interval` is used only for the hull rows, never on the
guarded-row path, which does no multiplication or division of bounds at all.

### Division rounding, and why there is no rounding decision to get wrong

Truncation toward zero, remainder taking the dividend's sign (D-0033) — and **the rows never
divide.** `int_div` is stated as `0 <= x − vq <= |v|−1` for `x >= 0` and `−(|v|−1) <= x − vq <= 0`
for `x <= −1`, guarded by `y = v` and the sign.

**Division by zero needs no special case**: at `v = 0` the window `|v|−1` is `−1`, so the row
reads `x <= −1` under `x >= 0` and `x >= 1` under `x <= −1`. Both signs refuted; `y = 0` is pruned
like any other value.

### Two tests that passed while broken, and were rebuilt

Both are the vacuity failure this project keeps meeting, and both were caught by the session:

- **The first pair of UNSAT models was hollow** — the hull rows alone refuted the declared box,
  so one `.opb` line closed each proof and the propagator's own rows were never cited. Redesigned;
  `test_no_single_row_refutes` now pins all three.
- **The first `pol` control passed with the coefficient broken**, because veripb accepts any
  `pol`. Rewritten so the broken instance *conflicts* where the honest row does not and its
  derivation is claimed as `conclusion UNSAT` — the checker then says *"is not contradicting, as
  specified by the hint."*

The strongest lane: against the **real** `.opb` for `−7 div 2`, the truncating claim `q <= −3` is
RUP and **accepted**, while the flooring claim `q <= −4` is **rejected** on the checker's full
sentence. That is D-0033 tested against the artefact rather than against a comment.

### A deliberate divergence from the row

The row asked to anchor the family on **one `is_in_relation` shared with
`Model.check_assignment`**. It was **not** shared: that predicate computes its product with
`Checked`, i.e. the propagators' own arithmetic, and `model.ml`'s `Exact` note refuses exactly
that on D-0029 grounds. The anti-drift guarantee is kept by **enumeration** instead.

### The defect it found in existing code

`Search.solve`'s `NFail` arm sweeps `Writer.live_ids` before its conclusion and says why — **no
`w` retires a level-0 id** — while the `NSat` arm did not. A level-0 pruning whose D-0013
explanation **nests** (a `Combine` citing a trail entry whose own explanation is a `Combine`)
mints intermediate `pol` ids at level 0, and the audit refuses the run with *"constraint id(s)
never deleted"*.

Not an arithmetic defect: **the arithmetic family is simply the first thing in the tree to nest
that deeply at level 0 on a SAT path.** Fixed by the orchestrator — unlike the refutation arm
there is no cited contradiction to spare, since the conclusion is `Sat lits`, so every live id
goes.

The row pinned it as a check that **asserted the bug**, with instructions to **delete rather than
re-bless** it once fixed. It went red on the fix exactly as predicted and was deleted per its own
instruction.

### Still open, and not this row's

**`scripts/check_determinism.sh` does not honour `test/models/PENDING`.** It runs every `.fzn` and
fails on a non-zero exit, so a model listed as an expected failure still turns the determinism
gate red. That is why the reproducer above had to be a unit check rather than a model, and it
means PENDING is **currently unusable for any model that errors**.

> **UPDATE 2026-09-21 (M4-T1, D-0061): the prediction above has landed.** `all_different` is
> in, and the `Bounds`/`Domain` tag now **does** separating work — the oracle is clean at
> `Bounds` and fires on a `Domain` flip with *"z = 1 survives at the fixpoint with no support"*.
> Lane 9's argument no longer covers everything that ships, which is what it was pinned to
> detect.

## D-0061  The Hall derivation: the ADT carried it, and the one place it could not

**Status**: **ACCEPTED**, implemented by M4-T1 (2026-09-21, agent-hall), `lib/core/prop/alldiff.ml`.
`docs/EXPLANATION-REVIEW.md` §3 called this the row where the project's central claim first
becomes falsifiable. **It was not falsified — with one honest exception, recorded below.**

### The claim held: no new constructor

**`lib/core/explanation.ml` and `lib/core/justify.ml` are both untouched.** `Combine`, `Weaken`
and `Model_row` carried a derivation citing many model rows in one tree — exactly what D-0015
built them for and D-0027 permitted. *Anticipation became evidence.*

**`Combine`'s divisor is load-bearing, not decoration.** The m-ary at-most-one is built by
induction as `((m−1)·A + m pairs) ÷ m`, because summing all pairs and dividing by `m−1` gives
degree `⌈m/2⌉`, not `m−1`. `pair_amo` (`alldiff.ml:238`) recovers a per-value at-most-one from
5 ids and `2d`.

**Verified rather than reported**: `conclusion UNSAT : @c32`, and `@c32` really is
`pol @c22 @c23 + @c27 + @c31 + @c18 + @c20 +` — six ids combined — with the checker answering
`s VERIFIED UNSATISFIABLE`.

### Where it creaked, and this is the finding

> **The ADT can *name* a constraint id but cannot *ask* for one.**

A Hall derivation over variables whose bounds have **moved** carries those bounds into the
derived row as literals. Cancelling them needs *"the id of the line that establishes this bound
fact"* — **D-0009's open gap verbatim**, with `Justify.defining_lit` sitting there as the lookup
that still has **no caller**, because nothing in an `Explanation.t` *value* can request one.

Citing the trail entry the way `Linear` does is **not** a substitute: a cited `Linear`
explanation derives a row in the **ladder currency** (D-0010, `ladder.ml`), not the unit
`x_ge_c >= 1` the counting needs.

The stand-in is `Explanation.clause [lit]`, resolved through M2-T9's claim index to the trace
line already stating that bound, minting nothing. **It is sound only at level 0**, and it makes
the derivation rest on a clause — so `Search.rests_on_a_clause` routes that root conflict the
D-0022 way and **the Hall `pol` is decorative for that one conflict** (`alldiff.ml:346`,
`moved_bound_cancels`). Both cases are pinned by tests: `alldiff_hall_unsat` cites the `pol`,
`alldiff_hall_moved_unsat` cites `rup >= 1`.

**This is the concrete, costed case for closing D-0009** that the gap has lacked since it was
opened.

### Two design choices that exist because of earlier findings

**The `.opb` posts `all_different` as pairwise disequality clause rows over order literals, not
big-M rows** — and the reason is not size. It is that the at-most-one recovery must be a `pol`.
A `rup` recovery also works, **and would make every `pol` in the file decorative**, which is
exactly what D-0057 and D-0060 found twice by accident. Applied in advance this time.

**`Trace.derive_ahead`** (`trace.ml:487`) is D-0040's own remedy implemented: a landed Hall
pruning's trace line `rup +1 z_ge_3 +1 x_ge_3 +1 y_ge_3 >= 1` is **not RUP** — measured, the
checker rejected it — and D-0040 says to emit the derivation as explicit `pol` lines ahead of
it. Only `Trace` can. Gated on `Encoding.has_direct`, which over-triggers deliberately rather
than threading a per-entry flag four modules must agree about.

**Cost on pre-M4 proofs: zero.** All 64 pre-existing models byte-identical, with genuinely
different binaries (`ca9ececce6` vs `81c8a6db64`).

### D-0059's prediction lands

D-0059 recorded that the `Bounds`/`Domain` tag **did no separating work**, because every
`Bounds` instance was a single linear inequality — and named `all_different` as where that would
change. **It has.** The oracle is clean at `Bounds` (`all_different_int (bounds) x7`, 0
violations, 0 skips, re-verified here), and flipping the declaration to `Domain` with nothing
else changed makes it fire: *"declares domain but is WEAKER than that: z = 1 survives at the
fixpoint with no support."*

### What this leaves for D-0004, which stays OPEN

- Bounds consistency achieved and oracle-verified; stage 1 only, `propagate` is where M4-T2's
  matching pass sequences.
- The derivation shape, and that **no constructor was needed**.
- **The ADT gap above** — the strongest argument yet for closing D-0009.
- **The Hall *interval* is not chosen for size.** `contained` returns exactly the saturating set,
  so no variable is named that the counting does not need — but the scan is `a` ascending then
  `b` ascending and returns on the first push, so among several tight intervals it takes the
  **lexicographically first, not the narrowest**. That is a size/quality lever nobody has
  measured, and `EXPLANATION-REVIEW.md` §6 says it is exactly where the choice of Hall set is
  the whole game.

### A cost note for D-0028

The direct-encoding preamble is **`3·n·w` `red` lines** (n = scope size, w = declared width):
measured at 3 variables, w=2 → 32 `.pbp` lines, w=8 → 79. `max_direct_values = 100_000` is
unreachable through the CLI because `max_order_width = 10_000` refuses first — but an
`all_different` over a 10 000-wide declared domain would still write ~30 000 `red` lines **per
variable**. **Nobody has decided whether a global should carry a tighter cap.**

## D-0062  M2-L6's PB analysis costs an order of magnitude on width, and that is accepted

**Status**: **ACCEPTED** — a cost decision, recorded because it was invisible for 392 commits
and because two rows guessed at it wrongly before it was bisected (M6-T6, 2026-09-21).

### The measurement

`test/models/width_sat_depth.fzn` carries the comment *"at 99 it is 43 ms end to end"*. That was
**essentially true when written** (18.6–23.4 ms at `83cc658`, the only commit that ever touched
the model, so the comparison is like-for-like across the whole range).

**One commit accounts for the jump: `aacbc8d`, "M2-L6: wire PB analysis into the search."** Its
parent `f93ecd1` added the PB conflict-analysis machinery **without calling it**; `aacbc8d`
turns it on. Found by `git bisect run` over 392 commits, 7 steps, 0 skipped.

**Reproduced independently by the orchestrator, building both commits:**

| | wall, best of 5 |
|---|---|
| `f93ecd1` — machinery present, not wired | **10 ms** |
| `aacbc8d` — wired | **260 ms** |

### Why it is accepted

PB conflict analysis is a **deliberate feature finding real value on this exact model**:
`pb-learned` 24 of 49, `pb-stronger` 24 — rows that propagate where the clause path cannot. And
M2-L13 claws most of the cost back for the shipped configuration: today's default-on figure is
~160 ms against ~590 ms with learned propagation off.

So the sequence is: M2-L6 spent an order of magnitude to make PB rows available, and M2-L13
spent a propagator to get most of it back. **Both halves were worth it, and neither was visible
as a time cost while it happened**, because nothing watched absolute wall clock on this model.

### The part worth carrying

**Two rows guessed at this before anyone bisected it, and both guesses were wrong in the same
direction.** M6-T1 hypothesised that M2-L13's ladder-suffix slack rule under `keep_all` drove
the cost — it named the **mitigation** as the cause. That hypothesis survived into a benchmark
section before measurement refuted it. And it is now **doubly** refuted: the regression predates
`BAGUETTE_PROPAGATE_LEARNED` by **322 commits**, so M2-L13 could not have caused it under any
reading.

`perf` is unavailable on this kernel, which is *why* both attempts reached for a hypothesis.
**When the profiler is missing, `git bisect` is the instrument — it needs no tooling this
machine lacks, and it produced an exact commit in 7 steps.** Reach for it first next time.

### Still owed

`test/models/width_sat_depth.fzn`'s header comment is now wrong by 7–14× depending on the flag.
It is a **cross-session request**, not done here, because `test/models/**` is held by the
concurrent M5 row. Whoever releases it should fix the comment rather than delete it — a figure
with a date on it is how this was caught at all.

## D-0063  A `soli` constraint is discharged by the conclusion and must never be deleted

**Status**: **ACCEPTED**, implemented by M5-T1/M5-T2 (2026-09-21, agent-bb). It extends
`PROOF-FORMAT.md` §5's carve-out and **narrows I-X2's scope**, on measurement rather than
reading.

### Branch and bound is an M2-L12 global unit

A bound found by branch and bound is **exactly** a level-0 global unit. `soli` yields the
strictly-improving constraint that the **checker** builds from the `.opb` objective, and the
single order literal `~obj_ge_v` is RUP against it through the ladder rows. So `type global`,
`global_of` and `apply_globals` are reused unchanged, the solution node is re-entered,
`apply_globals` conflicts because the objective is fixed at an excluded value, and the ordinary
trace / learning / nogood / backjump path does the rest.

**No new `Explanation` constructor was needed.** D-0044's table holds again.

`conclusion BOUNDS 2 : @c32 2`, and the checker answers `s VERIFIED BOUNDS 2 <= obj <= 2` —
verified under **`--force-checked-deletion`** as well as the default, so the lower bound is
genuinely checked.

### The two rules, both learned from the checker

1. **A `soli` must be introduced at level 0.** Emitted at the level the solution was found at, a
   `w` retires it and the checker says *"The claimed upper bound of 2 mismatches the best
   recorded upper bound of 4."*
2. **A `soli` id is not ours to delete.** Deleting one is an **unchecked deletion** — *"Switching
   from stronger to weaker guarantee"* — which verifies with a warning by default and is a **hard
   failure under `-c`**. It is discharged by the conclusion, so `Writer` records these ids apart
   from the live set and I-X2's audit stays exact.

### It is not a restart, and that is asserted rather than argued

SPEC §3.4 disables restarts and D-0045 asks whether that survives learning. **Branch and bound is
neither a restart nor a re-solve**: the bound is installed on the node the search is standing on,
which is re-entered once; the decision stack is untouched, no closed level reopened, no decision
re-taken.

Asserted, not asserted-by-prose: **M1-T36's identity `nodes = 2·decisions + 1 − skipped` holds
exactly on the exhausted branch-and-bound tree**, which a re-walked prefix would break. **I-X4**
likewise: constraint ids mint strictly increasing across the whole run, so nothing was rewound.
Backtracking stays deletion, never truncation.

### The decorative-`pol` obligation, and why M5 is structurally safer

Met on real proofs rather than constructed ones: the cited id was read back out of each emitted
`.pbp` and looked up. Three mint shapes across five models — `rup` (ordinary), `soli`
(floor/ceiling), `pol` (infeasible) — each broken, including deleting every improving constraint
as it is introduced, and a satisfiable model where the empty clause the conclusion cites cannot
come from the model rows.

> **M5's own chain contains no `pol`.** The bound is a `rup`, *verified by unit propagation*. A
> wrong one is **refused**, where a wrong `pol` is waved through. That is the opposite footing
> from D-0057 and D-0060, and it is a property of the shape rather than of the tests.

### `obju`: not emitted, and the filed trap is confirmed but its narrowing is NOT

**M5 emits no `obju` at all** — branch and bound tightens a bound on a *fixed* objective and never
updates the objective. A gate asserts nothing under `lib/` or `bin/` calls
`Writer.objective_update`, **and asserts the grep found the definition it looks past**, so it
cannot pass by not looking. It initially did exactly that; its own guard caught it.

`PROOF-FORMAT.md` line 136's trap is **confirmed**: `obju` before any `soli` gives *"Proofgoal #1
could not be autoproven."*

> **Reported but NOT reproduced**: agent-bb reports the trap is narrower than filed — that after a
> `soli` the goal *is* autoproven. The orchestrator's minimal two-line fixture gives the **same
> failure** in both orders. That may be a difference in the fixture (the minimal `soli` sets the
> *worst* objective value, not an improving one, so it may establish nothing useful) rather than a
> wrong report. **The doc keeps its existing warning**, and the narrowing needs a reproducible
> case before it is recorded as measured.

### Still owed to SPEC

- `conclusion UNSAT` is **refused** over a formula carrying a `min:` line; `BOUNDS INF INF` is the
  only conclusion for an infeasible optimisation model. The checker names the replacement itself.
- The objective must be a **variable**: a constant objective is refused, because `conclusion
  BOUNDS` needs a `min:` line and a constant has no order literals.

> **UPDATE 2026-09-22 (M4-T8): the second consumer landed, and it moved a conflict.**
> `element.ml` swapped all four `Explanation.term c (Explanation.clause [l])` stand-ins for
> `Defining`, and `element_moved_unsat`'s `conclusion UNSAT` went from citing `rup >= 1` to
> citing a `pol`. **One artefact changed across 85 models.** Two things that row learned and
> that a third consumer should not rediscover: **`Search.rests_on_a_clause` is not a usable
> signal for the level rule** — it cannot distinguish *"cancelled"* from *"correctly omitted,
> and nothing else happens to be a `Clause`"*, since both give `false`; inspect the forced
> `Combine`'s summand list instead. And **`Defining`'s multiplicity changes the shape of a
> `pol` line** (`@c31 2 *`), so any test that mutates proof text by token must handle a scaled
> summand or it produces a **parse error** rather than the judgement it meant to provoke.

## D-0064  `Explanation.Defining`: the ADT can now ask for a constraint id, and D-0044's table breaks at nine

**Status**: **ACCEPTED**, implemented by M4-T7 (2026-09-21, agent-defid). **This is the first
new `Explanation` constructor since the ADT was frozen**, and `explanation.ml`'s header requires
this record to exist before it. The argument is therefore the substance here, not the code.

### What was missing

**D-0009 says a bound fact in a `pol` needs a constraint id, not a literal.** The ADT could say
only the first half: it can *name* an id (`Model_row`) but could not *ask* for one.
`Justify.defining_lit` (`justify.ml:275`) has existed since D-0009, is documented at `:95` as
*"exactly what D-0009 needs"*, and **had no caller** — because nothing in an `Explanation.t`
*value* could request one.

D-0061 is the costed case. A Hall derivation over **moved** bounds carries those bounds into the
derived row as literals, and cancelling them needs the establishing line.

### The constructor, and why it is a summand

`Defining of int * Lit.t` — *c copies of the id of the line that **establishes** this literal*.

**It is a `summand`, not a `t`, for exactly the reason `Weaken` is**: arithmetic valid only
inside a `Combine`'s sum, not a value anyone can hold. So no `Cut` can take one, `emit` can never
be handed a bare one, and conflict analysis never has to decide what one means alone. The blast
radius is the **7 `summand` match sites**, not the ~20 `t` sites.

**Why nothing existing would do**: `Weaken lits` puts a literal in as the trivial axiom — it
cancels a term and **costs one unit of degree per copy**. A conflict needs the term gone **and the
degree kept**, which only citing the establishing line achieves. The two are the same arithmetic
from the two different sources D-0013 already calls different operations. `Defining` is the half
that was missing, and it sits beside `Weaken` rather than anywhere new.

### Alternatives rejected, including the two that saved earlier rows

- **Name the id from the propagator (`Model_row`)** — the M5-T1/D-0063 move. **Impossible in
  principle**, not merely awkward: the id is `Justify` **claim-index state at emit time**, and the
  propagator has no `ctx`. That is the whole content of *"can name an id but cannot ask for one"*.
- **Put it in the model** — the M4-T4b/D-0060 move. Which bounds the root fixpoint derives is not
  known at model time, so there is nothing static to post.
- **Give `Deferred`'s thunk a resolver, or an ambient pointer on `ctx`.** The second is M1-T31's
  deleted `model_id` returning under a new name; the first changes `Explanation.force`'s
  signature, which `search.ml` and six others call.
- **Restructure so no bound literal enters the row.** `excl` derives `~x_ge_lo(x) ∨ ~x_eq_v`; the
  exclusion genuinely depends on the current bound. D-0061's reading is **confirmed, not worked
  around**.
- **Keep `Explanation.clause [lit]`.** It emits the same bytes at level 0 (measured) — but it is a
  `Clause`, and `Search.rests_on_a_clause` reads the label.

**The property that earns the label**: `Defining` always cites a **unit**, so its cancellation is
**exact**. A `Clause` summand may cite a clause of any width, and its cancellation is not. That is
why a root conflict may rest on a `Defining` where it may not rest on a `Clause`.

### The effect, verified rather than reported

| | `conclusion UNSAT` cites |
|---|---|
| before | `@c102`, which is **`rup >= 1`** — decorative |
| after | `@c96` = `pol @c81 @c84 + @c88 + @c92 + @c64 + @c66 + @c93 2 * + @c94 2 * + @c95 +` |

`@c93`/`@c94`/`@c95` are the one-literal `rup` lines establishing the three moved Hall bounds.
`s VERIFIED UNSATISFIABLE`.

**Blast radius, measured over all 78 models with genuinely different binaries**: exactly **one**
artefact differs. (The implementing session reported this over 44 and understated its own
coverage.)

### It works above level 0, which the stand-in could not

The test is now **per bound, by the level the bound was *established* at** (`alldiff.ml:179`).
A bound the root fixpoint set is a consequence of the model, so its unit line stays true and
citable at any depth; a bound a **decision** set is still not cited. Measured: four `pol` lines
written at level 2 citing a level-0 unit the baseline binary cites nowhere.

### A latent defect, bounded and not fixed

The obvious routing rule (`Defining ⇒ false`) **reddened** `alldiff_hall_trace_unsat`: its
conclusion cites an `int_lin_le` combine that folds in an alldiff entry. That conflict was being
routed away by the **accidental presence of a `Clause`**, not by anything true about it. The rule
is now: a `Defining` at the **top level** is the derivation's own cancellation and the `pol`
closes; **below a `Term`** it belongs to another instance's row and D-0022's route is right — the
same boundary, for the same reason, as `Explanation.top_weaken_owners`.

> **~~The underlying defect is NOT fixed~~ — FIXED 2026-09-22 by M4-T2.** The old rule read the
> *presence* of a `Clause`/`Defining`; what it stood in for is the **currency** the cited row is
> stated in. `Encoding.is_direct_row` now records the ids minted for the direct encoding and
> `Search.mixes_currencies` asks directly — a top-level `Combine` adding an order-currency `.opb`
> row to a direct-currency counting row cited as a `Term` is a sound `pol` that does not close,
> and `Defining` can then say what is true of it. **A model that reaches the case this paragraph
> said nothing reaches is now shipped**: with the currency test disabled, 3.0.2 says *"not
> contradicting, as specified by the hint."*

### What this discharges

D-0009's *"until `Explanation.t` can carry ids…"* consequence is **discharged on the `pol` side**,
and D-0061's *"where it creaked"* section is **answered**. D-0044's no-new-constructor table held
eight times and breaks here, on the ninth — deliberately, with the argument above.

## D-0065  The hardware limits become options, defaulting off — and D-0041's objection is answered, not ignored

**Status**: **ACCEPTED**, implemented by M7-T1 (2026-09-22, agent-unlimit). **Amends D-0041**,
which forbade exactly this, and amends `SPEC.md` §3.1's normative MUST. The argument is the
substance here; the code is small.

### Why

The project was built on a 15 GB laptop and its limits reflect that machine, not the problem.
M7 runs the MiniZinc Challenge corpus on a 192-core / 2 TB node. A refusal calibrated to the
dev box is not a property of constraint programming.

### Three kinds of limit, and only one of them is a flag

M7-T1's brief named two — RAM, and proof-size/checker-time. **The implementing session found a
third and it is the one most likely to be lost:**

| kind | example | option? |
|---|---|---|
| the machine is small | suite `MEM_CAP_KB` | yes — and it is about **gate time on a shared dev box**, not solver capability |
| the artefact may be unusable | `max_order_width`, `max_direct_values` | yes, **defaulting off**, with a diagnostic that always fires |
| **the arithmetic does not exist** | a width not representable as a native int | **NO. Never.** Without it `declare_int` sits in a 2^64 loop |

> **A limit that exists because the machine is small is an option; a limit that exists because
> the arithmetic does not exist is not.**

Someone will read "M7-T1 removed the width limits" and try to remove the third. That sentence is
in `SPEC.md` §3.1 for them.

### How D-0041's objection is answered rather than overridden

D-0041 forbade a run-time knob because *"a knob would make the accepted language
environment-dependent, so two runs of the same binary on the same `.fzn` could disagree about
whether it is a legal model."* **That objection is correct as stated.**

It is answered because **the default is now unlimited**. The accepted language is *fixed and
maximal*; two default runs always agree; the knob can only **restrict**, making it an operator's
self-imposed budget rather than part of the language.

**D-0041's own arrangement was the weaker one on its own terms**: the accepted language depended
on a **compiled-in constant**, so two *builds* could disagree about legality, with no way for a
reader to see which constant was in force. What D-0041 was really protecting — that a reader
must never be unable to tell *why* a model was refused — is preserved, because the refusal names
the limit and says it was asked for.

### The refusal goes; the signal does not

This was the row's central instruction and it was met by **a warning that fires unasked**, not
only a `--stats` counter — *"a counter nobody asked for is a counter nobody reads."* The
threshold is the old cap, 10 000: that number's one remaining job is to mark where the artefacts
stopped fitting in a code review.

The diagnostic explains D-0028 to a reader who has never heard of it — it says what the order
encoding *is*, that a width of w costs w−1 clauses, names the count, and says the proof grows
with the **declared** domain rather than with difficulty. That was asked for explicitly:
"Encoded 4 000 000 ladder clauses" means nothing to someone who has not been told why.

`--stats` additionally reports `ladder` — **the aggregate the per-variable cap never bounded, as
its own comment admitted** — plus `widest`, naming the single variable to narrow first.

### Measured

**85 models × {stdout, stderr, exit code, `.opb`, `.pbp`} = 425 artefacts, 0 differing**, with
genuinely different binaries. Independently re-verified by the orchestrator across the merge
(340-artefact comparison, 0 differing, `6639381e5c02` → `3b1d28efb752`). Removing a ceiling
changed nothing about what an in-bounds model emits.

A width-30 000 model — refused outright before — now solves and **veripb 3.0.2 accepts its
proof**. Verified independently at width 20 000: `s VERIFIED SATISFIABLE`.

### The vacuity gap it found in its own work

**With the cap put back, the shell lane reddened and not one unit assertion did** — because
every unit test sets the limit explicitly, so none observed the *shipped default*. A suite can
test a setting exhaustively and never test what ships. Closed by sampling the refs at module
load, before any test can touch them.

That is this project's signature failure mode occurring inside the row written to prevent it —
the same shape as the width lint's own history, and as D-0058's two blind lanes.

### What did NOT change, deliberately

`scripts/check_test_widths.py` is untouched. It enforces **suite hygiene about gate time**, with
three memory-ceiling incidents behind it. The solver's capability limit was a different thing
wearing the same number, and separating them is what this row is. The over-wide test model lives
in a `mktemp -d` and is deleted; nothing wide is committed.

## D-0066  `rup` is vacuous over a contradictory database, and 26 lanes may be testing nothing

**Status**: **ACCEPTED as a measurement; the audit it demands is M7-T5 and is NOT done.**
Found by M7-T2 (2026-09-22, agent-annot) while building a break lane, and **re-verified
independently by the orchestrator** before recording.

### The measurement

Take `test/models/ne_eq_unsat.fzn`'s honest proof, which the checker accepts. Corrupt one
`rup` line two ways:

| corruption to `@c5 rup +1 y_ge_2 +1 x_ge_2 >= 1` | veripb 3.0.2 says |
|---|---|
| **a literal removed** (`+1 x_ge_2 >= 1`) | **`s VERIFIED UNSATISFIABLE`** |
| **a literal's polarity flipped** (`+1 ~y_ge_2 …`) | **`s VERIFIED UNSATISFIABLE`** |

Both are **accepted**. The reason is not a checker bug: **over a contradictory database
everything is RUP**, because unit propagation reaches a conflict from any claim at all.

> **Any break lane that asserts a `rup` rejection over an UNSAT model is testing nothing.**

### This is D-0053's finding, one rule over

D-0053 recorded that **`red` is vacuous over a contradictory database** — a `red` line is
accepted with a wrong witness or no witness at all. This is the same vacuity for **`rup`**,
and it is the more consequential of the two: `rup` is everywhere in these proofs, and most
models in this suite are UNSAT.

`CLAUDE.md`'s proof-discipline list already says *"verify a `red` over a **satisfiable**
model, or you have tested nothing."* **The same sentence is now needed for `rup`.**

### The exposure, measured but not yet audited

**26 lanes across 9 files** assert a RUP rejection: `test_prop` (4), `test_pb` (6),
`test_trace` (5), `test_learn` (3), `test_matrix` (3), `test_endtoend` (2), `test_proof` (1),
`test_justify` (1), `test_random` (1). Several of those files are dominated by UNSAT models —
`test_prop` mentions `_unsat` 23 times, `test_proof` 9, `test_learn` 8.

**How many of the 26 are vacuous is unknown.** A lane is only vacuous if its corrupted proof
is over a *contradictory* database; a lane over a SAT model, or one asserting a **judgement**
rather than a RUP failure, is unaffected. **Nobody has checked which is which**, and the
number is not guessable — M2-T14 looked for exactly this shape from a different direction and
found four.

**That audit is M7-T5.** It is not done, and this record exists so the gap is visible rather
than implied.

### What a correct lane looks like

M7-T2's own BREAK 2 is the pattern: it flips a unit nogood's polarity over a **satisfiable**
model, and the checker then says *"The constraint is not implied by reverse unit propagation
(RUP)…"* for a real reason. Its BREAK 1 is the other correct pattern — it does not reach the
checker at all, because `Search.branch` refuses the malformed order first, and the lane
asserts *that* wording instead.

### A second-order point worth keeping

**A merely wrong search order is not a proof defect.** Any tree that partitions is refutable,
so a bad order yields a *different* proof the checker still accepts. That is why M7-T2's
obligation (a) asserts on the **decision** — `d_var`, `d_split`, `d_high_first` — and never on
the answer. Two strategies that agree on every test are not tested, and a proof that verifies
says nothing about whether the order was honoured.


### AMENDED 2026-09-23 by M7-T5 (agent-vacuity). The measurement stands. **The inference drawn from it — by me, the orchestrator, in this record's title and in M7-T5's brief — does not.**

**The audit found 0 vacuous lanes of 15.** (The "26" was a grep of the wording string; in those
nine files it has 27 occurrences — 12 explanatory comments, 7 shared wording constants, 8
inline assertion sites — resolving to **15 distinct lanes**. All 15 sound, 0 vacuous, 0
unreachable, every verdict from a run rather than a read.)

**The logical error, plainly.** I wrote that a break lane asserting a `rup` rejection over an
UNSAT model "is testing nothing" and "goes green whether the code is right or wrong". That is
backwards. If a corrupted `rup` line is **accepted**, then a lane asserting **rejection**
goes **RED**. This vacuity cannot hide inside a rejection lane; it makes the lane **fail
loudly**. The failure mode I generalised from D-0053 — where `red`'s vacuity does silently
green a lane — does not transfer, because the two lanes assert opposite outcomes. I did not
check the direction before writing 26 lanes' worth of suspicion into the roadmap.

**And obligation (b) was wrong medicine.** The row instructed that every vacuous lane be
"rebuilt over a satisfiable model". Measured:

| model | `rup` flips accepted |
|---|---|
| `ne_eq_unsat` (UNSAT) | **8 of 8** — total |
| `chain_sat` (**satisfiable**, branches, 0..9) | **3 of 15 still accepted** |

**Vacuity is a property of the LINE, not of the model's answer.** A `rup` line is checkable
only if it is load-bearing for a *later* line; a satisfiable model makes that more likely, not
certain. **A lane rebuilt on my advice alone would have been just as vacuous** — and would
have carried a decision record saying it was fixed.

**What the audit shipped instead**, and it is the better deliverable: a **census in
`test/unit/test_mutation.ml`** — six checks re-measuring both rows of that table on every run
(controls, the total vacuity on UNSAT, the accepted flip on SAT, the refused flip on SAT, and
its full wording). The numbers now redden when they change, rather than the record quietly
rotting. It also raised `test_learn.ml`'s `rejection_wordings` to the checker's whole sentence
— its own comment claimed full strength while the constant matched less.

**Method note worth keeping**: the audit flipped a literal's polarity rather than dropping
one. A **dropped** literal can leave a claim that is genuinely stronger and genuinely implied,
so its acceptance is ambiguous; a **flip** is a different claim, so acceptance is
unambiguous. D-0066's original measurement used both and read them as equivalent.

**What survives unchanged**: the measurement itself, and its consequence for *proof
confidence* — on `ne_eq_unsat` all 8 `rup` lines are uncheckable, so a defect of D-0070's
class is invisible there. That is why D-0068's 1-in-11 rejection rate is a lower bound, and
that reasoning was never affected by the error above. **What is withdrawn** is the claim that
existing rejection lanes were at risk.

Corrected by M7-T5 / **D-0073**. This record's title is left as written, per the append-only
discipline; it is wrong, and this paragraph is its correction.

## D-0067  Keeping constraints high-level: 112 → 300 instances, and a pre-existing RUP defect it surfaced

**Status**: **ACCEPTED**, implemented by M7-T3 (2026-09-22, agent-mznlib). `mznlib/`,
`tools/baguette.msc`. The library is the deliverable; **the defect it found is the more
important result** and is M7-T6.

### What the library buys

Flattening against a library that declares what baguette actually supports, rather than an
empty one that decomposes everything:

| | empty lib | baguette lib |
|---|---|---|
| flatten at all | 301 | 300 |
| **flatten into baguette's subset** | **112** | **300** |
| `all_different_int` rows surviving | **0** | **903**, across 66 instances |

On the **112 instances supported under both** — where nothing new had to be decomposed, so
the comparison is like-for-like — keeping constraints native is a clear win: `2022_sudoku_opt`
**6520 rows → 76** (576 KB → 70 KB), `2013_ghoulomb` 6910 → **162**, `2023_sudoku_fixed`
1474 → **48**.

**The Hall path works end to end**, on a controlled pigeonhole instance: `.fzn` 1412 → 651 B,
`.pbp` 19 532 → 9 435 B, **both `s VERIFIED UNSATISFIABLE`**. That is D-0061's derivation
paying for itself on real input.

### A correction to my own figure

I cited 15 K → 88 K on `accap` as the cost of decomposition. Re-measured: 15 177 → 89 903
(empty) → **89 918 (baguette lib)**. **The library does not help that instance at all** — its
blowup is `diffn`, for which baguette has no propagator, so std's decomposition stands either
way. **The figure is real but it is a propagator gap, not a library gap**, and I had drawn the
wrong conclusion from it.

### The defect: a correct answer whose proof is rejected

`test/models/rup_level0_nogood_sat.fzn` — **nine variables, five constraints, no global at
all.** The solver answers `xs = [1,1,9,1,1,1,2,1,1]`, which satisfies every constraint by
inspection. veripb 3.0.2 rejects the proof at the **level-0 backtrack nogood**:

> The constraint is not implied by reverse unit propagation (RUP) from core and derived
> database.

**Reproduced independently by the orchestrator on `main`.**

**It is pre-existing, and that was established rather than assumed.** The same 2001 fuzz seeds
gave **3 RUP failures with `all_different` native and 5 with it decomposed** to pairwise
`int_ne` — overlapping but not identical sets. So the defect is upstream of the global
entirely, which is why the reproducer above has no global in it.

**This is M1-T44's shape**, which this project once called its highest-priority open defect:
the answer is right, every step looks valid, and the *artefact* is what is wrong. It is
**M7-T6**, and the model is in `PENDING` rather than absent, so it is visible on every run.

> Note the interaction with **D-0066**: `rup` is vacuous over a contradictory database, so a
> rejection like this one can only be *seen* on a **satisfiable** model. This reproducer is
> SAT. A UNSAT instance of the same bug would have been accepted silently.

### A second, degenerate defect

A model with **no variables and no constraints** solves and emits a proof veripb rejects —
*"No solution has been logged in the proof and no solution has been given in the conclusion."*
Both library arms. Degenerate, but real, and it is folded into M7-T6.

### The blocker is no longer width — it is set-literal domains

Of 78 refusals: **20 are set-literal domains**, 16 width. `var {1,2,3,4,5,6,8,9,10,11,12}: x;`
is refused because `Encoding.declare_int` takes only `~lo` and `~hi`. **MiniZinc emits these
routinely**, and neither `--only-range-domains` nor `mzn_opt_only_range_domains` has any effect
in 2.10.1 — the hole-y domains survive verbatim, so **no `mznlib` can work around it**.

`lib/core/domain.ml` already carries holes; the gap is in the *encoding*, not the domain. That
is the single biggest thing between this library and real instances, and it is bigger than the
width cap M7-T1 just removed.

### The refusal counts above are already stale, and the residual wall splits two ways

M7-T3 branched before M7-T1 merged, so **every width refusal it counted is now gone by
default** — M7-T1 made the width limit unlimited-by-default, so those instances should now
flatten *and* run (with the cost warning). The two rows compose, and the measurement predates
the composition. **Re-measure before quoting the 78-refusal breakdown.**

What remains after that is a cleaner split than "the width cap":

- **Set-literal domains on `X_INTRODUCED_*` variables — 20 instances.** Unreachable from
  `mznlib`, and the real remaining wall.
- **Width on the OBJECTIVE variable — ~8 instances** (`multi-knapsack`, `wordpress`,
  `wmsmc-int`, `vrp`, `unit-commitment`, `team-assignment`, `roster-sickness`, `spot5`). The
  objective's declared range is **MiniZinc's own bound on the sum**, so it is wide *almost by
  construction on any optimisation model*.

That second case is worth its own treatment rather than being absorbed into "raise the width
limit". An objective is not a decision variable the search branches on in the usual way — it is
a bound being tightened (D-0063) — so paying full order-encoding width for it is close to pure
waste. Whoever takes it should ask whether the objective needs a ladder at all, not how wide a
ladder it may have.

### What the library deliberately does not define

`int_pow` with a variable exponent, and everything float, are left undefined so the front end
**names them and exits non-zero** rather than the library emitting a wrong decomposition.
`cumulative`, `diffn`, `table`, `regular`, `circuit`, `global_cardinality` have no baguette
propagator, so std's decomposition stands — that is where the remaining inflation lives.

## D-0068  The first full corpus run: 8 proofs verified, and the blocker is not what anyone predicted

**Status**: **MEASUREMENT**, 2026-09-22/23. 436 MiniZinc Challenge instances (every `.mzn`,
smallest data file each), flattened with M7-T3's library, solved by `main` at `b6fa825`, **every
solved instance's proof checked by veripb 3.0.2**. 64-way parallel, 32 GB per job.

### The result

| outcome | count |
|---|---|
| `REFUSED-MODEL` (front end, exit 2) | **248** |
| `TIMEOUT-SOLVE` (300 s) | 87 |
| `FLATTEN-FAIL` | 51 |
| `REFUSED-LIMIT` (exit 3) | 30 |
| `SOLVE-ERR-134` (SIGABRT) | 9 |
| **`OK-PROOF-VERIFIED`** | **8** |
| **`PROOF-REJECTED`** | **3** |

**Eight real MiniZinc Challenge instances solved with a proof veripb accepts**, including
`2013_nonogram` (62 MB proof), `2015_roster` (42 MB) and `2023_roster` (28 MB). That is the
first time this solver has produced a checked proof for input it did not author.

### The blocker is a one-line over-strictness, and it is 10× the predicted one

Classifying all 278 refusals by cause:

| cause | instances |
|---|---|
| **"the search array must contain variables, not constants"** | **143** |
| unsupported value-choice strategy | 30 |
| parse: "expected a type but found the identifier" | 16 |
| **set-literal domain** | **14** |

**D-0067 predicted set-literal domains were the biggest wall. At full corpus scale they are
14, and the dominant cause is 143** — an over-strict check at `lib/flatzinc/builder.ml:614`
that refuses the whole model if the search array contains **any constant**.

**A constant in a search array is not a problem**: it is a variable with nothing left to
decide, and flattening produces them routinely. Skipping it *honours* the annotation exactly,
as SPEC §3.4 requires; refusing does not. That is **M7-T7**, and it is worth more than every
other refusal cause combined.

The lesson is the one this project keeps relearning: **a sample of 78 ranked the causes wrongly**.
D-0067's ranking came from the instances that flattened under an older build; the full corpus
inverted it.

### `PROOF-REJECTED` is 3, but only 1 is the real defect

- `2013_javarouting` and `2013_rubik` — **97-byte proofs**. These are the *degenerate* case
  already folded into M7-T6: a model with nothing in it emits a proof with no logged solution.
- **`2012_tpp` — a 38 MB proof, genuinely rejected.** That is the substantive RUP defect.

So the earlier provisional reading — "3 rejected against 2 verified, M7-T6 is not exotic" — was
**too pessimistic**. The real rate is 1 substantive rejection in 11 proofs. **It is still a
lower bound** (D-0066: the same defect on an UNSAT instance is accepted silently), but it is not
1-in-4.

### Removing the width refusal turned a refusal into a crash

All 9 `SOLVE-ERR-134` are **`Fatal error: allocation failure during minor GC`** — OOM against
the 32 GB cap — on wide-domain models where **M7-T1's warning fired first and correctly**.

D-0065 replaced a refusal-by-declared-width with a warning, on the grounds that declared width
was the wrong proxy for the real cost. That was right, and this is its consequence: the models
it now accepts can **exhaust memory and abort** rather than failing gracefully. The warning did
its job; the failure mode did not.

**That argues for what D-0065 did not provide: a graceful resource guard.** Not a refusal by
declared width — that proxy is still wrong — but a real bound with a diagnostic, so an
over-large encoding ends in a message rather than `Fatal error`. **M7-T8.**

### Harness caveats, so these numbers are not over-read

- **51 `FLATTEN-FAIL` are not all unsupported instances.** Many are 2008-era `int_search`
  signatures MiniZinc 2.10.1 no longer accepts — a *corpus age* problem, not a solver one.
- **87 timeouts are at 300 s**, an arbitrary budget, on the *smallest* data file of each family.
  They say nothing about difficulty.
- One data file per family; the corpus has 1604.

## D-0069  The corpus's refusals, classified properly: four strategies, and a harness that blamed the solver

**2026-09-23.** D-0068 counted 248 `REFUSED-MODEL` outcomes over 436 instances and
classified them by the error's leading words. That was enough to find M7-T7 (143 of them
are one over-strict check) but not enough to scope what comes after it. Classified
properly, by the *thing the model actually wanted*:

| cause | instances | row |
|---|---|---|
| a constant in the search array | 143 | M7-T7 |
| `smallest` variable-selection | 25 | M7-T9 |
| `indomain_split` value-choice | 13 | M7-T9 |
| **a torn `.fzn` — the harness's own bug** | **13** | **M7-T10** |
| `indomain_median` value-choice | 6 | M7-T9 |
| `largest` variable-selection | 5 | M7-T9 |
| set-literal domains | 14 | M6-T2 |
| no `solve` item / no such file | 9 | M7-T10, suspected same cause |

**Two findings, and the second is the uncomfortable one.**

**First: the strategy tail is finite, and short.** Beyond what M7-T2 already supports, the
corpus asks for **exactly four** strategies — `smallest`, `largest`, `indomain_split`,
`indomain_median` — and nothing else. Not "a long tail of annotations"; four named things,
all four defined in the MiniZinc spec, all four mechanical. That turns an open-ended row
into a closed one, which is why M7-T9 exists as a single row.

**Second: the harness was filing its own failures under the solver's name.** Thirteen
instances were recorded as the front end refusing the model. The front end was right to
refuse them — `2010_bacp.fzn` genuinely ends with a partial duplicate line, `lete) minimize
objective;`, spliced after a correct `solve` item. The file is **torn**: the flattener's
output was captured non-atomically with 64 jobs in flight. The solver behaved perfectly and
the measurement blamed it anyway.

This is the third time this project has been misled by an instrument rather than by the
thing measured — M2-L12 measured learning as worth nothing on a suite whose largest search
was 99 nodes, D-0067 predicted set-literal domains were the biggest wall from a 78-instance
sample when at full scale they are 14 against 143, and now this. The recurring shape is not
carelessness in any one case; it is that **a measurement's own failure modes look exactly
like findings about the subject**, and nothing in a results table distinguishes them.

**So the rule, and it is cheap to follow**: every bucket that attributes a failure to the
solver must be gated on a check that the *input was well-formed*. A torn or truncated
`.fzn` is its own outcome, never `REFUSED-MODEL`. Flatten to a temp path and rename into
place; `/scratch` is ext4, so rename is atomic. M7-T10 carries this, and M7-T4 must
inherit it rather than rediscover it.

**What this does not change**: the eight verified proofs are unaffected — they are
successes, and the harness's non-atomicity can only manufacture failures, not successes. The
`PROOF-REJECTED` bucket is likewise unaffected, since a torn input cannot produce a 38 MB
proof. **But the 87 `TIMEOUT-SOLVE` have not been audited for this**, and a torn file that
happens to remain parseable is a real possibility. They are a lower-priority re-run, noted
here so it is not forgotten.

Follows D-0068. Opens M7-T9 and M7-T10.

### AMENDED 2026-09-23, same day, by M7-T10 (agent-harness). The mechanism above is WRONG, and the correction is bigger than the original finding.

**I diagnosed a torn write and named the cause as non-atomic capture. It is not.** The cause
is an **instance-ID collision**. The node harness keyed each instance on `<year>_<family>`,
but a family directory holds many `.mzn` files — `2010/bacp/` holds **fifteen** — so up to
fifteen concurrent jobs flattened to the *same* `log/<id>.fzn`, read each other's
half-written bytes, and `rm -f`'d it from under one another. The torn `lete)` fragment I
found was a real symptom of a different disease.

**The fix I prescribed would have made it worse.** Temp-plus-rename alone lets one job win
*cleanly* — and the other fourteen then silently measure the wrong model, with no torn file
left behind to notice. I would have converted a visible corruption into an invisible one and
recorded that as a fix. The harness needs unique ids **and** atomic rename; either alone is a
trap.

**The scope was 22 rows in my count. It is 101.** Every row of the 18 colliding ids is void,
and **D-0068's "436 instances" was really 353 distinct ids**. So these numbers in D-0068 and
in the table above are wrong and are superseded:

| claim | published | actual |
|---|---|---|
| instances in the corpus run | 436 | **353 distinct ids** |
| rows that are void | 13 | **101** |
| `OK-PROOF-VERIFIED` | 8 | **17** (measured over the 103 re-run) |
| the cause | non-atomic capture | **id collision** |

**What the re-run actually found**, with unique ids and atomic flatten (103 instances,
complete, `fataepyc-07:/scratch/arthur/corpus-out-m7t10/results.tsv`):

- `2010_bacp`: 15 `REFUSED-MODEL` → **8 `OK-PROOF-VERIFIED` + 7 `TIMEOUT-SOLVE`**
- `2011_bacp`: 5 `TIMEOUT` → 1 verified + 4 timeouts
- `2013_javarouting`'s *"no such file"* (5) was a sibling job's cleanup `rm`; they are
  genuine **`REFUSED-LIMIT`** — set-literal domains (M6-T2)
- `2013_rubik`'s *"no solve item"* (4) was the shared file truncated mid-write; they are
  genuine **`REFUSED-MODEL`** — a constant in a `bool_search` array (M7-T7)
- a 1-row `Fatal error: exception End_of_file` nobody had counted at all
- `PROOF-REJECTED` unchanged in these families at 2, both the degenerate 97-byte case

**`REFUSED-MODEL` 248 and M7-T7's headline 143 are therefore LOWER BOUNDS** until the void
rows are re-run. M7-T7 is still almost certainly the highest-value row; the number attached
to it is not yet a measurement.

### What this says about the rule D-0069 proposed

The rule was right and I applied it to myself too late. I wrote that *"a measurement's own
failure modes look exactly like findings about the subject"* — and then diagnosed the
measurement's failure mode from the single artefact it left lying around, without asking how
that artefact came to exist. **One torn file is evidence of tearing; it is not evidence of
what tore it.** The distinguishing question — *can two jobs address the same path?* — costs
one `ls` of a family directory, and I did not ask it.

So the rule gains a clause: a harness fix must be validated against the mechanism, not
against the symptom. `scripts/corpus_run.sh` now carries `--self-test`, which needs no
corpus, node, solver or checker — and which caught **two live bugs in its own validator while
that validator was being written**, including a first version that *accepted* the real
`2010_bacp` shape. That is the argument for it existing, and it is the same argument as this
amendment.

**Not corrected, deliberately**: D-0068's own text stands as written, with this record as its
correction, per the append-only discipline. The 8 verified proofs it reports were real; there
were simply 9 more it could not see.
---

## D-0070  The level-0 nogood RUP defect: a decision that settles past a hole, and a filter that cannot see it

**Status**: **ACCEPTED and FIXED** (M7-T6, 2026-09-23, agent-rup). Closes the row D-0067
opened and D-0068 sized. A second, unrelated bug folded into the same row is recorded in
part 3 below.

### The defect

`test/models/rup_level0_nogood_sat.fzn` — nine variables, five constraints, **no global**
— is satisfiable, the solver answers `xs = [1,1,9,1,1,1,2,1,1]`, and every constraint is
satisfied by inspection. veripb 3.0.2 nevertheless refused the proof at the level-7
backtrack nogood with *"The constraint is not implied by reverse unit propagation (RUP)
from core and derived database."* M1-T44's shape exactly: right answer, valid-looking
steps, wrong artefact.

### The cause, in one paragraph

`int_ne(x6, x7)` with `x6` fixed at 2 punches a **hole** in `x7`'s domain at 2. The
level-6 decision pushes `set_lo x7 2`, `Domain.settle` walks the bound over the hole, and
the trail records **`x7 >= 3`** while the branch literal is **`x7 >= 2`**. That gap is
M1-T55's, and M1-T55 already writes it down: `Search.bridges` emits

```
rup 1 x7_ge_3  1 ~x7_ge_2  1 ~<each ancestor decision> >= 1 ;
```

conditioned on **every** ancestor, because its own `rup` reaches `x7_ge_3` only by the
hole's trace line or by the disequality's `.opb` rows, and both of those need the
ancestors asserted. Then M2-L3's nogood filter runs:

```ocaml
(* lib/core/search.ml, dfs's conflict arm *)
| Some ls -> minimise stats cfg.policy (List.filter (fun (_, l) -> List.mem l ls) all)
```

`ls` is `Learn.levels` — the decision levels the 1UIP walk says the conflict rests on.
**The implication graph has no edge for a settle.** It records the decision as the
literal the branch *assumed* (`x7 >= 2`); everything downstream propagated from the bound
the trail *landed on* (`x7 >= 3`); nothing connects the two, so no ancestor that punched
the hole ever enters the walk and none of their levels appear in `ls`. The filter then
drops exactly the literals the bridge rests on. The bridge stops being unit under the
negated nogood, and the nogood's `rup` fails — **at the nogood, several inferences away
from the settle that caused it**, which is why three earlier readings of this symptom
looked at the nogood machinery and found nothing wrong with it.

This also explains D-0067's puzzling asymmetry — the same 2001 fuzz seeds giving **3**
RUP failures with `all_different` native and **5** with it decomposed to pairwise
`int_ne`. Overlapping but not identical, because the two produce different *settle*
patterns over the same underlying gap. The defect was never in the global; it is upstream
of every propagator that punches a hole.

### It is a wrong ARTEFACT, never a wrong ANSWER

Stated explicitly because M1-T44 had the same shape and someone will ask. The defect is
**proof-only**, and the reason is that nothing here feeds back into the search:

- `bridges` is pure emission — it writes lines and touches no domain, no trail and no
  decision.
- The filter's output is the nogood *clause*. Under-filtering it makes the clause
  **stronger than the branch supports in the artefact**, but the solver's own pruning was
  done by propagators from real reasons; the nogood is consumed only to skip a sibling
  (`mentions_level`) and to file a backjump level. A nogood carrying *more* literals
  mentions *more* levels, so the repaired build skips *fewer* siblings — strictly less
  pruning, never more.
- The break lane asserts this rather than arguing it: with the break on and off, the
  returned assignment is **identical**, and only the proof differs.

### The fix

`Search.bridges` now **returns the decision literals its lines rest on**, and the nogood
filter keeps a literal that is either in `Learn.levels` *or* one a bridge rests on. On
every path where no decision settled past a hole, the returned list is empty and the
filter is byte-for-byte what it was.

**Measured, not argued.** Flipping the new `break_bridge_levels` knob back to the
pre-M7-T6 filter and re-running all 87 models: **exactly one** of the 87 `.pbp` files
differs, `rup_level0_nogood_sat.pbp`, and it is the only one that fails. The other 86 are
byte-identical. So the fix pays for itself in one model and costs nothing anywhere else.

### What D-0066 means for the blast radius

D-0068's headline rate — 1 substantive rejection in 11 proofs over 436 instances — was
**never the true rate and cannot be**. `rup` is vacuous over a contradictory database
(D-0066), so every UNSAT instance of this same defect has been **accepted silently** all
along, and most models in this suite and in that corpus are UNSAT. The rate we could see
was the rate on the satisfiable ones. Two consequences the next person should carry:

1. **Proofs that were passing were changed by this fix**, and that is the expected
   direction — some of them were passing vacuously. The 86-of-87 byte-identical
   measurement above bounds how many.
2. **A settle-past-a-hole is the thing to look at first** the next time a nogood is
   rejected. It is invisible in the answer, invisible on UNSAT models, and its symptom
   appears at a line that looks correct.

### Part 3: the empty model, which is a DIFFERENT bug

Folded into the same row, and it is not the same defect. A model with no variables and no
constraints emitted `conclusion SAT` with **no `sol` line before it**, and 3.0.2 refused
the whole file: *"No solution has been logged in the proof and no solution has been given
in the conclusion."* D-0068 measured this as **two of the corpus's three rejections**
(`2013_javarouting`, `2013_rubik` — both 97-byte proofs).

The cause is one guard in `lib/proof/writer.ml`'s `conclusion`:

```ocaml
(match v with Sat (_ :: _ as lits) -> solution t lits | _ -> ());
```

`git log -S` places it in **26d3ab2 (M1-T18)**, and reading that commit settles which of
the two readings it is. M1-T18 replaced `Sat [] -> "conclusion SAT"` /
`Sat lits -> "conclusion SAT : <lits>"`, where the empty case meant *"no assignment to
inline"* and skipping it was right. The `_ :: _` was that case split **carried over
mechanically** onto the new `sol` line, where it is not right: `conclusion SAT` *requires*
a logged solution. It was **not** suppressing an empty assignment on a non-empty model —
the other reading, under which removing the guard would turn a silent skip into a *wrong*
`sol` line. `Search.solve` builds these literals with `Encoding.assignment_lits` over the
assignment of **every** store variable, so the list is empty exactly when the encoding has
no variables, which is exactly when the `.opb` has none either and the empty assignment is
the complete one. A bare `sol ;` is accepted by 3.0.2; measured.

So the fix is `Sat lits -> solution t lits`, and `test/models/empty_model_sat.fzn` is the
model test. The **control** matters as much as the lane: `test/unit/test_learn.ml` asserts
both that the empty model's proof verifies *and* that a model with variables still emits
its full `sol` line with its literals — otherwise the lane would have shown only that a
bare `sol ;` parses.

### Break lanes

`Search.config.break_bridge_levels`, not CLI-reachable, exactly as `break_i_s4`,
`break_ladder_mult`, `break_pb_degree` and `backjump_on_pb` are. It restores the
pre-M7-T6 filter. `test/unit/test_learn.ml` runs it over a **satisfiable** model — D-0066
makes that mandatory, not stylistic — and pins the rejection at the checker's full
wording *and* at the line number it names, because CLAUDE.md is right that *"reverse unit
propagation"* alone would be matched by any other RUP failure in the same proof. The
empty-model lane removes the `sol` line by byte mutation and pins *"No solution has been
logged in the proof"* the same way.

Follows D-0066, D-0067 and D-0068. Closes M7-T6.
## D-0071  The graceful resource guard: predictive AND reactive, both defaulting to off

**Status**: **ACCEPTED**, implemented by M7-T8 (2026-09-23, agent-guard). Sits directly on
top of **D-0065** and does not amend it. **D-0068** is why it exists.

### The problem, exactly

D-0068's first full corpus run lost **9 of 436 instances to exit 134**, and all nine were
the same death: `Fatal error: allocation failure during minor GC` — the OCaml runtime
aborting against a 32 GB per-job cap, on wide-domain models. In every one of the nine,
**M7-T1's width warning had already fired, and fired correctly.** The warning did its job.
The failure mode did not.

That abort is the worst possible ending. It cannot be caught, it names nothing, and its
exit status is indistinguishable from a crash — so a harness folds "this machine ran out"
into the same bucket as "this proof is wrong", which is precisely what `SOLVE-ERR-134` was.

### What this is NOT

**The declared-width refusal does not come back.** D-0065's argument is untouched and still
correct: declared width is the wrong proxy for the real cost, it bounds one variable rather
than the model, and a width-30 000 model demonstrably solves and verifies. This row does not
restrict what the solver attempts. It makes the *ending* graceful.

### Predictive or reactive: both, and they are not redundant

| | predictive: `--max-encoding-clauses` | reactive: `--max-heap-mb` |
|---|---|---|
| bounds | `ladder_clauses + direct_values` | live OCaml heap |
| where | `declare_int`, `ensure_direct`, **before the allocating loop** | a `Gc` alarm, plus a synchronous read at each declaration |
| cost when unset | nothing: one `None` match per declaration | nothing: no alarm is installed at all |
| catches | the nine | everything the nine are not: the trail, learned constraints, the writer |

**A `Gc` alarm alone would not have caught the nine.** It is mem_guard.ml's mechanism
(M1-T53) and the shape here is deliberately its shape, but an alarm runs **at the end of a
major cycle**, and the abort in question is a **minor**-heap allocation failure: the window
between "fine" and "the runtime gave up" need contain no major cycle. A guard that only
watches cannot promise to act before the allocation it is watching for. The row said so —
*"the guard must act BEFORE the allocation"* — and that rules reactive-only out.

**A predictive bound can, and the quantity is already minted here.** `lib/proof/encoding.ml`
computes the encoding's size; the check is one comparison per declaration, deterministic,
and made before the ladder loop, so a refused declaration leaves the encoding byte-identical
to what it was (M1-T54's property, kept for M1-T54's reason).

And this is the **aggregate** `max_order_width`'s own comment admitted no per-variable cap
ever bounded: *"a thousand variables at w = 9 999 is still ten million clauses. That gap is
deliberate and left open rather than papered over here — an aggregate budget is a different
check in a different place."* This is that different place.

The heap watch is kept as the backstop for what no encoding-size prediction can see. Neither
is a refusal by declared width, and the heap watch cannot refuse a model at all — only end
the run it is already in.

### A measurement that changes how the reactive half is described

On this switch (**OCaml 5.1.1, native**, 2026-09-23), `Gc.quick_stat ().heap_words` **reads
0 until the first major cycle completes**. `Gc.stat` is exact but walks the heap, which is
not a per-declaration cost.

This is not a hole, but it inverts the naive reading of which half is reliable:

- the **alarm** fires at end-of-major-cycle, which is exactly when the figure is fresh — the
  reliable half;
- the **synchronous** check reads whatever the last cycle left, so on a run too short to
  complete one it reads 0, **correctly**: such a run holds at most a minor heap. It earns
  its place by being the only check guaranteed to run before a *particular* declaration.

`test/unit/mem_guard.ml` is unaffected — it is alarm-only — but any future session tempted
to read `quick_stat` synchronously should read this paragraph first.

### The default is OFF, and no measurement would justify otherwise

Both budgets default to `None`. This is D-0065's rule and the user's standing instruction:
the normal build has no restrictions and restrictions live behind options. A default here
would be a number calibrated to whichever machine measured it — which is the exact defect
D-0065 removed. There is no measurement that argues for one, and inventing one out of
caution would be reinstating D-0041 under a new name.

What *is* measured is that having the guard costs nothing:

- **86 models × {stdout, stderr, exit code, `.opb`, `.pbp`} = 430 artefacts, 0 differing**,
  against a binary built from the parent commit (md5 `9bad5e8e` → `e9ef0277`, so the two
  sides really are different binaries — D-0068's own caveat about comparisons that used the
  same binary).
- the largest encoding in the 85-model suite is **1996 clauses** (`width_root_unsat`, w=999,
  the deliberate one); the next largest is 196. Nothing in the suite is within three orders
  of magnitude of a budget anyone would set.

### Exit status 5, and why a fifth number

0 solved (SAT or UNSAT), 2 usage or bad model, 3 unsupported model, 4 internal invariant
failure, **5 resource budget exhausted**. It is not 3, because the model is legal FlatZinc
that a larger budget answers; not 4, because no invariant failed; and emphatically not 134.
A bucket a harness cannot separate is the defect D-0068 reported, so the separation is the
deliverable.

### The diagnostic

"Out of memory" is not a diagnostic. Both messages name the declaration that crossed the
line, what it would have added, what was already minted, the budget in force, and —
separately, because it need not be the same variable — **the widest declared domain, which
is the one a reader can act on**. When the crossing declaration is the first one, it names
itself rather than saying no variable has been declared yet; that sentence was written,
observed to be true and useless, and replaced.

Under `--proof`, the binary additionally says the `.opb`/`.pbp` are incomplete and must not
be checked or kept. The overrun can fire at `ensure_direct`, which runs inside `start_proof`
with files already open, and half a proof that veripb happens to parse is the worst outcome
available.

### What was deliberately not done

- **No wide-domain test model.** CLAUDE.md forbids one outright and `width_root_unsat.fzn`
  at w=999 already covers deliberate width. The guard is tripped by setting the **option**
  low on an ordinary model, which also tests the option — a wide model would not.
- **No default, no aggregate check in `compile.ml`.** `lib/flatzinc/builder.ml` and
  `lib/core/**` were another session's during this wave; nothing here needed them.
- **The alarm exits rather than raising.** It fires at an arbitrary point in an arbitrary
  function, and an exception from there would unwind through code that never agreed to
  handle it — including the proof writer, mid-line. The synchronous check raises, because it
  knows where it is; the wording and the status are identical either way.

---

## D-0072  Set domains: the holes go in the .opb as ladder rows, and in the solver as propagators

**Status**: **ACCEPTED** (M7-T11, 2026-09-23, agent-holes). Removes
`Compile.reject_set_domain`, which refused `var {1,3,5}: x`. It was not weakened; the
thing it protected against was fixed.

### What the refusal was protecting

Its message named the gap precisely, which is why it was worth keeping until this row:
`Encoding.declare_int` took only `~lo` and `~hi`, so the holes of a set domain had no
representation in the `.opb`. Encoding the hull instead would have been a **relaxation** —
the solver could report UNSAT and hand veripb a refutation of an `.opb` that is
satisfiable, and veripb would accept it, because veripb only ever sees the `.opb`. That
is the one failure mode this project will not ship, and it is invisible to the checker,
so nothing downstream could have caught it.

### The ladder convention, confirmed

`docs/PROOF-FORMAT.md` §3 is normative and the loop at the bottom of
`Encoding.declare_int` agrees with it literally:

- `x_ge_v` exists for `lo < v <= hi` and means `x >= v`;
- the rung written for each `lo < v < hi` is `+1 ~x_ge_(v+1) +1 x_ge_v >= 1`, i.e.
  **`x >= v+1 -> x >= v`** — **downward**.

Confirmed two ways rather than read once: by the spec section, and by dumping a real
`.opb` (`var {1,3,5}` → `@c1 +1 ~x_ge_3 +1 x_ge_2 >= 1`, and so on).

### The hole row

`x = h` is the conjunction `x >= h` AND NOT `x >= h+1`, so the row that forbids exactly
that assignment and nothing else is the **mirror** of the rung at the same value:

```
+1 ~x_ge_h +1 x_ge_(h+1) >= 1        i.e.  x >= h  ->  x >= h+1      (UPWARD)
```

**The polarity is the whole soundness argument, and getting it backwards is silently
unsound rather than loudly wrong**: writing the ladder's own direction there
(`x >= h+1 -> x >= h`) is already implied by the ladder, forbids nothing, and leaves the
`.opb` a relaxation that the checker cannot see. `test_proof.ml`'s
`test_m7t11_hole_rows` and `test_compile.ml`'s `test_set_domain_holes` both match the
emitted text literally, and both match a ladder rung as well, so a change that collapsed
the two shapes into one could not pass.

A hole is required to be **strictly interior** (`lo < h < hi`), which costs nothing
because `Compile` takes the hull to be the min and max of the value set, so both ends are
always present. Out-of-range holes raise `Encoding.Hole_out_of_range` rather than being
filtered: a silently dropped hole is a value the `.opb` admits and the store does not,
which is this decision running backwards.

### The half that the hole row alone does NOT buy, and the measurement that showed it

The first implementation put the holes into the store as well, via `Domain.of_list`. It
is **wrong, and silently so**. A hole that is in the declared domain but behind no
propagator has no trail entry — `Store.remover` returns `None`, and
`lib/core/trace.ml`'s header is explicit that this is the `var {1,3,5}` case — so nothing
in the proof ever claims it. `int_eq(x, 4)` over `{1,3,5}` is the smallest instance: the
domain wipeout happens because 4 is a hole, but `Lin_eq`'s justification is a `pol` over
two model rows that is satisfied at `x = 4`. Measured, veripb 3.0.2:

```
The constraint with ID 9 is not contradicting, as specified by the hint.
```

Three further shapes (`int_eq` against a `4..4` variable, against a `1..5` variable
pinned to 4, and against a second set domain `{2,4}`) failed the same way, and one failed
earlier still with `Justify.emit: Combine's Weaken summand must be non-empty`.

This is the same root cause D-0070 fixed from the other end: the implication graph has no
edge for a `settle`, so a bound that walks over a hole is disconnected from the reasoning
that put the hole there. D-0070's fix is `Search.bridges`, and a bridge needs the hole to
have been *derived*. A declared hole never is.

**So the store gets the hull, and each hole is posted as its own `Ne` instance**
(`x <> h`, the single term `(+1, x)` with right-hand side `h`). Every hole pruning is then
an ordinary logged pruning with an ordinary trail entry, and M1-T55's bridge and D-0070's
nogood filter apply to it unchanged. Nothing new was added to the explanation vocabulary
and no propagator was written.

### Why the hole row and the `Ne` instance are not redundant

`Ne` **cites no row id**; its justification is a self-contained `rup` over order literals
(its module header says why). The clause that `rup` has to land on for `x <> h` **is** the
hole row. So `Compile` deliberately does *not* call `Encoding.add_int_lin_ne` for a hole:
that would mint an auxiliary Boolean and two rows where one clause does the job.
`test_set_domain_holes` asserts the absence of the auxiliary, so "one clause per hole" is
a property of the artefact rather than of the intention.

### Case (d): `{0, 1000}` is BUDGETED, not refused

**Decision: budgeted.** A set domain is never worse than **twice** the ladder of its own
hull, because a hole must be strictly interior and there are at most `hi - lo - 1` of
those. Holes therefore add a constant factor, not an order of magnitude, to a cost the
hull already pays and already passes through two caps: `Encoding.max_order_width` (10 000,
D-0041) and M7-T8's `--max-encoding-clauses` (D-0071). A third refusal keyed on the ratio
of holes to values would fire on models the existing caps already admit at the same cost,
and would be the only cap in this module keyed on something other than size.

Hole rows are counted into `ladder_clauses`, so M7-T8's **predictive** check sees them
before anything is allocated — an unbudgeted allocation path is exactly what D-0071
exists to prevent. `test_m7t11_hole_rows` pins this: hull `1..5` with holes `{2,4}` is 5
clauses, a budget of 5 admits it, a budget of 4 refuses it and leaves the encoding
untouched.

`test/models/set_domain_wide_sat.fzn` carries the shape at `{0,200}` — 2 values, 199
holes, 199 + 199 rows — with a width justification in its header, the way
`width_root_unsat.fzn` does.

### Evidence

- (a) `set_domain_sat.fzn` — `{1,3,5}` bounded to `(1,5)` answers `x = 3`, which only the
  holes can force. `s VERIFIED SATISFIABLE`.
- (b) `set_domain_hole_unsat.fzn` — the only value satisfying the constraints is 4, a
  hole. UNSAT, `s VERIFIED UNSATISFIABLE`. Over a relaxed `.opb` this would be a
  refutation of a satisfiable model.
- (c) `test_set_domain_holes` asserts on the **emitted** `.opb` text, both polarities,
  and the absence of an auxiliary; `test_m7t11_hole_rows` asserts the budget.
- (d) `set_domain_wide_sat.fzn`, `s VERIFIED SATISFIABLE`.

Two of the four are **satisfiable**, per D-0053/D-0066: `red` and `rup` are both vacuous
over a contradictory database, so a suite of UNSAT lanes alone would be evidence of
nothing.

## D-0073  The `rup` audit: none of the 26 lanes was vacuous, and D-0066's remedy was wrong

**Status**: **ACCEPTED**, implemented by M7-T5 (2026-09-23, agent-vacuity).
`test/unit/test_mutation.ml`, `test/unit/test_learn.ml`, `CLAUDE.md`. Amends **D-0066**.

### The audit, by name

D-0066 counted **26 lanes across 9 files** asserting a `rup` rejection and said how many
were vacuous was unknown. The 26 is a grep of the string *"reverse unit propagation"*.
Of the **27** occurrences that string now has in those nine files, **twelve are comments
explaining the rule**, **seven are shared wording constants**, and **eight are inline
assertion or diagnostic sites**. Resolved into distinct lanes — one lane being one test
that asserts the checker rejects on the RUP judgement — that is **fifteen lanes**, four of
which fan out over scene tables (`test_trace` 9 executed checks, `test_matrix` 13,
`test_proof` 4). Every one was run and its verdict taken from the run, not from reading:

| file | lane | verdict |
|---|---|---|
| `test_prop` | `arith D-0033: the FLOORING bound -7 div 2 <= -4 is refused` | **sound** — model SAT, rejection observed |
| `test_prop` | `reif eq: the same nogood with the reifier's literal dropped` | **sound** |
| `test_prop` | two further occurrences at `:4221`, `:4680` | comments, not lanes |
| `test_pb` | `e: ...rejects on the JUDGEMENT, in the checker's whole sentence` (`break_pb_degree`, PHP 5→4) | **sound** |
| `test_pb` | `c: ...and on the JUDGEMENT...` (`backjump_on_pb`) | **sound** |
| `test_pb` | `rup_judgement` definition + three comment occurrences | constant / comments |
| `test_trace` | blanked-trace judgement, the scene table (`:569`) — 5 executed | **sound** |
| `test_trace` | blanked-trace judgement, the settle scenes (`:894`) — 2 executed | **sound** |
| `test_trace` | `I-X10 ahead BREAK: the same line standalone is REFUSED` (`:1412`) — 2 executed | **sound** |
| `test_matrix` | blanked-trace judgement, the instance table (`:1065`) — 13 executed | **sound** |
| `test_learn` | `a2 BREAK: weakest-threshold minimisation` | **sound** |
| `test_learn` | `b BREAK: derivation after the \`w\` retiring its level` | **sound** |
| `test_learn` | `M7-T6 break: the rejection is the RUP judgement, at full wording` | **sound** |
| `test_endtoend` | `M5 BREAK: ...refused on the JUDGEMENT, not on the grammar` | **sound** — model SAT |
| `test_endtoend` | `M5 load-bearing: ...refused on the judgement` | **sound** — model SAT |
| `test_proof` | `rejected_at`, the three view breaks — 4 executed | **sound** — model SAT, and it pins `file:line` as well as the judgement |
| `test_justify` | `Defining BREAK: citing a bound the model does NOT imply (x >= 3)` | **sound** |
| `test_random` | `:724` | **not a lane** — it classifies an observed rejection into a known-bug bucket, and every bucket is asserted EMPTY |

**Counts: vacuous 0, sound 15, unreachable 0.** Nothing was rebuilt, because there was
nothing to rebuild.

### Why the premise was wrong, and it is worth stating

D-0066 reasoned: *over a contradictory database everything is RUP, so a break lane
asserting a `rup` rejection over an UNSAT model goes green whether the code is right or
wrong.* **The second half does not follow from the first.** If the corrupted line is
accepted, a lane asserting *rejection* goes **RED**, not green. Vacuity of this kind
cannot hide in a rejection lane; it makes the lane fail loudly. Every one of the fifteen
observes a real rejection today, each with an honest control that verifies.

### What the audit did find, and it is larger

**The exposure is on the ACCEPTANCE side, and satisfiability is not the cure.** M7-T5 put
D-0066's own remedy — *"verify over a satisfiable model"*, which is the right rule for
`red` (D-0053) — to the checker, by flipping one literal's polarity in **every** eligible
`rup` line of two real proofs:

| model | answer | eligible `rup` lines | flips ACCEPTED |
|---|---|---|---|
| `ne_eq_unsat` | UNSAT | 8 | **8** — total |
| `chain_sat` | **SAT** | 15 | **3** |

**A satisfiable model does not make a `rup` line load-bearing.** `chain_sat` is
satisfiable, branches, and still has three lines whose claim the checker owes nothing to.
Conversely twelve of its fifteen *are* load-bearing and refuse the flip on the RUP
judgement. **Vacuity is a property of the LINE, not of the model's answer** — the line has
to matter to a *later* line, which is `test_mutation.ml`'s own trap 3 stated one level up.
A lane rebuilt over a SAT model on D-0066's advice alone would have been just as vacuous.

The polarity flip is used rather than the dropped literal on purpose: dropping a literal
can leave a claim that is genuinely stronger and genuinely implied, so its acceptance is
ambiguous. A flip is a different claim, and accepting it is vacuity and nothing else.

### What was built

The census is **six checks in `test/unit/test_mutation.ml`**, run on every suite run, that
re-measure the table above rather than quoting it — control, the total vacuity on the
UNSAT model, the accepted flip on the SAT model, the refused flip on the SAT model, and
the checker's full wording on that refusal. If the checker changes, the numbers change and
the lane reddens instead of the record rotting.

`test/unit/test_learn.ml`'s `rejection_wordings` was raised from *"is not implied by
reverse unit propagation"* to the checker's whole sentence — its own comment already
claimed full strength and the constant did not match it. Both break lanes still recognise
their rejection.

`CLAUDE.md`'s proof-discipline list gains the `rup` sentence beside the `red` one, stating
the **measured** remedy (pin the line) rather than the assumed one (pick a SAT model).

### No defect in `lib/` was uncovered

This was the outcome the row most wanted and it did not arrive: the fifteen lanes were
real, so none was hiding a live bug. The nearest thing is not new — D-0070's level-0
nogood RUP defect, already open as M7-T6, and D-0066's own note that on an UNSAT instance
the same defect is accepted silently. **This record makes that note quantitative**: on
`ne_eq_unsat` it is not "some" lines, it is **all** of them.

Amends D-0066. Closes M7-T5.

## D-0074  The wave-27 corpus run: 33 verified, the search-array wall is gone, and `2012_tpp` is a SECOND defect

**2026-09-23.** The first run on the M7-T4 harness, 436 **distinct** instances, complete
(`DONE-1790169395  436  436`), binary hashed `605ede27…` at `ea5fc4c`. **That tip is wave 27
only** — M7-T9 and M7-T11 merged after launch and are *not* in these numbers. That matters for
reading every line below.

| outcome | count |
|---|---|
| `TIMEOUT-SOLVE` (300 s) | 155 |
| `REFUSED-MODEL` | 107 |
| `REFUSED-LIMIT` | 74 |
| `FLATTEN-FAIL` | 50 |
| **`OK-PROOF-VERIFIED`** | **33** |
| `SOLVE-ERR-134` | 15 |
| **`PROOF-REJECTED`** | **1** |
| `FLATTEN-TIMEOUT` | 1 |

### M7-T7 worked completely, and that is a measurement now

**Search-array refusals: 0.** Not "reduced" — the string appears nowhere in 436 results,
against 143 occurrences before. D-0068's headline was the one prediction this project made
that survived contact with the corpus intact. `OK-PROOF-VERIFIED` **8 → 33**.

**Do not read 33 as 8 + 25.** D-0069's amendment applies: that run had 353 distinct ids over
436 rows, this one has 436 distinct instances, so 83 of these models had never been measured.
The like-for-like claim is narrower and still strong: *the single check M7-T7 removed was
worth more than every other refusal cause combined, as predicted.*

### The two biggest remaining buckets are ALREADY FIXED on `main`, and this run cannot see it

- **`REFUSED-MODEL` 107, of which 94 are search strategies** — 52 `indomain_split`, 35
  `smallest`, 6 `largest`, 1 `bool_search` `smallest`. **M7-T9 shipped all of those**, hours
  after this run launched.
- **`REFUSED-LIMIT` 74, of which 74 are set domains.** Every single one. **M7-T11 shipped
  that**, also after launch.

So **~168 of the 436 are addressed by code already on `main`** and unmeasured. The next run is
not a re-measurement, it is the first measurement of wave 28. **Nobody should quote 33 as the
current figure.**

What genuinely remains in `REFUSED-MODEL` after wave 28 is small: 6 `indomain_median`
(M7-T12, refused **by design**), 2 `anti_first_fail`, 1 bare `indomain`, 2 `var int` with no
declared domain.

### `2012_tpp` is STILL REJECTED, and that is the most informative bit in the run

M7-T6 / D-0070 fixed the settle-past-a-hole defect and its reproducer verifies. **`2012_tpp`
does not**: 38.5 MB proof, *"The constraint is not implied by reverse unit propagation (RUP)
from core and derived database."* Same wording, same instance, after the fix.

**So there is a second RUP defect.** D-0070's account was right about what it explained — the
reproducer was reduced from this corpus and the fix is real — but it was **not the whole of
what `2012_tpp` hits**. I recorded on merge that M7-T6 did not claim to be the only cause;
this is that caveat cashing out, not a surprise. Opened as **M7-T13**.

Note what makes this visible at all: `2012_tpp` is a **satisfiable** instance. Per D-0066 as
amended, a `rup` line is checkable only when it is load-bearing for a later line, so the UNSAT
instances of this second defect are still being accepted silently. **1 of 34 proofs rejected
is a lower bound and always was.**

### The resource guard is present and did nothing, by design

**15 `SOLVE-ERR-134`** (OCaml allocation-failure aborts), up from 9 — more instances now reach
the solver at all. **0 exit-5.** M7-T8's guard shipped with both limits defaulting to `none`
(D-0071, on D-0065's reasoning that any default is a property of the measuring machine), so it
was never armed. That is the designed behaviour and not a defect — **but a harness that runs
under a 32 GB `ulimit` and does not tell the solver about it is throwing away the diagnostic
it paid for.** Opened as **M7-T14**: the harness should pass `--max-heap-mb` derived from its
own `MEM_KB`, turning 15 aborts into 15 diagnostics naming what to narrow.

### The frontier moved

`TIMEOUT-SOLVE` is now the largest bucket at **155**, and after wave 28 lands it will grow
again as refusals convert into attempts. **That is the next real wall, and it is a different
kind of problem from every wave so far** — not a refusal to fix or an artefact to correct, but
search and propagation strength. No row is open for it yet and none should be opened until the
wave-28 run says which instances time out and how close they get.

Follows D-0068, D-0069 (as amended), D-0070. Opens M7-T13 and M7-T14.

## D-0075  The SECOND RUP defect: a propagator that reads a HOLE and states only BOUNDS

**Status**: **ACCEPTED and FIXED** (M7-T13, 2026-09-23, agent-tpp). Closes the row D-0074
opened. It is **not** D-0070's shape, and saying which it is not is half the record.

### The defect, in one paragraph

`array_int_element` is **DOMAIN** consistent, so its rule 2 — `dom(c) := { as[p] : p in
dom(idx) }` — reads the index's **live domain, holes included**. Its *reason* could not:
`Reason.t` holds bound facts and nothing else, and `element.ml`'s `bound_facts` said so in
its own comment — "the index's HOLES are not here and cannot be" — discharging the gap with
the claim that the checker "re-derives the hole itself, from this constraint's own rows or
**from the hole's own earlier trace line**". **That second half is false as stated.** A
hole's trace line is a clause with its own TAIL, the facts the propagator that punched the
hole read. `rup` is unit propagation, and a line only fires once its tail is falsified — and
negating a line that never mentions those facts does not falsify them. So the result push's
`rup` is not derivable, and the checker says so several inferences downstream of where the
wrong thing was written, exactly as in D-0070.

### The reproducer, which is the deliverable D-0074 asked for first

`test/models/element_index_hole_rup_sat.fzn`: **six variables, six constraints, no global,
every declared domain three values wide**, reduced from `2012_tpp`'s 188 KB / 38.5 MB. The
model is satisfiable and the answer is right. `y >= 2` fixes `y` at 2, `int_ne(idx,y)` punches
the **interior** hole `idx <> 2`, and `element` reads `dom(idx) = {1,3}` over `a = [1,0,2]`
and pushes `z >= 1`. Both of the index's bounds and both of the result's were **still at their
declared values**, so `Reason.lit_of_fact` dropped every one of them and the line came out as

```
rup +1 z_ge_1 >= 1 ;
```

— a bare unit, with no tail at all, which is not merely unprovable but **false**: `idx = 2`
gives `z = a[2] = 0`. That is the strongest form the defect takes and the reason this
reduction is worth more than the 38.5 MB it came from.

Two things about the model look over-built and are not. **q1/q2/q3** are the failure: trace
lines are written only when a branch fails (`trace.ml`, "lazy, not eager"), so the defective
line is emitted — and therefore checked — only if the branch that made the push goes on to
fail, and it must fail **deeper** than the push so the push is on the trail the failure walks.
Delete them and the model is satisfied at level 1, no trace is written, and the defect is
invisible. **The search annotation** is load-bearing too: `input_order`/`indomain_max` is what
makes `y >= 2` the first decision, and only a decision that leaves an interior gap produces
the hole — a bound-value decision cannot.

### The fix

The facts travel. For each hole the pruning read, `element.ml` now cites the **reason of the
trail entry that punched the hole** (`Store.remover` → `entry.reason`), which is bound facts
and does fit on a clause tail. The line becomes `rup +1 z_ge_1 +1 ~y_ge_2 >= 1 ;`, RUP against
`int_ne`'s own earlier line. This is `trace.ml`'s `settle_facts` technique applied **one step
earlier**: there the line for a bound that *settled over* a hole cites the hole's facts, here
the line for a pruning that *read* a hole cites them.

Both directions are fixed, because both filtering rules read a domain and not a window: a
**result** pruning carries the INDEX's holes (rule 2 reads `dom(idx)`), an **index** pruning
carries the RESULT's (rule 1 reads `dom(c)`). Only the first is reproduced; the second is the
same mechanism and was fixed with it rather than left for a second rejection to find.

The collection is over the whole current window rather than over the holes the pruning
provably leaned on. **An over-stated reason is a weaker line, never an unsound one** — the
same trade `bound_facts` already makes for reading both views' bounds unconditionally.

A price this pays knowingly: such a line is **no longer a consequence of a single model row**,
so I-X10's enumeration gains a second member of the kind `trace.ml`'s header already names
("that one line is therefore **not** a consequence of a single model row, and it is the only
kind here that is not" — it is now not the only kind). The line is still decision-free in
I-X10's sense and still globally valid; what it needs from the database is a line `trace.ml`
wrote itself, earlier, for an earlier trail entry.

### It is a wrong ARTEFACT, never a wrong ANSWER

Same argument D-0070 makes, and it holds for the same reason: nothing here feeds back into the
search. `bound_facts` and the new hole facts are consumed by `Trace` to write lines and by
conflict analysis to build a nogood; the *pruning itself* is made by rule 1 and rule 2 reading
the live domains, which were and are correct — `dom(idx) = {1,3}` really does force `z >= 1`.
Measured, not argued: on the reproducer and on `2012_tpp` the **answer is byte-identical**
before and after (`2012_tpp`'s solution file is 27059 bytes either way, `obj = 190`), and only
the proof differs. The defect could never have produced a wrong answer, and — the other half —
it could never have been *caught* by one.

### `2012_tpp` verifies, and that was checked rather than inferred

Both sides built on the node, **both binaries hashed**: at `2748fe2` (`2cf89014…`) veripb 3.0.2
still refuses at `.pbp:21217`, the same line D-0074 reported; with this patch (`44985cac…`) the
same instance gives **`s VERIFIED BOUNDS 190 <= obj <= 190`**. The proof grew by 10 KB on 38.5 MB.

### What this does NOT license anyone to conclude

`2012_tpp` was visible because it is **satisfiable**. Per D-0066 as amended a `rup` line is
checkable only where it is load-bearing for a later line over a database that is not already
contradictory, so **every UNSAT instance of this same defect has been accepted silently**, here
and in the corpus. One rejection in 34 proofs was a lower bound before this fix and the next
run's number will be a lower bound too. **Do not quote a rate.**

And the general lesson, which is the third time this project has paid for it (M1-T44, D-0070,
this): **a propagator whose consistency level is stronger than its reason language is a proof
defect waiting for an instance.** `element` is the first `Domain`-consistent propagator in the
tree (D-0059), and it read holes from the day it shipped while `Reason.t` could only say
bounds. The next `Domain` propagator inherits the same gap. `alldiff` does not, today, only
because it is `Bounds` and genuinely reads a window; **that is an accident of its consistency
level and not a property of the code**, and M4-T2's second stage would end it.

Follows D-0070, D-0074, D-0066 (as amended), D-0059. Closes M7-T13.
---

## D-0076  `FLATTEN-FAIL` was mostly a 2008-2010 dialect, not a missing global

**Status**: **ACCEPTED**, implemented by M7-T15 (2026-09-23, agent-flatten).
`mznlib/compat_mzn1.mzn`, `mznlib/test/`, four model tests.

### What the 50 actually were

D-0074's run left 50 instances that never reached the solver. The row that opened
M7-T15 read the bucket as "16 shim + 8 a missing global + 12 harness + 2 models'
own". Re-read from the per-instance logs, the second bucket is **not a global**:
all eight are

```
int_search(array[int] of var int, string, string, string)
```

— MiniZinc **1.x's string-valued search annotation**, which 2.x has no signature
for. Together with `is_output`, 24 of the 50 are one thing: a Challenge archive
written against a MiniZinc the current compiler no longer speaks. **Nothing in
this row is a propagator gap and only one line of it decomposes anything.**

| bucket | count | after M7-T15 |
|---|---|---|
| `is_output` undefined | 16 | **14 flatten**; 2 hit a further, pre-existing incompatibility |
| string-valued `int_search` | 8 | **8 flatten** (one also needed the gcc bridge below) |
| `maximum of empty set` | 2 | unchanged, and **confirmed the models' own** |
| harness data pairing | ~20 | not this row (M7-T14's file, agent-harness2) |

**22 of the 24 this row owns now flatten**, measured on `fataepyc-07` against the
committed library, not inferred from a local test.

### `is_output` cannot be aliased, and the residue is stated rather than hidden

`is_output` is 1.x's "this declaration belongs in the solution output". 2.x's
`add_to_output` has exactly that meaning, and the natural move is to alias onto
it. **Both spellings were measured on 2.10.1 and neither works**: `ann: is_output
= add_to_output;` type-checks and is inert — the compiler recognises
`add_to_output` by the identifier written at the *declaration site*, not by the
value it denotes — and `annotation is_output = add_to_output;` is rejected, leaving
the identifier undefined. A bare `annotation is_output;` is all that is available.

So output falls back to MiniZinc's default, which prints every top-level variable:
a **superset** of what the model asked for. That is worth stating plainly because
the failure it is *not* is the dangerous one. A variable the model asked for and we
silently dropped would be a wrong answer in the FlatZinc output format with nothing
to signal it; a variable printed that nobody asked for is noise.
`test/models/is_output_shim_sat.fzn` pins the superset so a future change cannot
turn it into a subset unnoticed.

### The one decomposition, and why it was right *here*

`2008_debruijn_binary` calls `global_cardinality(x, counts)`, 1.x's two-argument
form whose cover is the index set of `counts`. The shim spells the cover out and
hands the call to std's three-argument predicate, which decomposes it.

D-0067's rule is to keep a global whole for the propagator that wants it. **There
is no such propagator**: baguette has no `global_cardinality`, so there is nothing
here to keep the constraint whole *for*, and std would have decomposed the 2.x
spelling of the same call identically. Refusing the bridge would not have preserved
a global; it would only have kept the instance from reaching the solver. A
`global_cardinality` propagator is the better answer and is a roadmap item, not a
reason to withhold the bridge. **This is the shape of argument a future
decomposition should have to make** — "std decomposes it either way and we have no
propagator", not "it was easier".

### The failure this row met, which is a property of `mznlib/` and not of this shim

The first version of the bridge called std's three-argument predicate **without
including `global_cardinality.mzn`**. `redefinitions.mzn` is pulled into *every*
model, so every body in it must type-check in every model — including the majority
that never include `globals.mzn`. The unresolved call was reported as a type error
**against the library**, and **twelve instances with nothing to do with cardinality
went from flattening to `FLATTEN-FAIL`**. The confirmation run over all 24 read
`ok=12` before the include and `ok=22` after it.

**It was caught only because the confirmation run was done over all 24 together
rather than bucket by bucket**, which is the practice worth keeping: the per-bucket
runs were all green, because each bucket's models happened to include
`globals.mzn`.

**The repo's gate cannot see this class of bug at all.** Everything under `test/`
consumes FlatZinc, and this defect lives on the MiniZinc side of the boundary.
`mznlib/test/check_mznlib.sh` is the answer: it flattens `bare.mzn`, which includes
nothing, and re-flattens each provenance model to check it still yields the body
committed under `test/models/`. It needs a MiniZinc binary, which the dev
environment does not have, so it is **run by hand and is not in `make check`** —
and with no flattener it FAILS rather than skipping, for the reason
`scripts/checker.sh` gives about a missing checker.

### The three residual failures, confirmed not ours

Each was re-run **under Gecode's own library**, with only `annotation is_output;`
supplied, and fails identically there:

- `2021_yumi-dynamic`, `2022_yumi-static` — *maximum of empty set is undefined*,
  in the model's own par declarations.
- `2009_p1f` — the model defines `predicate circuit(...)` itself, which has since
  entered the standard library; 2.10 calls the overload ambiguous. Shadowing std's
  `circuit` from `mznlib/` to paper over this would be exactly the wrong trade.
- `2009_search_stress2` — the model's own `assert` on `dom(x)`, which 2.x no longer
  satisfies.

A 2009 model that the 2026 compiler rejects on the model's own terms stays
`FLATTEN-FAIL`. The corpus is the subject of the measurement and is not edited.

### Cost

No regression: a 60-instance sample of instances that already flattened gives an
identical 31/29 split under the old and new libraries. The four new model tests
pass with their proofs accepted by veripb 3.0.2.

Follows D-0067 (the library) and D-0074 (the run that counted this).

## D-0077  The assignment decision: a disjunctive sibling is discharged by DERIVATION, not by resolution
Status: DECIDED
Date: 2026-09-23
Task: M7-T12 (agent-decision, wave 30).
Touches: `lib/core/search.ml`, `lib/flatzinc/{model,builder,compile}.ml`, `docs/SPEC.md`
section 3.4, `test/unit/{test_learn,test_compile,test_flatzinc}.ml`, three new models.
Follows D-0019 (a disequality is a two-literal clause, not a direct-encoding literal),
D-0018 (the trace, and what a line may mention), D-0070 and D-0075 (a right answer with a
wrong emitted line), D-0053 and D-0066-as-amended-by-D-0073 (which answers a break lane
may be checked over). Closes M7-T12 and lifts SPEC 3.4's `indomain_median` refusal.

### The problem, stated once

A baguette decision was a SINGLE ORDER LITERAL: `x <= k` on one side, `x >= k+1` on the
other. `indomain_min` and `indomain_max` are exact under that **by accident of sitting at
a domain boundary** -- `x <= lo` *is* `x = lo`, and `x != lo` collapses to the single
literal `x >= lo+1`. An interior `m` has neither property. `x = m` is two literals
(`x >= m AND x <= m`), and its sibling `x != m` is a **disjunction**
`x <= m-1 \/ x >= m+1` (D-0019).

That is not a value-choice problem. A nogood is a clause of NEGATED ASSUMPTIONS, and the
negation of a disjunctive assumption is a conjunction, which no clause can hold. So the
sibling of an assignment cannot be named in a nogood at all, and `combine_nogoods`
resolving two children on exactly one literal has nothing to resolve. M7-T9 refused
`indomain_median` for exactly this reason rather than substituting a bisection, and that
refusal was correct.

### What was built, in three moves

**1. The `x = m` branch is TWO STACKED ORDINARY DECISIONS**, `x >= m` at one level and
`x <= m` at the next. Not one level with two pushes. This is the single most important
choice in the row, and it is what kept the blast radius small: every existing invariant
holds verbatim. Each push is the first trail entry of its own level, so
`check_decision_landed` is untouched; `levelled_nogood` still reads one literal per level;
`bridges` still pairs decision entries with decision literals one to one; `Trace` still
skips both pushes because both are level starts. **No nogood machinery changed.**

**2. The failed branch's nogood is WEAKENED, and weakening is the whole proof
obligation.** The child's nogood `ng` names `x <= m-1` at the lower level and `x >= m+1`
at the upper -- the negations of the two decisions. Re-level those two onto the node's own
level, add whichever `ng` did not name, keep everything else, and the result

    C1  =  (ng's outer literals)  \/  x <= m-1  \/  x >= m+1

is a **SUPERSET of `ng` as a set of literals**. A superset of a RUP clause is RUP:
negating it asserts everything negating `ng` asserts, so the same unit propagation reaches
the same contradiction. That is the entire argument, and it needs nothing about this
search.

Its ONE precondition is that the literals dropped are exactly the two the assignment put
there -- i.e. that a nogood is everywhere a set of negated decisions tagged with their
levels. That is true (`levelled_nogood` builds it that way; `minimise`, the `Learn.levels`
filter and `combine_nogoods` only ever remove from it) and it is now a `Debug.check`
rather than a paragraph, because if it ever stopped being true the drop would STRENGTHEN
C1 instead of weakening it, the hole below would be punched on a clause the node does not
entail, and on an UNSAT instance nothing would say so (D-0066).

**3. THE SIBLING IS NOT A SIBLING.** C1 is globally valid, and under the decisions in
force at this node it says exactly `x <> m`. So `x <> m` is not an assumption to branch
under: it is a DERIVED FACT at the node that already exists. The value is removed from the
domain at the node's own level, with C1 as the pruning's justification and the active
decisions as its reason, and `dfs` is RE-ENTERED on the unchanged decision stack. M5-T1's
branch-and-bound re-entry is the same move and carries the same argument: no level is
reopened, no decision is re-taken, the tree is still traversed once, left to right.

### THE RESOLVENT, AND WHY THE BACKJUMP IS SOUND

**There is no resolvent, and that is the answer rather than a gap.**

The node's nogood is whatever the re-entry returns, **unresolved and unmodified**. Three
facts make the unmodified clause the right one to hand up:

  - it is valid under the outer decisions, because that is what a nogood is;
  - it names no literal of either assignment level, because those levels were CLOSED
    before the re-entry began and the re-entry's decision stack is the outer one. There
    is no level for such a literal to be tagged with;
  - therefore the `mentions_level` test the frame above applies to it -- the test that
    licenses a backjump -- is evaluated over exactly the assumption set the clause is
    valid under, which is the property that test has always needed and the only one it
    has ever needed.

So the backjump level is `filed_at`, computed by the unmodified rule, and it is sound for
the unmodified reason. The disjunctive sibling is discharged by DERIVATION, not by
RESOLUTION. **A change to `combine_nogoods` was the row's stated scope and turned out not
to be needed; saying which half of a row's premise was wrong is the record's job.**

The second arm is the backjump THROUGH an assignment: the child's nogood names neither
assignment level, so it refutes the node whatever the variable takes, no clause is written
about the assignment and the value is never removed. That arm is where an unsound
resolvent would live if this shape had one, since it is the only place the assignment's
levels are discharged with nothing emitted about them; `test_learn.ml`'s M7-T12 (d)
asserts on the spectator being decided exactly ONCE.

### HOW THE TWO BRANCHES ARE WRITTEN

- **`x = m`**: nothing at all for the decisions. Two levels open and two trail entries
  land, and D-0018's rule that a decision gets no line applies to both because both are
  level starts. The subtree's trace, bridges, learned clause and nogood are byte for byte
  what they would be under any other pair of decisions.
- **`x <> m`**: no decision line either, because it is not a decision. What appears is
  ONE clause -- C1, a `rup`, filed at the node's own level -- and then the ordinary trace
  line for an ordinary pruning, `rup +1 ~x_ge_m +1 x_ge_(m+1) +1 ~d1 ... >= 1`, whose tail
  is the decisions in force. That line is C1 weakened by any decision C1 had already
  minimised away, so it is RUP against C1 and never stronger than it.

**C1's LIFETIME is the one new I-X2 obligation.** The re-entry's every line rests on it:
the hole's line is RUP against it, every later pruning that reads the hole cites the
hole's reason (D-0075's mechanism, unchanged), and the re-entry's nogood is RUP along that
chain. C1 is filed at the node's level, so the frame owning that level wipes it on the way
out -- after the re-entry has returned. At level 0 nothing wipes, so `Search` records those
ids and `retire_assign_clauses` deletes them at the end of the search, beside `Trace`'s
permanent lines and `Retention`'s learned ones. Those two sentences are the whole of it.

### I-X10 GAINS ITS FIRST EXCEPTION, STATED

`trace.ml`'s header says "**no decision ever appears in a trace line**, and every line is
globally valid on its own". The hole's line breaks the first clause and keeps the second:
it names the active decisions in its tail, and it is globally valid because it is C1
weakened. This is the only line in `lib/` that does. The alternative -- stating `x <> m`
with an empty tail -- is **D-0075's defect exactly**, a line that is not merely underived
but false, and it is what `break_assign_facts` produces.

### WHAT WAS MEASURED RATHER THAN PREDICTED

**The D-0075 break lane was GREEN on the first model it was written against, and the
model was the bug.** Trace lines are written lazily, only when a branch fails, so the
hole's line is emitted -- and therefore checked -- only if the re-entry that follows the
hole goes on to fail deeper. The first nested scene's re-entry succeeded immediately, no
trace was written, and an empty tail was invisible. A third exclusion row fixed it. This
is D-0075's own note about its reproducer's `q1/q2/q3`, rediscovered from the other side,
and it is the reason `median_assign_under_decision_sat.fzn`'s header argues for every row
it contains.

Both breaks redden at the checker's full wording ("The constraint is not implied by
reverse unit propagation (RUP) from core and derived database"), over SATISFIABLE scenes,
each with a control proving the unbroken scene verifies.

### THE DISPATCH, AND WHY IT MATTERS

`indomain_median` returns an `Assign` only for a STRICTLY INTERIOR median. At the lower
bound it returns `indomain_min`'s decision and at the upper bound `indomain_max`'s,
because there the one-literal shape is exact. A domain of two values always lands at the
boundary. So the new machinery is reached only where it is genuinely needed, and every
model whose medians all sit at a boundary emits the proof it emitted before. That is not
an optimisation: it keeps the new shape's blast radius equal to its necessity.

The median is the LOWER median -- the value at index `(size-1)/2` of the domain's values
ascending, Gecode's `INT_VAL_MED`. It counts VALUES, which is exactly what distinguishes
it from `indomain_split`'s range midpoint; over `0..6` with `3` removed the two are 2 and
3, and `test_flatzinc.ml` asserts both on the same domain.

### THE STATS IDENTITY

M1-T36's `nodes = 2 * decisions + 1 - skipped` gains one term and stays an EQUALITY. An
assignment bumps `decisions` by 2 and dispatches ONE child, so it contributes 1 node where
the equation expects 4: `- 3 * assigns`. `skipped` is NOT bumped on the backjump arm --
an assignment has no sibling to skip, and those three nodes are already subtracted --
which was found by the identity failing, not by reading. `assign_backjumps` counts that
arm instead.

### WHAT THIS DOES NOT DO, AND WHAT IT OPENS

**Staged, deliberately.** `all_different`'s value-graph branching and M4's element rows
were named as the real reasons to build this, and neither is wired to it. What they need
is the SHAPE -- an assignment decision with a disjunctive sibling, and a contract saying
what its refutation is -- and that is here and is general: nothing in `branch_assign`
knows about medians, and `Search.Assign` is an ordinary `choice` any order may return.
What is NOT here is a value-graph criterion, a matching-based order, or an assignment over
the DIRECT encoding. The last is the one to check before assuming this generalises: a
direct-encoding assignment would claim `x = m` as a single literal, and D-0019 point 3's
test for when that is forced applies to it and not to this.

**`combine_nogoods` is untouched**, so a decision shape whose two children are BOTH
explored and must resolve on two literals is still not expressible. This row did not need
one and does not provide one.

### SPEC 3.4 WAS CHANGED, AND IT IS A NORMATIVE DOCUMENT

The `indomain_median` refusal paragraph is gone, replaced by the strategy's definition and
by the dispatch. The refusal genuinely went away -- it was not weakened into an acceptance
-- and the sentence it stood under is untouched: substituting a strategy still solves a
different problem, and `anti_first_fail`, `indomain_random`, `float_search`, `set_search`
and `priority_search` are still refused by name, at full strength, with their own lanes.
## D-0078  A `global_cardinality` propagator: the counting row lives in the ORDER encoding, and the interval capacity is what the decomposition cannot reach

**Status**: **ACCEPTED**, implemented by M7-T16 (2026-09-23, agent-gcc).
`lib/core/prop/gcc.ml`, `lib/flatzinc/{model,builder,compile}.ml`,
`mznlib/fzn_global_cardinality.mzn`, four model lanes.

### What was built, and what was deliberately not

Two filtering rules, both bounds-level reasoning.

**Rule A -- interval capacity.** For an interval `[a, b]` all of whose values are in the
cover, `cap = sum_v (hi(c_v) - const_v)` and `H = { i : [lo_i, hi_i] inside [a, b] }`.
`|H| = cap` pushes every other variable out of `[a, b]`; `|H| > cap` refutes. **With every
capacity 1 this IS all_different's Hall rule**, which is the sense in which gcc is
all_different's generalisation and this module is shaped on `alldiff.ml`.

**Rule C -- the count bounds.** `hi(c_v) := may_v`, `lo(c_v) := must_v`, over possible and
certain takers. This is what makes the propagator a checker, and it is also how a
shortfall becomes a refutation: too few possible takers empties the count's domain.

**Not built, and named rather than omitted**: no flow (domain consistency is Regin's
argument and is a later row, as stage 2 was for all_different); and no interval
LOWER-capacity rule -- its per-value case is exactly what the decomposition's own linear
row already propagates, so it would not earn its justification in the row whose thesis is
that the global infers what the decomposition cannot. The line its interval case needs is
written out in `gcc.ml`'s header so the next stage starts from a sentence.

### The counting row cannot live in the direct encoding, and that turned out to be a gift

A tally is naturally `sum_i x_i_eq_v`, which is what `alldiff`'s Hall derivation counts
over. **It is not available: the direct encoding does not exist when the `.opb` is
written.** `Encoding.start_proof` introduces it with `red` (PROOF-FORMAT §3), so a model
row naming `x_eq_v` names variables the model file has never heard of. `all_different`
does not meet this because its model rows are pairwise disequalities over ORDER literals;
a counting row has nowhere to hide.

The identity `[x = v] = x_ge_v - x_ge_(v+1)` makes the same tally linear in literals the
`.opb` already has. Three consequences, all of them wins:

1. **The derivation names no direct literal at all** -- no channelling clauses, no
   at-least-one line, none of the width-proportional machinery D-0028 charges for, which
   `all_different` pays for in full. (`compile.ml` does still call `request_direct` for
   the gcc scope, and *not* for the derivation: see the `derive_ahead` defect below.
   That call is a stopgap and is the one thing standing between this row and "no direct
   encoding".)
2. **"x lands in `[a, b]`" telescopes** to `x_ge_a - x_ge_(b+1)`, so the at-least-one line
   a Hall argument needs is not derived from the channelling -- it is the variable's two
   bound facts.
3. **The pruning needs no channelling telescope either.** What the counting leaves is
   already a statement about order literals.

### A bound a DECISION moved has no unit line, and none is derivable

This is the finding that cost the most and is the one to carry forward. The derivation
wants `x >= lo(x)` at UNIT strength, and D-0064's `Explanation.defining` supplies it for a
root-established bound. Under a decision there is no such line: **a decision is not an
assumption in this proof format**, nothing states it, and `Justify.defining_lit`'s minted
`rup ~n1_ge_1 >= 1` is refused by 3.0.2 with *"not implied by reverse unit propagation"*.
Measured, on `test/models/gcc_search_sat.fzn`'s first branch.

The resolution is `alldiff.ml`'s and it generalises: **do not ask for the unit.** Sum
LADDER CHAINS, which are globally valid and free, and let the bound literal stay in the
row. What comes out is `<the pruning> \/ ~<the bounds it read>` -- the `Ne` shape, sound at
any level -- and the pruning's `Reason` carries the same bounds, which is what makes the
trace line true (I-P5) and RUP. `bound_cancels` removes a literal where, and only where,
the bound is a root one, which is the case that matters: a ROOT conflict must derive
`0 >= 1`, and a row with literals left in it is not contradicting.

**A corollary worth stating on its own**: the degree of "x lands in `[a, b]`" is two units
and the ladder gives away one. The missing unit is the bound fact, and it cannot be
conjured. Any future propagator that needs a decision-dependent fact at unit strength
needs the direct encoding's at-least-one line, or it needs this trick.

### The overshoot, which `alldiff` shipped latent and this row met

`alldiff.ml`'s `overshoot_cancel` has a counterpart here and it was written only after
3.0.2 said *"the constraint with ID 48 is not contradicting"*. The conflict arm pushes a
confined variable past its own upper bound; when the interval's top is at or above that
variable's DECLARED top the residue is the constant false and the row is `0 >= 1` for
nothing -- and that is the case every model with declared-narrow variables reaches. When
only the CURRENT top is inside, the residue is a real literal, the row derives a perfectly
valid `u >= 4`, and the refutation is not a refutation.
`test/models/gcc_hall_narrowed_unsat.fzn` exists to keep that closed: its variables are
declared `1..4` and narrowed to `2..3` by linear rows, which is the only shape that
exercises it.

### Two defects the I-X10 gate found, and neither was in the counting

**(1) `Trace.derive_ahead` under-triggers.** It fires on `Encoding.has_direct` of the
pruned variable, and its own comment describes that as deliberately OVER-triggering --
an `int_lin_le` pruning of an `all_different` variable gets a `pol` it did not need. It
also UNDER-triggers, and gcc is the first family to show it: gcc's rows are over the
order encoding and it names no direct literal anywhere, so `has_direct` was false for its
whole scope and **every gcc trace line went out as a bare `rup`**, which 3.0.2 refused.
Bought back by requesting the direct encoding for the gcc scope purely to arm the
trigger, spelled out at the call site. It costs the width-proportional `red` lines
(D-0028) for an encoding nothing reads, so it is a stopgap: the real fix is a marker that
says "this pruning needs its derivation ahead" as a property of the propagator, which
`trace.ml`'s comment already names ("a per-entry flag threaded from the propagator through
`Store.entry`"). Filed as a cross-session request against `lib/core/trace.ml` and
`lib/proof/encoding.ml`.

**(2) D-0010's CURRENCY, and this one would have shipped silently.** What the counting
leaves is a single order literal, `y_ge_(b+1) >= 1`. That is a true statement of the new
bound and it is **not** what another propagator can combine with: an order literal is 0/1,
so a bound is worth its whole prefix of the ladder, which is the substitution
`encoding.ml` performs on the model side and `order_reason.ml` exists to restate. A
`Linear` row summed against the single literal is short by exactly the rungs beneath it,
and 3.0.2 answers *"the constraint with ID n is not contradicting"*. Measured on a gcc
capacity push of `u` to 5 consumed by `int_lin_le([1],[u],4)` at the ROOT.

**Why `all_different` never showed it**, and this is worth writing down because it is
luck rather than design: alldiff's derivations still reach `Explanation.clause` often
enough that `search.ml`'s `rests_on_a_clause` routes those root conflicts the D-0022 way,
where `conclusion UNSAT` cites the empty clause and **nothing the checker does depends on
the Hall arithmetic being right** -- which is the sentence alldiff.ml's own header already
makes about `Explanation.Clause`, arriving from the other side. gcc's derivation is
`Defining` all the way down, so it takes the numeric route, and the numeric route is where
the currency matters. `Gcc.ladder_lift` is the fix: W copies of the single-literal
derivation plus one chain per rung beneath the pushed bound.

### NO NEW `Explanation` CONSTRUCTOR

`Combine`/`Weaken`/`Model_row`/`Defining` throughout, plus `Model_row` on the ladder rungs.
D-0044's bet is not spent. `Weaken` is used in **both** of its directions and the sign is
what decides which: cancelling a NEGATIVE term costs nothing, cancelling a positive one
costs the unit of degree D-0009 describes. `Combine`'s divisor does real work in exactly
one place -- `ladder_at_most`/`ladder_at_least`, where a single division rounds the degree
up to 1 and turns a bound on the count's ladder into the one literal about it.

### The declaration is `Checking`, and that is a measured under-claim

The filtering is bounds-level reasoning, but the tag is `Propagator.Checking`, which is
what the M2-T10 oracle holds a propagator to. Bounds consistency for gcc is
Quimper/Katriel's algorithm, not the capacity-Hall rules here, and with VARIABLE counts it
additionally has to reach a fixpoint between the count bounds and the interval capacities;
nothing in the module proves that it does. `all_different` could declare `Bounds` at stage
1 because Hall intervals ARE bounds consistency for all_different (Puget) -- there is no
such theorem for what is written here, and **a declaration the oracle falsifies is a crash
at a search node, not a warning**. What `Checking` does oblige, rule C delivers.

### The numbers, both ways

Native gcc against the per-value decomposition, hand-written in the shape
`std/fzn_global_cardinality.mzn` produces (one `int_eq_reif` + `bool2int` per variable per
cover value, summed against the count by an `int_lin_eq`). Same solver, same checker,
same machine; both sides `s VERIFIED`.

| model | `.opb` | `.pbp` | lines | `pol` | `rup` |
|---|---|---|---|---|---|
| `gcc_search_sat` (SAT, under search) | **575 B** | **1 169 B** | **45** | 15 | 5 |
| the same, decomposed | 3 236 B | 26 340 B | 697 | 0 | 520 |
| `gcc_capacity_unsat` (UNSAT) | **311 B** | **170 B** | **9** | 3 | 0 |
| the same, decomposed | 2 957 B | 6 535 B | 188 | 0 | 133 |
| `gcc_capacity_sat` (SAT, settled at the root) | **523 B** | 191 B | 8 | 0 | 0 |
| the same, decomposed | 3 497 B | 384 B | 8 | 0 | 0 |

**22x on the proof and 15x on the line count** where there is a search to do, 38x and 21x
on the refutation. The `.opb` is 5-10x smaller in every row, which is the direct encoding
the decomposition needs and this does not.

**Read the `pol`/`rup` columns as well as the sizes, and this is the more interesting
half.** The decomposed proofs are **entirely `rup`** -- 520 lines and 133 lines of it,
zero `pol`. Per D-0066-as-amended a `rup` line is checkable only when it is load-bearing
for a later line, so most of what the decomposition emits is a proof artefact the checker
walks past. gcc's proof is 15 `pol` against 5 `rup`: a `pol` is *computed* by the checker
and cannot be vacuous. **The decomposition is not merely larger, it is larger in the
currency that proves less.**

Caveat, stated rather than buried: the two sides of the search rows do not explore the
same tree, because the propagators differ -- that is the point of the comparison, not a
confound, but it means the ratio is a property of this model and not a constant.

### On the REAL instance the proof came out BIGGER, and the cause is named

`2008_debruijn_binary` (`02_03.dzn`), on `fataepyc-07`, both binaries hashed and
distinct, both proofs `s VERIFIED SATISFIABLE`, **answers byte-identical**.

| | decomposed (`main`) | native gcc |
|---|---|---|
| `.fzn` | 13 886 B, 78 constraints | **8 578 B, 45 constraints** |
| `.opb` | 69 643 B, 504 rows | **63 128 B, 412 rows** |
| `.pbp` | **25 202 B, 195 lines** | 28 552 B, 235 lines |
| of which `red` | 176 lines, 18 320 B | 208 lines, 21 508 B |
| `pol` | 8 | 16 |

**The model shrinks by 38%, the `.opb` by 9%, and the proof GROWS by 13%.** That is the
opposite of what this row set out to show and it goes here rather than in a footnote.

**The cause is not the counting argument; it is the `derive_ahead` stopgap above.** The
whole of the excess is `red` lines -- 32 more of them, 3 188 bytes -- and every one is a
direct-encoding introduction for a variable *whose derivation never names a direct
literal*. `compile.ml` requests that encoding only to arm `Trace.derive_ahead`'s
`has_direct` trigger. The `pol` count doubles (8 -> 16), which is the counting argument
actually appearing, and it costs a few hundred bytes.

So the prediction stands with a condition attached: **the native global is smaller in
every artefact the propagator controls, and larger in the one the stopgap controls.**
Fixing the trigger is what settles it, and that is the cross-session request, not a
further propagator change. Anyone quoting the controlled numbers above should quote this
row beside them.

### The lane that would have proved nothing

`gcc_capacity_sat.fzn` is the model the row was designed around -- gcc prunes at the root
what the decomposition cannot -- and **its proof contains no gcc reasoning at all**. A
propagation emits its justification only when a later line needs it (`trace.ml`'s deferred
explanations), so a model the propagator settles at the root verifies a proof that is a
header and a `sol` line. **The same is true of `test/models/alldiff_hall_sat.fzn`**, which
has been green since M4-T1 and whose proof contains the `red` lines of the direct encoding
and not one step of the Hall derivation.

That is D-0053's shape in a new dress and it is worth a sentence of its own: *a green lane
over a model your propagator settles at the root is not evidence that its justification is
right.* `gcc_search_sat.fzn` is the answer here -- a search annotation that branches on the
counts, smallest value first, makes the first three guesses wrong, and each failure's
nogood rests on the derivation that reached it. 15 `pol` lines over a SATISFIABLE model,
which is the condition D-0053 insists on and which a refutation lane cannot supply.

### Three refusals, with a source position

A cover and counts of different lengths; a count that is a literal constant rather than a
variable (the rows subtract the count's ladder and a constant has none -- declare it on a
single value, which IS supported and is what every model lane uses); and the same variable
twice in the array, whose tally contribution would be 2 where every cancellation assumes
1. `all_different` can let a repeat through because its pairwise decomposition refutes it;
there is no such decomposition here, so it is refused rather than mis-counted.

### D-0076's condition has expired

M7-T15 bridged 1.x's two-argument `global_cardinality` onto std's three-argument predicate
and let std decompose it, and argued the case in the form *"std decomposes it either way
and we have no propagator"*. That was the right argument and it names its own expiry
condition. `mznlib/fzn_global_cardinality.mzn` now declares the inner predicate bodyless,
so the same bridge lands on the propagator; **nothing about the bridge itself had to
change.**

## D-0079  The wave-30 corpus run: 58 verified, 0 rejected, and the blocker is now TIME

**Status**: **MEASUREMENT**, recorded 2026-10-01 by the orchestrator from
`/scratch/arthur/corpus-out-w30` on `fataepyc-07`. The run is complete
(`DONE-1790256627  436  436`, finished 2026-09-24), `PAR=64`, 32 GB per job,
`--max-heap-mb 15625`, 300 s solve timeout, 120 s flatten timeout, every solved instance's
proof checked by veripb 3.0.2. The binary was the wave-30 tip: the `fzn_global_cardinality`
refusals below carry M7-T16's own wording, so the gcc propagator was in. It is the baseline
a comparison against Chuffed and GCS starts from, and it set wave 31's agenda.

### The result

| outcome | wave 30 | wave 27 (D-0074) |
|---|---|---|
| `TIMEOUT-SOLVE` (300 s) | **273** | 155 |
| `REFUSED-RESOURCE` | 58 | — (bucket did not exist) |
| **`OK-PROOF-VERIFIED`** | **58** | 33 |
| `NO-DATA` | 20 | — (was inside `FLATTEN-FAIL`) |
| `REFUSED-MODEL` | 10 | 107 |
| `REFUSED-LIMIT` | 9 | 74 |
| `FLATTEN-FAIL` | 4 | 50 |
| `SOLVE-ERR-134` | 3 | 15 |
| `FLATTEN-TIMEOUT` | 1 | 1 |
| **`PROOF-REJECTED`** | **0** | 1 |

### What it says

1. **Every proof the solver produced was accepted.** 58 of 58, `2012_tpp` among them at
   38.5 MB, so D-0070 and D-0075 were the whole of the bucket. The caveat is D-0066's: an
   UNSAT instance accepts a defective `rup` silently, so the SAT instances are the evidence
   and the UNSAT ones are not. The proofs range from 120 bytes to 82 MB (`2013_rubik_5-cube`);
   ten are above 20 MB. Proof size is a comparison axis against GCS and these are its
   first real numbers.
2. **The front end is no longer the wall.** `REFUSED-MODEL` went 248 → 107 → 10, and the
   ten are three messages in full: value choice `indomain` ×4, variable selection
   `anti_first_fail` ×2, `var int` with no domain ×4 — **M7-T19**. The 9 `REFUSED-LIMIT` are
   ONE message, `fzn_global_cardinality` with a constant count — **M7-T18**.
3. **The wall is time: 273 of 436, 63%.** Nothing in the roadmap says where the time goes
   on an instance this project did not write: M6-T1 profiled the hand-written suite, where
   emission was 2–4% and only 10 of 64 models carried signal at all. Worse, the solver
   cannot say what it was doing when `timeout` killed it — there is no `--time-limit`, so a
   timed-out run leaves no stats, no incumbent and no proof. **M6-T9** is the diagnosis;
   the fix is whatever the diagnosis names, and not before.
4. **The 58 `REFUSED-RESOURCE` are D-0028's cost, not a defect.** 54 are a declared width
   between 10 000 and 40 million (`2018_steiner-tree`'s objective is `0..40330252`); 4 are
   the heap budget (`2009_prop_stress`, `2013_l2p`, `2016_carpet-cutting`,
   `2018_test-scheduling`). The 3 `SOLVE-ERR-134` have the same shape — widths 144 400,
   605 284 and 78 million — and abort before the heap guard fires. These are out of reach
   without a different encoding of wide domains. That is a decision this record does not
   take; the instances stay in the comparison set as what they are.
5. The input side is the corpus's: `NO-DATA` 20, `FLATTEN-FAIL` 4 (the models' own, M7-T15
   confirmed each under Gecode's library), `FLATTEN-TIMEOUT` 1 (`2025_gt-sort`, a JSON
   data file).

### What follows

Wave 31 (2026-10-01): M6-T9 the time diagnosis, M6-T4 the three-solver harness with GCS
built on the node and Chuffed from the MiniZinc 2.10.1 bundle, M7-T17/M7-T18 on gcc,
M7-T19 on the ten refusals. The comparison can start once (a) Chuffed and GCS run under one
harness that checks agreement between solvers — the first external oracle this solver has
ever had — and (b) baguette reports at a time limit instead of being killed.

## D-0080  Where the 300 s go: a stopped run is now a checked proof, and the time is in quadratic bookkeeping, not in search

**Status**: **MEASUREMENT + one shipped fix**, recorded 2026-10-01 by agent-perf (M6-T9),
branch `wave31-perf`. Every number below is from `fataepyc-07`, MiniZinc 2.10.1 flattening,
veripb 3.0.2 checking, `corpus_run.sh` at `PAR=64`, 32 GB per job, `--max-heap-mb 15625`,
`SOLVE_TIMEOUT=300`, `SOLVER_ARGS="--time-limit 280 --stats --time"`, `RSS=1`. The instance
set is the 273 wave-30 `TIMEOUT-SOLVE` ids plus the 58 wave-30 `OK-PROOF-VERIFIED` ids (the
timing reference), 331 in all; configs (a)-(d) are COMPLETE (their `DONE-` markers are in the copies under
`bench/m6t9/results/<cfg>.tsv`; originals in `/scratch/arthur/perf-out-<cfg>/`); config (e)
is NOT (below). Binaries, hashed on the node:

| tag | commit | md5 of `main.exe` | what it is |
|---|---|---|---|
| OLD | `5955d31` | `a04c77fda02664ee74a40d9480acda92` | `main` + `--time-limit` only (no fix) |
| NEW | `ca9c6b2` | `66c0944c60105a4e42334bdcad6d3cf7` | OLD + the `Pb_analysis.falsified_at` fix + SIGTERM line + `BAGUETTE_NODE_LIMIT` |
| MEMO | `ca9c6b2` + `bench/m6t9/justify-memo.patch` | `2e49df4f53a86c43ef9e6b72150d4566` | NEW + the PROPOSED `Justify` memo (not on any branch: `justify.ml` is the orchestrator's) |

### What M6-T9 added, so that the numbers exist at all

* **`--time-limit S`** (process CPU seconds, `Sys.time`: `bin/` links no wall clock, a
  request is filed). Checked at every node entry through `Search.config.stop`; on expiry the
  search sweeps every live id (I-X2) and ends `output NONE` / `conclusion NONE`, and raises
  `Search.Stopped` with the incumbent. stdout is `=====UNKNOWN=====` when nothing was printed,
  otherwise the improving solutions already printed and no `==========`; stderr gets one
  `limit: reached ...` line; exit 0. **veripb accepts the stopped proof — `VERIFIED NO
  CONCLUSION` — on 142 stopped runs of config NEW (a'), and those 142 are this project's
  first checked record of what a timed-out run derived, learned constraints included.**
  `test_endtoend` pins it on a 4-into-3 pigeonhole stopped at node 7 and an optimisation run
  stopped after its first incumbent, with the break: `conclusion UNSAT` in place of NONE is
  refused, "There is no contradicting constraint in the database."
* `BAGUETTE_PB_ANALYSIS=off` (config d), `BAGUETTE_NODE_LIMIT=N` (the deterministic stop that
  makes two builds byte-comparable), a `stats: conflicts` counter, and a SIGTERM handler that
  prints `limit: killed phase=... nodes=...` so a `TIMEOUT-SOLVE` row says where it was.
* `corpus_run.sh`, additively: `SOLVER_ARGS`, `NO_PROOF=1`, `RSS=1`, the `UNKNOWN-LIMIT` bucket
  with a compact stats detail. Selftest green; `--report corpus-out-w30` byte-identical (md5
  `69a2120379138e415cb625bc90b24817` before and after).

### Two harness defects the sweep found (both fixed, both D-0069's failure mode)

1. **TIMEOUT-CHECK could never fire.** `rc=$?` was read *after* `if timeout ... veripb ...;
   then ...; fi`, which is the if-statement's status — 0 when the condition failed. Every
   checker timeout since M7-T4 was filed as `PROOF-REJECTED`. Config OLD has four such rows
   (`2013_league`, `2014_openshop`, `2023_test-scheduling`, `2025_skill-allocation`, `.vp` =
   the banner only); one was re-run and exits 124 at 900.09 s. Fixed in `2dda188`.
2. **A rejection is now gated on the checker's wording** ("Verification error"); a non-zero
   exit without it is `CHECK-ERR-<rc>`. (Config NEW ran with this gate and the rc bug, so its
   9 `CHECK-ERR-0` are checker timeouts; configs c and d ran with both fixes and say
   `TIMEOUT-CHECK`.)

### The sweep

`fin` = `OK-PROOF-VERIFIED` (or `SOLVED-NOPROOF` for b). nodes/s is over the runs that stopped
at the limit (n in brackets); `search`/`emit` are the summed `--time` rows over every row that
printed them; `emit` is a LOWER bound (it excludes building each line, M1-T47).

| config | binary | fin | stopped & checked | killed (TIMEOUT-SOLVE) | REJECTED | nodes/s min / p25 / **median** / p75 / max | RSS median / max (MB) | emit / search |
|---|---|---|---|---|---|---|---|---|
| (a) default | OLD | 57 | 122 | 137 | 15 (11 real + 4 checker timeouts) | 0.00 / 0.65 / **1.44** / 10.6 / 61 (122) | 228 / 19672 | 0.2 % |
| (a') default | NEW | **73** | 142 | 78 | 26 | 0.01 / 2.46 / **10.8** / 21.9 / 62 (142) | 369 / 13401 | 0.6 % |
| (b) no `--proof` | NEW | 74 | 179 | 76 | — | 0.00 / 2.17 / **10.5** / 21.5 / 64 (179) | 378 / 16633 | 0.6 % |
| (c) `lbd:16` | NEW | 73 | 146 | 73 | 26 | 0.00 / 2.14 / **10.7** / 21.5 / 62 (146) | 370 / 13403 | 0.6 % |
| (d) PB analysis off | NEW | 72 | 157 | 48 | 27 (+27 TIMEOUT-CHECK) | 0.01 / 3.35 / **15.5** / 28.4 / 65 (157) | 317 / 13402 | 0.7 % |
| (e) proposed memo | MEMO | **not measured** — in flight (~31 of 331 rows, no `DONE-`) when node access was cut; its `results.tsv` was not copied. Needs the node | | | | | | |

Per instance, against (a') on the runs stopped in both: (b) nodes/s ratio median **1.007**
(n=138) — writing the `.pbp` to disk rather than to a temporary file costs nothing measurable,
and note what (b) is NOT: without `--proof` the CLI still logs to a temporary file
(`bin/main.ml`'s header, SPEC 1), so no config here measures "no proof logging". (c) ratio
**1.00** (n=141), and on the 73 instances solved in both, summed search 1641 s vs 1651 s,
`.pbp` bytes median ratio 1.000: **retention is not where the time is, and D-0051's
`keep_all` default stands on corpus evidence now, not only on the hand-written suite.**
(d) PB analysis off: per-instance nodes/s ratio **1.04** (n=134, min 0.89, max 36.5); 72 solved
(3 gained: `2008_trucking`, `2008_shortest_path`, `2013_radiation`; 4 lost: `2014_solbat_sb`,
`2016_java-auto-gen_plusexample_6`, `2016_nfc`, `2022_nfc`); killed 78 → 48. So with fix #1 in,
**D-0062's order of magnitude is gone on the corpus**: PB analysis now costs ~4 % per node at
the median, buys a different 4 instances than it loses, and the long tail (max 36.5×, and 30
fewer kills) is where it still hurts. (The higher distribution median, 15.5, is a different
SET of stopped runs; the per-instance ratio is the comparison.)

### Where the time goes: six 60 s profiles (NEW binary unless marked)

`perf record -F 499 --call-graph dwarf`, self time (the dwarf call chains did not unwind
through OCaml frames, so attribution is by symbol); full tables in `bench/m6t9/profiles/`.

| instance | shape | nodes in 60 s | top self-time symbols (module) |
|---|---|---|---|
| 2011 costas-array 15 | narrow, alldiff | 404 (OLD: 167) | **61 % `Justify.go`** (the memo scan), 6 % `Alldiff.go`, 4 % `Store.trail_entry` |
| 2011 costas-array 15, OLD | — | 167 | 23 % `Justify.go`, **17 % `Pb_analysis.down`** + 14 % `Store.trail_entry` + 17 % `caml_apply2` (the O(trail²) scan) |
| 2016 prize-collecting | fewest nodes/s | 12 | **21 % `Analysis.go`** + 16 % `caml_string_equal` + 10 % `Store.name` + 12 % `Store.trail_entry` (`Analysis.scan_support`: a trail scan comparing NAMES) |
| 2008 trucking | optimisation, PB-heavy | 559 | 15 % `Lit.var_compare` + 12 % `List.part` (sort) + 10 % `Lit.var_equal` + 7 % `Learned.fun` (learned-row combination); 4 % `Pb` |
| 2017 tc-graph-color | most learned (2609 in 60 s) | 9054 | **~45 % `Pb.*`** (the learned-PB-row propagator: `Pb.fun`, `Pb.status`, `List.fold_left`) |
| 2018 rotating-workforce | wide, 6 GB | 2 | compile 28.5 s; then 11 % `Store.go` (`Store.var_named`, a LINEAR name lookup) + `Bytes.map`/`Lit.fun` (name sanitisation) |
| 2009 black-hole | wide | 1 (compile 73 s) | `Bytes.map` 15 % + `Lit.fun` 10 % + hashing 12 % + **GC ~28 %** — all in COMPILE |

GC (`OCAMLRUNPARAM=v=0x400` on the same runs): costas 4776 minor / 31 major collections in
60 s, no GC symbol at ≥ 1 %; tc-graph-color 2.7 %; trucking 3.6 % (20.5 G minor words);
rotating-workforce 9 %; only the compile-bound black-hole is GC-heavy. `OCAMLRUNPARAM=s=1M` on
costas' 30-node prefix was SLOWER (6.82 s vs 5.47 s user) and `s>=4M` cannot start under
`ulimit -v 4000000` (OCaml 5 reserves minor heaps for every potential domain). **GC tuning is
not a lever on search**; it may be one on compile, not measured.

What is NOT where the time goes: emission (≤ 0.6 % of search, `emit` row), the engine's
enqueue-everything at each node (costas 30-node prefix: all propagation 0.7 s of 5.5 s),
retention (config c), and — by the profiles — M2-T6's self-wake (the engine is not hot).

### The fix candidates, ranked by the numbers

| # | candidate | file (owner) | evidence | status |
|---|---|---|---|---|
| 1 | `Pb_analysis.falsified_at` asked `falsified_before` at every trail position, each a trail scan: O(trail²) per literal per term per step | `pb_analysis.ml` (mine) | costas: PB analysis 5.8 s of 15 s → 0.06 s; 31-node prefix 10.98 s → 6.10 s, **proof byte-identical** (5.6 MB, VERIFIED); suite 107/107 `.opb`/`.pbp`/`.out` byte-identical; corpus: fin 57 → **73**, median nodes/s **1.44 → 10.8**, killed 137 → 78, summed search on the 57 solved-in-both **2217 s → 590 s**, 0 lost | **SHIPPED** `51d926e` |
| 2 | `Justify`'s memo is an association list scanned with `==` on every emit; its header says the list is "small" — on costas it averaged 13 000 entries: 1.05 × 10⁹ steps, 7.0 s of 15 s | `justify.ml` (orchestrator) | patch `bench/m6t9/justify-memo.patch` (identity buckets under a shallow hash that never enters a `Deferred`): costas 60-node prefix **15.32 s → 3.72 s**, proof byte-identical; suite 107/107 byte-identical; corpus: NOT MEASURED (config e was cut off) | **PROPOSED**, cross-session request |
| 3 | `Analysis.scan_support` compares `Store.name` STRINGS along the trail | `analysis.ml` (unclaimed) | prize-collecting ~60 % self in `Analysis.go`/`string_equal`/`Store.name`/`trail_entry` | request: compare `Var.t` |
| 4 | the learned-PB-row propagator and learned-row combination | `prop/pb.ml`, `learned.ml` | tc-graph-color ~45 % `Pb.*`; trucking ~50 % sort/compare in `Learned` | request; needs its own design (watched slack) |
| 5 | `Store.var_named` is linear; its header says "only ever called from the debug-gated agreement check" — it is on the PB-analysis and `Analysis` hot path | `store.ml` (agent-gcc2 this wave) | rotating-workforce 11 % | request: an index |
| 6 | compile on wide models: name sanitisation (`Bytes.map`) and hashing per literal | `lit.ml`/`encoding.ml` | black-hole compile 73 s, rotating-workforce 28.5 s, 2012 amaze2 > 280 s | request |
| — | `Trace.derive_ahead` writes a `pol` for EVERY pruning of a direct-encoded variable | `trace.ml` (agent-gcc2, M7-T17) | costas: 5910 of 6042 derive-aheads were `Combine` emits; their cost is #2's scan, not their own | M7-T17 is already this |
| — | GC parameters | `bin/main.ml` | see above: slower or unstartable | rejected by measurement |
| — | retention policy | `retention.ml` | config (c): ratio 1.00 | D-0051 stands, not amended |

**Proposed, not shipped (SPEC §3.4 territory):** none of the above changes the search order
or which solution is found first — #1 and #2 are byte-identical by measurement. The ones that
would (incremental waking in place of enqueue-all, restarts per D-0045) are not supported by
these profiles as the next lever, so no SPEC proposal is made here.

### Findings that are not about speed

1. **26 `PROOF-REJECTED` in config (a'), 23 of one shape**: `rup +1 ~<v>_eq_<k> >= 1 ;` — a
   direct-encoding hole with an EMPTY tail, at a decision level > 0, the FIRST such line in its
   proof (on 2015_spot5 there are 2497 rups before it and no bare `_eq_` unit among them),
   preceded by `Trace.derive_ahead`'s `pol`s. That is D-0075's defect shape ("a bare `x <> m`,
   asserted unconditionally") on element indices (`spot5`, `traveling-tppv`, `mario`, `portal`,
   `stable-goods`, `peaceable-queens`) and `mapget*` (`javarouting`/`java-routing` ×10). The
   other 3 are multi-literal `rup`s in models with `baguette_global_cardinality`
   (`generalized-peacable-queens`, `chessboard`, `compression`). Every one was invisible
   before: the instance timed out, so its proof was never checked. Neither fix here caused them:
   the OLD binary (config a) rejects 10 of these same proofs at the SAME line numbers, and
   the rest are instances OLD never reached the line on. With PB analysis OFF (config d) the
   same 26 are rejected plus `2025_stripboard` (`.pbp` 1 554 045 299 bytes, "not implied by
   reverse unit propagation"; under OLD it failed at L846552 on
   `rup +1 ~X_INTRODUCED_340__eq_2 >= 1 ;`, the same shape) -- so PB analysis is not the
   cause either. Artefacts kept on the node: `/scratch/arthur/perf-out-{a,a2,d}/log/<id>.{fzn,
   opb,pbp,vp}`.
2. **An overflow escaped the D-0029 cap** on `2014_rectangle-packing` and `2016_maximum-dag`
   (exit 4, config a'): `Pb_analysis.slack_at` summing a combined row, outside the
   Overflow-to-fallback wrapping the combination already had. Fixed (`aa32015`): the same
   instance now ends `UNKNOWN-LIMIT` at 3923 nodes, VERIFIED NO CONCLUSION. No small unit lane
   was found (1900 fuzzed 0..1 models under the cap did not reach it); the corpus instance is
   the reproducer.
3. **Killed runs are slow NODES, not slow searches**: of NEW's 78 `TIMEOUT-SOLVE`, 59 report
   `killed-in=search` with as few as 1–30 nodes, i.e. single nodes taking more than the 20 s
   between the limit and the kill. The other 19 printed nothing, and the handler is installed
   after compile and the `.opb` write, so those were killed in parse/compile/`.opb`.

### Not measured — needs the node (access was cut 2026-10-01 before these could run)

* **Config (e)**, the proposed `Justify` memo over the corpus: the run was in flight (about
  31 of 331 rows, no `DONE-` marker) and its `results.tsv` was not copied. Re-run with
  `bench/m6t9/sweep3.sh` (binary MEMO above). Until then #2's evidence is the costas prefix
  and the suite, not the corpus.
* The failing line of `2025_stripboard` under config (d): its `.vp` was not copied.
* GC parameters on the COMPILE phase (black-hole, rotating-workforce), and M2-T6's self-wake
  guard measured directly: neither was run; the profiles above only say they are not where the
  SEARCH time is.

### Gate on the final tip

`dune runtest --root . --force` **2953 ok / 0 FAIL**, peak RSS 40.9 MB; `run_model_tests.sh`
**107 passed / 0 failed** on binary `cad68e390e727a1b7906aabc8704eab6` (tip `249d37d`), peak RSS
18.5 MB; `corpus_selftest.sh` PASS; `@fmt` clean. Every sweep config, profile script and
summariser is in `bench/m6t9/` (`sweep*.sh`, `prof.sh`, `repro.sh`, `summarise.py`,
`compare.py`), the per-config `results.tsv` in `bench/m6t9/results/`, the profile tables and
GC lines in `bench/m6t9/profiles/`.
## D-0081  The comparison harness, and baguette's first external oracle: no disagreement on 164 instances

**Status**: **MEASUREMENT + TOOL**, recorded 2026-10-01 by agent-compare (M6-T4, absorbing
M5-T3), wave 31, branch `wave31-compare`. Runs on `fataepyc-07` under
`/scratch/arthur/compare-out-{pilot,chuffed,gcs-noproof}`; every one has its `DONE-` marker
and a `run.conf` hashing every binary. Harness: `scripts/compare_run.sh`,
`scripts/compare_selftest.sh`, `tools/compare/compare.py`; how to read it: `bench/README.md` §8.

### Setup facts

| | |
|---|---|
| MiniZinc | 2.10.1 bundle, `/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/`, `minizinc` md5 `4dcf37f1e8305d0814d6347b9db1d151` |
| **baguette** | `main` at `e59f214` (the wave-31 claim commit; `wave31-compare` adds no `lib/`/`bin/`/`mznlib/` change), built in `/scratch/arthur/baguette-compare`, `main.exe` md5 **`b9394d8d9e576f0eb1c2673bcfda9e47`**; flattened with `tools/baguette.msc` → `mznlib/` (D-0067); `--max-heap-mb 15625 --proof` |
| **Chuffed** | **0.14.0** (the bundle's `chuffed.msc`; `fzn-chuffed` has no `--version`), `fzn-chuffed` md5 `d30798695fa151c08caf956a774589d2`; flattened with its own `share/minizinc/chuffed`; **no `-f`** (free search OFF, annotation honoured), restarts at Chuffed's default, `-a` on optimisation only. Logs no proof |
| **GCS** | `github.com/ciaranm/glasgow-constraint-solver` at **`5882c2943480db38fd66760858e3b6196ad7b7cc`** (2026-10-01), `/scratch/arthur/gcs`. `cmake --preset release` (Release, `-march=native`, g++ 15.2) and `cmake --build --preset release --target fzn-glasgow`: built first time, **no Boost** (CMake fetches Catch2, cxxopts, nlohmann/json, gch::small_vector; libxml2 was present). `fzn-glasgow` md5 `ebffdc089f351bbedbd02c12bca6e00d` |
| GCS entry point | `minizinc/fzn_glasgow.cc` → `build/fzn-glasgow`; the build writes `build/glasgow.msc` (id `com.github.ciaranm.glasgow-constraint-solver`, mznlib `minizinc/mznlib`, **`inputType: JSON`** — MiniZinc hands it JSON FlatZinc). `MZN_SOLVER_PATH=build/` makes `minizinc --solver` find it |
| GCS flags | `-i` on optimisation only; no `-f`; `--restarts` left at 0 (off); **proof logging `--prove --proof-files-basename <b>`** → `<b>.opb`, `<b>.pbp` (+ `.scp`, `.varmap`) |
| **Proof formats, and who checks whom** | baguette: `pseudo-Boolean proof version 3.0`. **GCS: `pseudo-Boolean proof version 3.0`** (first line of its `.pbp`). Both are checked by **`~/.cargo/bin/veripb`, VeriPB 3.0.2 (Rust)**. No Python VeriPB was needed and none was installed; `~/.local/bin/veripb` stays broken and unused. Verdict by wording: `s VERIFIED …` accepted; `Verification error at …` + a non-grammar `Caused by` rejected |

### The harness, in one paragraph

Per instance, the data file is chosen **once**, independent of which solvers run: the
smallest candidate (corpus_run.sh's order, bare last) that at least one of the three
libraries flattens. Then each solver flattens with its own library, atomically, the
flattened file passes `validate_fzn`/JSON parse before any solver-blaming bucket is
reachable (D-0069), the objective is made an output variable identically for all three,
and each run gets `timeout`, `ulimit -v 32000000` and a `ulimit -f` proof cap (16 GB). The
agreement verdict per instance — `AGREE`, `DISAGREE` (solution vs UNSAT, two different
proved optima, or an incumbent better than a proved optimum), `INCOMPLETE` — is computed
from the table, and `--report` prints `DISAGREE` first. The self-test reaches SAT, UNSAT,
OPT, REFUSED, NO-PROOF, NO-DATA and two `DISAGREE`s against a deliberately wrong GCS shim,
and fails rather than skips without baguette or veripb.

### The pilot: 88 instances × 3 solvers, 300 s

The 58 `OK-PROOF-VERIFIED`, 10 `REFUSED-MODEL` and first 20 `TIMEOUT-SOLVE` of D-0079.
`PAR=10` per solver. **All 88 paired the SAME data file as `corpus-out-w30`** (checked
id by id), and all three libraries flattened all 88.

| status | baguette | chuffed | gcs (proof on) |
|---|---|---|---|
| OPT | 42 | 58 | 34 |
| SAT | 13 | 19 | 18 |
| UNSAT | 4 | 5 | 4 |
| TIMEOUT | 19 | 6 | 1 |
| CAPPED (16 GB proof cap) | 0 | 0 | **28** |
| REFUSED | 10 | 0 | 0 |
| ERROR | 0 | 0 | 3 |
| proofs VERIFIED | **59 / 59** | — | 44 |
| proofs REJECTED | **0** | — | **2** |
| TIMEOUT-CHECK (900 s) | 0 | — | 10 |

**Agreement: 77 AGREE, 0 DISAGREE, 11 INCOMPLETE.** On the 38 instances all three solved:
median wall **baguette 4.97 s, Chuffed 0.12 s, GCS 0.17 s** (means 37.3 / 0.17 / 17.2); median
proof 2.9 MB (baguette) vs 6.0 MB (GCS), median check 0.57 s vs 1.22 s. PAR2 over all 88:
baguette 229.5, Chuffed 41.9, GCS 235.9. baguette solved 59 = D-0079's 58 plus
`2010_bacp_bacp-10` (a `TIMEOUT-SOLVE` in wave 30, OPT here in 287.9 s -- inside the 300 s by 12 s, so a timing margin, not a change), and none that
Chuffed did not. Its 10 REFUSED are D-0079's 10 `indomain` refusals.

### The single-solver passes: all 436, 300 s

| status | Chuffed (`PAR=16`) | GCS, proof OFF (`PAR=16`) |
|---|---|---|
| OPT | 219 | 111 |
| SAT | 44 | 31 |
| UNSAT | 10 | 7 |
| TIMEOUT | 139 | 259 |
| ERROR | 0 | 3 |
| FLATTEN-FAIL | 4 | 5 |
| NO-DATA | 20 | 20 |
| **solved** | **273** | **149** |

Chuffed's median over its 273 is 1.41 s, PAR2 238.1; GCS's over its 149 is 13.4 s, PAR2
411.3. The GCS pass ran **without** proof logging, because the pilot showed GCS's proofs
dominating its time: 28 of 88 pilot runs hit the 16 GB cap after a median 157 s, and with
proofs off the same 88 give 41 OPT instead of 34. So the GCS pass measures the solver, and
the pilot measures its proofs.

### What it found

1. **The oracle found nothing against baguette.** Over the pilot plus both passes, **164
   instances AGREE and 0 DISAGREE**; baguette is party to 61 of the agreeing pins
   (45 with both others, 16 with Chuffed alone). That is the measurement: on every
   instance where baguette proved something, two independent solvers that share none of
   its code reached the same answer, and veripb accepted all 59 of its proofs.
2. **GCS's proofs were rejected twice by veripb 3.0.2, with the answers agreeing.**
   `2014_stochastic-fjsp_fjsp-a1-s4_fjsp-t8-j2-m3-a1_det` (OPT 242 by all three):
   *"not implied by reverse unit propagation"* at `.pbp:17336`, 13.9 GB proof.
   `2019_stochastic-vrp_vrp-s4-v2-c3_svrp-v2-c3_det` (OPT 117 by all three): *"The
   propagated assignment does not satisfy the constraint with ID 9457"* at
   `.pbp:262034`, 38 MB — **reproduced by hand on a fresh flatten with neither the
   COMPAT file nor the objective injection** (both instances already output their
   objective), so it is not the harness's doing. Both artefacts are kept under
   `compare-out-pilot/log/`. They are findings about GCS `5882c294` (or about the one
   checker, which D-0046 made the sole oracle), not about baguette.
3. **GCS errors**: `Integer overflow` on `2010_wwtp_random_wwtpp`, `2010_wwtp_real_wwtpp`,
   `2025_work-task-variation`; it also substitutes `dom_w_deg` for the `largest` variable
   heuristic it does not know (a warning), so "annotation-driven" is approximate for GCS
   there.
4. **The shared set is 411 of 436** (`bench/corpus/shared_set.lst`): 20 NO-DATA (all
   `2026/`, as D-0074 found), 4 that no library flattens (`2009_p1f` ambiguous `circuit`,
   `2016_cryptanalysis_step1_aes` index-set mismatch, `2021_yumi-dynamic` max of empty set,
   `2024_train-scheduling_trains`), and `2025_gt-sort`, whose flatten crosses the 120 s
   timeout for baguette's and (in one run) GCS's library.
5. **`bench/corpus/answers.tsv` pins 387 instances** — 223 OPT, 10 UNSAT, 44 SAT
   (satisfaction), 110 SAT with a best-known objective — 0 DISPUTED; 127 rest on Chuffed
   alone and 4 on GCS alone. It is M5-T3's regression set: a later run that contradicts a
   row is reported `PIN-MISMATCH` by `--report --pinned`.

### Three corrections the first runs forced, each now in the script

* **MiniZinc 1.x models** (2008-2010: `:: is_output`, string-valued `int_search`) are
  refused by the 2.10.1 standard library and shimmed by baguette's `mznlib/compat_mzn1.mzn`.
  The first pilot attempt had 22/88 `FLATTEN-FAIL` for Chuffed and GCS on that alone; it
  was stopped and re-run with `COMPAT=1`, which passes the same language-only file to their
  flattens. It decomposes nothing; their globals are still theirs. **A deviation from "each
  solver flattens with only its own library", stated rather than hidden**; `COMPAT=0`
  restores the strict form.
* **`minizinc -c -o X.part` writes `<model>.ozn` into the corpus directory** — 412 stray
  `.ozn` files under `/scratch/arthur/mzn-challenge/` today, from this harness and from
  `scripts/corpus_run.sh`, which has the same `-o .part` pattern (cross-session request
  filed). `--no-output-ozn` stops it. The files are inert (no data glob matches them) and
  were left in place for the orchestrator to remove.
* **Pairing is deterministic only up to `FLATTEN_TIMEOUT`**: `2025_gt-sort` paired two
  different data files in the Chuffed and GCS passes. `--answers` caught it (DISPUTED), the
  GCS row was re-run with `PAIRS` pinned to the Chuffed pass's choice, and `PAIRS` is now
  how any later run is made comparable with `answers.tsv`. Also fixed on the way: NO-DATA
  is detected in MiniZinc's whole message, not its first 200 bytes (two 2026 instances).

### What is not done

GCS's proof-logging comparison covers the pilot only; a full-corpus GCS pass with proofs
would spend most of its time writing and checking multi-GB proofs (10 of the 56 pilot
proofs that were checked did not finish in 900 s; one 15 GB proof did). The pilot did not include
baguette on the other 348 instances — D-0079 is that run, and `PAIRS=bench/corpus/answers.tsv`
makes the next one directly comparable.
## D-0082  Derive-ahead is a property of the PROPAGATOR (M7-T17), and a constant gcc count is a VIEW (M7-T18)

**Status**: **DECIDED and MEASURED**, 2026-10-01, agent-gcc2, branch `wave31-gcc2`.
Closes the cross-session request M7-T16 filed against `lib/core/trace.ml` (D-0078's
defect (1)) and the nine `fzn_global_cardinality` refusals of D-0079.

### M7-T17 — the trigger

**Before.** `Trace.derive_ahead` wrote a pruning's derivation (`Justify.emit` of its
forced explanation) ahead of its trace line iff `Encoding.has_direct` held for the pruned
variable. That was a proxy for "this variable is in a counting global's scope", wrong both
ways: it over-triggered (any `int_lin_le` pruning of an all_different variable, and every
element INDEX pruning, got a `pol` nobody needed) and it under-triggered (gcc names no
direct literal, so M7-T16 had to `request_direct` the gcc scope purely to arm it, minting
the width-proportional `red` lines of an encoding nothing read).

**After.** `Store.entry` carries `ahead : bool`, stamped by `Store.apply` from a slot that
only `Store.deriving_ahead` sets, around a call. The PROPAGATOR makes the pruning call
under it: `Alldiff` for its Hall bound moves and its Regin holes, `Gcc` for rule A's
capacity pushes (rule C's count bounds are RUP against one row and never had a derivation
ahead; they still do not). `Trace.derive_ahead` reads `e.ahead` and nothing else; the
decision-skip and the level/ownership rules (the `pol` is minted at the entry's level and
retired by the same `w`, I-X2) are unchanged. The engine is not involved. The trace.ml
header's lead -- answer it from the entry's `prop` with no new field -- does not work:
`prop` is an instance id, and nothing `Trace` can see maps an id to its family; one
immediate field per entry is cheaper than threading the instance table through `Search`.

The `request_direct` stopgap in `compile.ml`'s gcc region is DELETED. The two that remain
are for the derivation, as their comments say: `all_different`'s (its Hall `pol` cites
`x_eq_v` lines) and the element INDEX's (its derivations cite `direct_lo_id` /
`direct_hi_id` / `at_least_one_id`).

**The four measurements.**

1. **Byte identity.** Model suite, before (`e59f214`) and after, every `.opb` and `.pbp`
   hashed: **205 of 214 identical**. All 107 `.opb` are identical. The 9 that differ are
   all `.pbp` of models with a global, and all shrink: `alldiff_hall_moved_unsat` 3612 ->
   3405, `alldiff_hall_trace_unsat` 4291 -> 4244, `alldiff_search_unsat` 21751 -> 19524,
   `element_index_hole_rup_sat` 3316 -> 3264, `element_moved_unsat` 981 -> 932,
   `gcc_capacity_sat` 2311 -> 191, `gcc_capacity_unsat` 1426 -> 170,
   `gcc_hall_narrowed_unsat` 4608 -> 610, `gcc_search_sat` 2514 -> 1169. Of the 80 models
   with no global, **every** proof is byte-identical, which is the promise the trace.ml
   comment made.
2. **Lanes.** Every alldiff / element / gcc model verifies (109/109 with M7-T18's two new
   ones), and so do the three `test_ix10_derive_ahead` scenes. Element now has NO
   derivation ahead of any line, index side included, and verifies -- `Single_row`, as
   the I-X10 table classified it, measured on both sides for the first time
   (`element_index_hole_rup_sat` is SAT).
3. **`2008_debruijn_binary` on `fataepyc-07`** (flatten with the clone's `tools/`, solve,
   veripb 3.0.2): before `e59f214` (binary `b9394d8d9e576f0eb1c2673bcfda9e47`) `.pbp`
   **28 552 B**, 208 `red`; after `26dc38f` (binary `74e11dbf72bb54079727259c5dba378c`)
   **24 542 B**, 176 `red`, `.opb` 63 145 B both sides, both `s VERIFIED SATISFIABLE`.
   That is **below the pre-gcc decomposition's 25 202 B** (D-0078) -- the native
   propagator's proof is now smaller than the decomposition's, not 13% larger.
4. **The break lanes still redden, and the trigger is load-bearing.** Performed: (a)
   rule A's pushes made WITHOUT `deriving_ahead` -> test_trace's gcc scene reddens on
   exactly two checks ("a pol precedes the Hall trace line", "the full proof verifies");
   its standalone BREAK ("the same line standalone is REFUSED, and on the checker's own
   judgement") stays green, as it must. Not one model test of M7-T16's four noticed; the
   new `gcc_const_counts_sat` does ("not implied by reverse unit propagation"). (b)
   alldiff's two wrappers removed -> both alldiff scenes redden on "the full proof
   verifies", and `alldiff_hall_trace_unsat` is rejected by veripb.

### M7-T18 — constant counts

A constant count is the count VIEW `View.const k` (D-0058); `Gcc.cover.cx` is a `View.t`.
The argument that the artefacts are exactly as valid is one observation: the propagator and
the rows read a count only through `cdlo`, `cdhi`, its current bounds and its ladder, and a
constant is `var k..k` with all four identical -- `cdlo = cdhi = k`, an EMPTY ladder. So
the `.opb` row is `sum (x indicators) = k - ones - const_v`, the constant on the DEGREE
side, which is the row a one-value count variable already got; every derivation's ladder
range is empty; rule C's attempted narrowing goes through `View.set_lo`/`set_hi`, whose
`Const` arm returns `Store.unattributed_conflict` -- the value `Store.apply`'s `Failed` arm
gives the one-value variable. `scope_facts` names no fact for a constant, which has no
name. **Measured**: `gcc_const_counts_sat` / `_unsat` against their `var k..k` twins give
`.opb` and `.pbp` byte-identical apart from comment lines; `test_compile.ml` pins the
`.opb` half, the instance count, and that no gcc-scope variable has a direct encoding.

Lanes: `gcc_const_counts_sat` (SAT; the M7-T16 I-X10 scene with constants, so the
across-values capacity push lands under a decision, its `pol` ahead of it) and
`gcc_const_counts_unsat` (UNSAT under search, every branch closed by the constant
capacities).

**The nine corpus instances**, on `fataepyc-07`, binary `74e11dbf72bb54079727259c5dba378c`,
300 s solve, `ulimit -v 32000000`, 5 at a time: **9 TIMEOUT, 0 refused, 0 rejected**
(`2014/2016/2018/2023_elitserien_handball`, `2016/2018_oocsp_racks`,
`2019/2020_lot-sizing_lot_sizing_cp`, `2025_mondoku_mondoku-gcc-model-balance`). All nine
flatten (283 KB to 5.7 MB of `.fzn`) and compile; none solves in 300 s, so none has a proof
to check. That is D-0079's TIME blocker, now reached by nine more instances.

`global_cardinality_closed` reaches the propagator through std's own definition.
`global_cardinality_low_up` does NOT (std decomposes it into `count` sums); the `mznlib`
line that would route it is filed as a cross-session request. None of the nine needs it.
## D-0083  The ten corpus refusals: `indomain` is `indomain_min`, `anti_first_fail` is first_fail reversed, and an undomained `var int` gets the domain its constraints imply

**Status**: DECIDED, 2026-10-01, agent-cover (wave 31, M7-T19).
**Touches**: `lib/flatzinc/{builder,model,compile}.ml`, `lib/core/search.ml` (the
variable-selection functions), `docs/SPEC.md` §2.1 and §3.4,
`test/unit/{test_flatzinc,test_compile}.ml`, five new models.
**Follows** D-0079 (the wave-30 corpus run, whose ten `REFUSED-MODEL` were exactly these
three messages), D-0077 (the precedent for lifting a §3.4 refusal: build the real thing,
never a near-equivalent), D-0029 (the arithmetic limit), D-0028/D-0065 (the order encoding
is width-proportional; the width limits are options).

### 1. Bare `indomain` — mapped to `indomain_min`

The MiniZinc specification defines `indomain` as "assign values in ascending order". That
is `indomain_min`'s branching at every node — `x = lo` first, the rest as the sibling, the
next decision on that variable taking the new minimum — so it is the **same search**, not a
substitute for one, and §3.4's ban on substitution does not bite. The builder maps the
spelling onto `Model.Indomain_min`; no constructor was added, because a second constructor
for the same decision is a place for the two to drift.

### 2. `anti_first_fail` — a new selector, `first_fail` with the comparison reversed

The unfixed variable with the **largest** current domain (`Domain.size`, the live value
count — first_fail's measure). **Ties go to the earliest candidate**, which is
`first_fail`'s rule unchanged (both comparisons are strict). The alternative reading,
"first_fail's ordering reversed", would also reverse the tie-break and pick the LAST of
several equally large domains; nothing in the MiniZinc specification asks for that, and
Gecode's `INT_VAR_SIZE_MAX` takes the first. `test_flatzinc.ml` pins the tie-break on a
hand-built store and through an annotation whose array order differs from declaration
order; `search_anti_first_fail_sat.fzn` is a model on which every other supported
selection gives a different first answer (measured).

### 3. `var int` with no domain — inferred, and refused only when inference fails

**Why inference and not a default range.** A default range is width-proportional cost paid
BLIND (D-0028): `-10^6..10^6` is two million ladder rungs per variable whatever the model
needs, and every corpus instance that has one undomained variable has dozens. The bound the
model's own constraints imply is the width the model licenses and no more.

**Why refusing stays.** A variable no constraint bounds has no width to encode; any range
would be a guess, and a guess that is too narrow is a different model answered with a
verified proof. So §2.1 still refuses — now with a message that names the variable, says
inference was tried, gives the bound it reached on each side, and lists the variable's
neighbours with what inference knew about each.

**Soundness obligation.** Every rule derives a bound that every solution of the one
constraint it reads satisfies, so the inferred domain contains every value the variable
takes in any solution, and the encoded model has exactly the FlatZinc model's solutions.
This is a front-end obligation, like the rest of the encoding: veripb checks the proof
against the `.opb`, into which the inferred domain is written as a declaration, and cannot
see the inference. Every step is `Baguette_core.Checked`; an overflowing step derives
nothing for that constraint on that pass. A declared domain is read and never tightened.

**The rules shipped** (constant operands folded into the rhs, repeated variables merged):

- `int_lin_eq`: for each term, solve the row given the other terms' bounds — both sides.
- `int_lin_le`: the same, one side (`a*x <= rhs - least(rest)`), floor/ceil rounding outward.
- `int_eq(a, b)` / `int_le(a, b)` / `int_lt(a, b)`: as the rows `a-b = 0`, `a-b <= 0`, `a-b <= -1`.
- `bool2int(b, x)`: `x in 0..1`.
- `int_abs(x, z)`: `z >= 0`; `z <= max|x|`; `x in -hi(z)..hi(z)`.
- `int_times(x, y, z)`: `z` in the four-corner product (`Interval.product_bounds`).
- `int_div(x, y, q)`: `|q| <= max|x|` (wherever the relation holds `|y| >= 1`).
- `array_int_element(i, a, c)`: `i in 1..|a|`, `c in min(a)..max(a)`.
- `global_cardinality` (both spellings): each count in `0..|xs|`.
- **Case split** on a Boolean `c`: `if c then x = e1 else x = e2`, which MiniZinc writes as
  `int_eq_reif(x, e1, p1)`, `int_eq_reif(x, e2, p2)`, `bool_clause([p1],[c])`,
  `bool_clause([c,p2],[])`. Each side's implied equalities are intersected; `x` is in the
  hull of the two sides, only when both are two-sided, and a side whose bounds cross is
  impossible and drops out. Added after the first node run: it is the whole of
  `2025_work-task-variation`'s 469 undomained variables (`run_cost`), and no listed rule
  reaches them.
- Nothing else is read: other reified forms, `int_ne`, `all_different`, and clauses other
  than the two-literal implications above imply no bound.

At most 64 passes over the facts, stopping at the first pass that changes nothing; every
intermediate state is sound, so the cap costs precision and never soundness. If inference
CROSSES a variable's bounds (`lo > hi`) the model has no solution, any domain is sound, and
the variable is declared on the hull `hi..lo` (`unbounded_crossed_unsat.fzn`). The hull and
not a singleton because a root-UNSAT linear row over a singleton-declared variable crashes
`Justify.emit` today — a pre-existing defect, reproducible with a declared `var 7..7`, filed
as a cross-session request rather than fixed here.

An alias `var int: x = y;` declares nothing and is no longer refused. An inferred domain
is a declared domain for every other purpose, so a wide one meets the width limits of §3.1
honestly; D-0065 says those are options, and a wide inferred domain is the order
encoding's real cost, not inference's fault.

**Where it runs.** In `Builder.build`, after the declarations and BEFORE the constraints are
built, because the arithmetic family sizes its auxiliaries from domains; the refusal fires
AFTER the constraints are built, so a malformed constraint still reports its own error
first. It reads the syntax directly (`facts_of`), and only runs when some variable is
undomained, so a model without one is untouched — byte-identical artefacts.

`builder.ml` now references `Baguette_core` (`Checked`, `Interval`), which the dependency
order permits (`flatzinc -> core`) but `lib/flatzinc/dune`'s comment says it does not do;
that comment is the orchestrator's and is a cross-session request.

### The ten instances, measured 2026-10-01 on `fataepyc-07`

Branch tip `c6112f1` (binary md5 `10e0f406d5afc52ad5ab4a2f498c62a6` on the node), flattened
with MiniZinc 2.10.1 and baguette's library, 300 s solve timeout, `--max-heap-mb 15625`,
`ulimit -v 32000000`, veripb 3.0.2 on every solved run. Output under
`/scratch/arthur/cover-out-w31`.

| Instance | Before (w30) | After | Proof |
|---|---|---|---|
| `2008_quasigroup7` | REFUSED `indomain` | SAT in 0.12 s | VERIFIED |
| `2010_ghoulomb` | REFUSED `indomain` | TIMEOUT 300 s | — |
| `2013_ghoulomb` | REFUSED `indomain` | TIMEOUT 300 s | — |
| `2010_depot_placement` | REFUSED `indomain` | TIMEOUT 300 s | — |
| `2013_on-call-rostering_oc-roster` | REFUSED `anti_first_fail` | TIMEOUT 300 s | — |
| `2018_on-call-rostering_oc-roster` | REFUSED `anti_first_fail` | TIMEOUT 300 s (width warning, 28 800) | — |
| `2010_wwtp_real_wwtpp` | REFUSED no domain | TIMEOUT 300 s; all inferred (widest warned 10 440–22 500) | — |
| `2010_wwtp_random_wwtpp` | REFUSED no domain | TIMEOUT 300 s; all inferred (68 width warnings, widest 20 959) | — |
| `2025_work-task-variation` | REFUSED no domain | all 469 inferred (case split; `cost` 0..660040, warned); then REFUSED-LIMIT on `fzn_global_cardinality` with a constant count — **M7-T18's** refusal, not this one | — |
| `2021_connect_connect__0086_02` | REFUSED no domain | still REFUSED, new wording: `fplen` has lower bound 54938 and NO upper bound | — |

`connect` is a correct refusal, not a missing rule: `fplen`, `fpwid` and `FPCOST` are bounded
below and minimised, and no constraint bounds them above — the model's own solution set is
unbounded in them. Bounding from the objective would need an incumbent first, and is a
different decision. Zero proofs rejected.

## D-0084  The 26 corpus rejections: a derivation one propagator EMBEDS in another, in two families
Status: DECIDED (element and gcc fixed and measured locally; the 26 node instances UNVERIFIED until the node returns)
Date: 2026-10-02
Task: M7-T21 (agent-rup2, wave 32).
Touches: `lib/core/prop/element.ml`, `lib/core/prop/gcc.ml`, `test/unit/test_trace.ml`,
`docs/PROOF-FORMAT.md` §4 (element, gcc rows), seven new models.
Follows D-0075 (element's hole facts), D-0040/D-0082 (derive-ahead, the propagator's flag),
D-0064 (root-established bounds cited by `Defining`), D-0066/D-0073 (a rup is checked by
being load-bearing, and a SAT model is where a wrong one is visible).

### Shape 1 -- the 23 bare units: a foreign index hole, under a decision

**The defect.** `element.ml`'s [pos_gone] excludes each dead position by one derivation. For
a position the index lost to ANOTHER propagator (an `int_ne`, another element sharing the
index), the arm was `Explanation.clause [~idx_eq_p]` -- a bare unit, emitted as
`rup +1 ~<idx>_eq_<p> >= 1 ;`. That unit is RUP only when the hole is a consequence of the
model: the hole's own trace line is `~idx_ge_p \/ idx_ge_(p+1) \/ ~<the puncher's facts>`,
and with only `idx_eq_p` assumed those facts are not falsified, so unit propagation never
fires it. At level 0 the facts are root facts and it holds; under a decision it does not.
The line is written only when the derivation is FORCED, and the path is: a second element
whose result is this one's result hits a factless conflict, `search.ml`'s D-0040 arm emits
the conflict's `pol`, and that `pol` embeds this instance's [hole_expl] through
[excl_hole]. That is exactly D-0080's description -- a bare direct-encoding unit, empty
tail, level > 0, the first such line in its proof, after a run of `pol`s (they are the
conflict's derivation, not `derive_ahead`'s) -- and it is the ONLY site in `lib/` that
writes a bare `~x_eq_k` unit (alldiff's root case cites the unit through `Defining`; its
deep case carries the facts already). The trace lines were never wrong, which is why every
lane D-0075 added stayed green.

**Is it D-0075's shape?** Its sibling, not the same line. D-0075 was a TRACE line whose tail
lacked a hole's facts; this is a DERIVATION summand that lacked them. The repair is the
same idea -- carry the puncher's reason -- and its exact precedent is alldiff's
[Gone_hole] arm: [index_hole_clause] is `~idx_eq_p \/ ~<puncher's facts>`, RUP against the
hole's own trace line plus the channelling halves, and the bare unit only for a level-0
hole, so a proof that never reaches a deep foreign hole is byte-identical.

**Reproducer.** `test/models/element_foreign_hole_rup_sat.fzn` (three variables, SAT;
`int_ne(i,j)` with `j = 3` by `indomain_median`, two elements sharing the result). Pre-fix
it writes `@c70 rup +1 ~i_eq_3 >= 1 ;` at line 54 and 3.0.2 refuses it ("not implied by
reverse unit propagation (RUP) from core and derived database"); post-fix the line is
`rup +1 ~i_eq_3 +1 ~j_ge_3 +1 j_ge_4 >= 1 ;` and the proof verifies. The UNSAT twin
(`element_foreign_hole_rup_unsat.fzn`) reaches the same line, and pre-fix 3.0.2 ACCEPTED the
bare unit there -- D-0066 measured once more. `test_trace.ml`'s M7-T21 element lane pins
the line, rewrites it back to the bare unit in place, and asserts the refusal at that line
number with full wording; with the fix reverted its "no bare unit" and "written with its
puncher's facts" checks redden (measured).

### Shape 2 -- the 3 gcc multi-literal rups: rule C's LOWER push is not single-row

**The defect.** gcc's rule C pushes `lo(n) := #{scope variables fixed to v}`, and
`gcc.ml` wrote its trace line bare, saying it "is RUP against the ONE counting row of its
own value plus the count's ladder". The `<=` row carries every OTHER variable's indicator
negated, `~x_ge_v + x_ge_(v+1) - 1`, and unit propagation treats the two literals
independently: it cannot see the indicator is never negative, because that is the rung
`x_ge_(v+1) -> x_ge_v`, a second constraint. With two or more other variables holding v
strictly inside their window the row keeps slack and never fires, so the line -- e.g.
`rup +1 n_ge_1 +1 ~x_ge_2 +1 x_ge_3 >= 1 ;`, multi-literal, in a gcc model -- is true and
not RUP. With exactly one such variable the slack forces both literals and the rung
conflicts, which is why no M7-T16 scene saw it. The UPPER push is genuinely single-row
(every indicator it clears is pinned by a bound fact the ladder propagates).

**The fix.** The lower push runs under `Store.deriving_ahead`, so `Trace.derive_ahead`
writes [c_lower_expl] -- whose [free_summands] ARE those rungs -- ahead of the line. One
flag, D-0082's mechanism, no new constructor.

**Reproducer.** `test/models/gcc_count_lower_rup_sat.fzn` (gcc over three variables, SAT,
the D-0075 pigeonhole to fail deeper). Pre-fix: refused at line 8, the bare rule C line.
Found by a random sweep (12 of 300 small gcc models, all this shape), not reduced from the
corpus, so which of the three corpus instances it explains is for the node to confirm.
`test_trace.ml` runs it through [test_ix10_derive_ahead] (now able to honour a scene's
search annotation); with `~ahead:false` restored its "a pol precedes" and "the full proof
verifies" checks redden (measured). The UNSAT twin is refused pre-fix too: its database is
not yet contradictory at that line.

### Found on the way: four ROOT-conflict defects, three fixed here

The sweep (about 20 000 small models over element, gcc, int_ne, int_lin_le and
all_different, every proof checked) found refutations whose `conclusion UNSAT` row is "not
contradicting". All are pre-existing (the wave-32 base binary is rejected identically) and
UNSAT-only, so none is among the 26. Each is a derivation EMBEDDED in a root conflict
carrying something the embedder did not count:

1. **Element, shared result** (`element_shared_result_root_unsat.fzn`). [excl_hole] cites a
   result hole by its remover's explanation, another instance's [hole_expl], which kept
   its root-established residue. Fix: every element pruning derivation cancels
   root-established residue where it is built ([alo_of]'s [cancel], and [filter_index]).
2. **Element, crossed index/result** (`element_crossed_root_unsat.fzn`). The embedded
   remover was an INDEX removal, which concluded `~idx_eq_p` where [excl_hole] pairs off
   ORDER literals. Fix: an interior index removal is restated over the order encoding by
   the forward channelling line ([in_order_currency]). **The contract this states: a hole's
   trail-entry explanation concludes the hole in the ORDER currency, the clause the trace
   line claims.** Ne and element now keep it; all_different's Regin removal does not
   (item 4).
3. **gcc, emptying rule C push** (`gcc_count_empty_root_unsat.fzn`). A push that empties the
   count against a bound the root set past the declared one derived the valid `n >= 1`,
   not `0 >= 1`. Fix: [close_lower]/[close_upper] walk the rungs to the opposite bound and
   cite it by `Defining` -- rule A's "one more line" for rule C.
4. **NOT FIXED, cross-session:** (a) `search.ml`'s root arm emits the root trace only when
   the conflict's derivation has a TOP-level `Defining`; a nested one mints
   `rup <lit> >= 1` with nothing on the page to propagate from (four sweep instances;
   always emitting the trace there fixed all four, measured and reverted); (b)
   all_different's Regin removal concludes `~y_eq_v` -- measured: restating it through
   `Encoding.direct_fwd_id` fixed both sweep instances and kept 124/124 models, reverted;
   (c) an `Alldiff: ladder rung has no constraint id` CRASH (exit 2) on three sweep
   models mixing all_different and element, pre-existing. Requests filed in WORKLOG.

### Not verified until the node returns

The 26 of config (a'), by shape, for tomorrow's run to tick off (binary hashed, one per
shape at least):

- **bare `~<v>_eq_<k>` unit, element shape 1 (23):** `2014_spot5`, `2015_spot5`,
  `2022_spot5`; `2014_traveling-tppv_ttppv`, `2017_traveling-tppv_ttppv`,
  `2022_traveling-tppv_ttppv`; `2013_mario`, `2014_mario`; `2024_portal`;
  `2020_stable-goods_stable-goods-solution`; `2021_peacable_queens_peaceable_queens_mznc2021`,
  `2024_peacable_queens_peaceable_queens_mznc2021`; `2012_project-planning_ProjectPlannertest_12_8`;
  `2013_javarouting_trip_{6_3,7_1,7_2,8_1,8_5}`, `2021_java-routing_trip_{6_2,7_4,7_5,8_2,8_3}`.
  Plus `2025_stripboard` of config (d), same shape. The `mapget*` variables are expected to
  be element INDICES (MiniZinc's `mapget` over a constant array flattens to
  `array_int_element`); no `.fzn` of those models exists locally to confirm it.
- **gcc multi-literal rup, shape 2 (3):** `2022_generalized-peacable-queens_peaceable_queens`,
  `2023_chessboard`, `2024_compression`. Expected: rule C lower lines
  (`rup +1 <count>_ge_k +1 ~<x>_ge_v +1 <x>_ge_(v+1) ...`); if the rejected line there is
  NOT of that form, it is a second gcc defect this record does not explain.

What a fix here cannot promise: these instances were rejected at the FIRST bad line, so a
proof that now passes that line may meet a later one of another family (the sweep's item
4 kinds among them).
## D-0085  D-0080's levers #3-#6 shipped as constant-factor changes: every artefact byte-identical, the learned-PB-row work is the one that moves locally

**Status**: **SHIPPED (four levers) + MEASUREMENT (local only) + PROPOSALS**, recorded
2026-10-02 by agent-speed (M6-T11), branch `wave32-speed`. The node `fataepyc-07` was
unreachable for the whole task, so every number below is LOCAL (12-core WSL2 laptop, load
average 1-5 from the other wave-32 sessions, which is why each figure is a minimum of 5 and
why ratios inside +-10 % are read as noise). What to measure on the node is at the end.

### The binaries, and the byte-identity verdict

`bench/m6t11/byte_identity.sh OLD NEW [extra.fzn ...]` runs both with `--proof` over every
`test/models/*.fzn` plus extras and diffs the md5 of every `.opb`, `.pbp` and stdout+exit
code. Run with five generated extras (`bench/m6t11/gen.py`: `ne 7 0`, `ne 7 2000`,
`wide 400 300 400`, `knap 8 2 3 1`, `knap 10 2 3 1`; the knapsacks and the wide model
declare wide domains, so they live under `/tmp` and are never committed, D-0028):

| tag | commit | md5 of `main.exe` | vs BASE |
|---|---|---|---|
| BASE | `f52ed18` (wave-32 claim, = `main`) | `fd432a570606be1d05d25a89f3d12685` | -- (self-run also identical: the script is deterministic) |
| L5 | `f56a1c4` | `82d10ff34d341327e5f9eb3fa611a8dc` | **366 / 366 artefacts identical over 122 models** |
| L3 | `6523695` | `224090958732f13b6015d20683ef69db` | **366 / 366 identical** |
| L6 | `1b46fdb` | `90df5300e8ba7ce3181b59db7427c8b5` | **366 / 366 identical** |
| L4 = tip | `ab9cc5b` | `7a8b5e2c3b86cdc19e3eec5a21aa189b` | **366 / 366 identical**; also the `.pbp` of `knap 12 3 3 1` under `BAGUETTE_NODE_LIMIT=100` (md5 `3bdf307a...`, same on both) |

Byte identity is the evidence that nothing in SPEC 3.4 moved: same search order, same
learned rows, same proof lines. Builds are reproducible (the same tree rebuilt gives the
same md5).

### The levers, two sentences each

* **#5 `Store.var_named`** -- was a linear scan whose header claimed a debug-only caller;
  `Pb_analysis`, `Analysis.support_of`, `Learn`, `Pb` and `Search` call it on the conflict
  path. Now a hash index built LAZILY on first use (`Engine.oracle_accepts` creates a
  scratch store per tuple and never asks), keeping the FIRST index per name as the scan
  did; `var_named_scan` is kept as the specification and `test_core` pins the two together
  on a store with a duplicated name (break: a last-wins index fails all four checks).
* **#3 `Analysis.scan_support`** -- compared `String.equal (Store.name e.var) name` at every
  trail entry. It now compares `Store.name_rep e.var` (the first variable bearing that name,
  an O(1) array read) with the `Var.t` `support_of` already holds: the same entries match,
  duplicate names included.
* **#6 compile on wide models** -- `Lit.sanitize` returns a clean identifier itself instead
  of `String.map`-copying it; `var_name`/`to_string` write into one right-sized buffer
  instead of `Printf.sprintf` plus a second concatenation for `~`; `var_compare` skips the C
  compare on a physically equal identifier. `Encoding.fresh_aux_name` rebuilt the sanitised
  name set of EVERY declared variable on EVERY auxiliary (O(vars) per `int_lin_ne`, so
  O(vars x rows) per compile) and now reads a set kept beside `ints`; both identifier tables
  are a `string`-specialised `Hashtbl.Make` (same hash, so same layout; no polymorphic
  `compare` per probe). The names are NORMATIVE and unchanged: `test_proof` checks every
  rendering against the old definitions copied verbatim (negative values, `min_int`, `$`,
  dots, non-ASCII, empty name).
* **#4, the local part** -- `Learned.combine`'s cancel stage `List.partition`ed the WHOLE
  remainder per variable and appended with `acc @ keep` (quadratic per combination; it is
  also what `Ladder.lift` calls); the group is the sorted prefix, so a `span` takes it.
  `Pb.propagate` computed every open term's ladder-effective coefficient by walking every
  term (O(n^2) per pass); terms are now grouped once per pass by (variable, polarity) in
  term order and each query walks only its group, with the same test and the same
  `Checked.add` sequence, so the same sums and the same overflow.

### Local before/after (seconds, minimum of 5, `--proof` on; `bench/m6t11/timing.sh`)

Per lever (each row is the lever ALONE against the binary before it), CPU user+sys:

| model | what it stresses | #5 | #3 | #6 | #4 |
|---|---|---|---|---|---|
| `width_sat_depth` | learned rows over one 99-rung ladder | 0.09 -> 0.10 | 0.10 -> 0.10 | 0.11 -> 0.10 | **0.10 -> 0.05 (2.0x)** |
| `knap 8 2 3 1` | PB learning, combination | 0.84 -> 0.81 | 0.74 -> 0.73 | 0.88 -> 0.80 | **0.77 -> 0.54 (1.43x)** |
| `knap 10 2 3 1` | same, longer | 5.85 -> 5.70 | 5.61 -> 5.47 | 5.81 -> 5.78 | **5.49 -> 4.41 (1.24x)** |
| `knap 12 3 3 1`, 100 nodes | trucking-like: the learned rows are long | 4.75 -> 4.64 | 5.21 -> 4.30 (1.21x, not reproduced elsewhere: read as noise) | 4.79 -> 4.76 | **4.59 -> 1.83 (2.51x)** |
| `ne 7 0` | 8-into-7 pigeonhole by `int_ne` | 1.92 -> 1.85 | 1.57 -> 1.66 | 1.97 -> 1.80 | 1.80 -> 1.77 |
| `ne 7 2000` | the same behind 2000 unconstrained variables | 4.92 -> 4.83 | 4.52 -> 4.59 | 4.89 -> 5.06 | 4.57 -> 4.59 |
| `wide 400 300 400` | compile: 400 vars x 301 values, 400 aux Booleans | 6.13 -> 6.24 | 6.51 -> 6.43 | **6.39 -> 5.09 (1.26x)** | 4.89 -> 4.64 |

All four together, BASE -> tip: `width_sat_depth` 0.09 -> 0.05 (1.8x), `knap 8` 1.57x,
`knap 10` 1.24x, `knap 12 @100` **4.91 -> 1.82 (2.70x)**, `ne 7` 0.99x, `ne 7 pad` 1.08x,
`wide` 1.22x. On `wide`, `--time`'s own phases (3 runs each): `compile` ~2.0 s -> ~1.55 s,
`opb` ~2.1 s -> ~1.85 s.

**What this says.** #4 is the lever that moves anything locally: the knapsack at 100
nodes reproduces D-0080's trucking profile (`Learned.cancel` 40 % inclusive, `Lit.var_compare`
11 % self) and is 2.7x faster with it. #6 moves a generated wide compile by ~1.25x, not
more, because the rest of that compile is in `Opb.normalise`/`Opb.var_names` (string-keyed
generic tables over rendered names, a request below) and in the GC. **#3 and #5 move
nothing measurable locally**: no local model makes `scan_support` fall through to its scan
often, and the suite's stores are small enough that a linear `var_named` is cheap (2000
padding variables did not show it either: the padded pigeonhole's time is in `Search`
per-node work over all variables, not in name lookup). They are shipped on D-0080's
profile evidence, which names them at ~60 % and 11 %, and the node is where they are judged.

### What #4 turned out to be, and what is left of it

Two quadratic loops, both local, both fixed above. After them the knapsack profile is
~40 % `Pb.propagate` -- the survey of every term and the group walk on every pass, with
no early exit -- plus `compare_val`/`caml_hash` (~12 %) from generic-`Hashtbl` probes on
the search path. A sorted-thresholds-with-running-sums version of `effective` was tried
(exact: every partial sum is bounded by the group total, so when the total does not
overflow the order does not matter; 209 170 large-row queries cross-checked equal) and
REJECTED by measurement: 1.83 s -> 2.7 s on `knap 12 @100`, because building the arrays
costs more per pass than the walks it saves. **Proposed, not shipped, design territory:**
watched slack for `Pb` (a counter maintained on bound events instead of a survey per
call) -- it changes when the propagator runs, so it needs its own argument that the
fixpoint and the trace lines are the same, and it is the next tier for tc-graph-color.

### Node measurement plan (D-0080's six instances, `bench/m6t9/prof.sh` with OLD = BASE, NEW = tip)

Same recipe as D-0080: `perf record -F 499 --call-graph dwarf` for 60 s, `--time-limit 60
--stats --time --proof`, nodes in 60 s and the self-time table, both binaries hashed; then
the corpus sweep of config (a') (`bench/m6t9/sweep.sh`, `BAGUETTE=` the tip) for fin /
nodes/s / killed against D-0080's (a') row, and `BAGUETTE_NODE_LIMIT` pairs to re-confirm
byte identity on the corpus instances themselves. What the profiles predict:

| instance | lever | D-0080 says | prediction |
|---|---|---|---|
| 2016 prize-collecting | #3 (+#5) | 21 % `Analysis.go` + 16 % `string_equal` + 10 % `Store.name` + 12 % `trail_entry` | the 26 % of string compare and name fetch goes; the scan itself (O(trail)) stays: **1.3-1.5x nodes/s** (12 -> ~16-18 in 60 s) |
| 2018 rotating-workforce | #5, #6 | compile 28.5 s; 11 % `Store.go` (`var_named`); `Bytes.map`/`Lit.fun` | `var_named` share to ~0; compile **-15 to -30 %** |
| 2009 black-hole | #6 | compile 73 s: `Bytes.map` 15 % + `Lit.fun` 10 % + hashing 12 % + GC 28 % | compile **73 s -> ~50-60 s**; GC and `Opb` remain |
| 2008 trucking | #4 | ~50 % `var_compare`/`List.part`/`var_equal`/`Learned` | the knapsack reproduces this shape at 2.5x: **1.5-2.5x nodes/s** |
| 2017 tc-graph-color | #4 | ~45 % `Pb.*` | the group walk removes the n^2; the survey stays: **1.2-1.6x** |
| 2011 costas-array 15 | none (control) | 61 % `Justify.go` (lever #2, not this task) | **~1.0x**; anything else is noise or a regression |

Also on the node: 2012 amaze2 and 2017 opd (never reached the search in 280 s) under
`--time` -- whether `compile` now finishes, and how much of it is `opb`.

## D-0086  Three root-conflict defects from the sweep: the root trace is gated on a WALK, a hole has one currency, a telescope stops at the declared top
Status: DECIDED (all three fixed; 120 000 sweep models clean)
Date: 2026-10-02
Task: M7-T22 (agent-root, wave 33), from D-0084 item 4's three cross-session requests.
Touches: `lib/core/search.ml` (the root arm of `dfs` and `root_needs_trace`),
`lib/core/prop/alldiff.ml`, `docs/PROOF-FORMAT.md` §4 (all_different row), `bench/fuzz/README.md`,
six new models.
Follows D-0064 (`Defining`), D-0084 (embedded derivations; element's `in_order_currency`),
D-0066/D-0073 (a `rup` is checked by being load-bearing).

### (a) The root arm writes the root trace when the derivation CONTAINS a `rup` leaf

**The defect.** With no decision on the stack, `dfs` justifies a numeric root conflict by
its own `pol`, and wrote the root trace first only when `top_defining e` -- a `Defining` at the
derivation's TOP level. A `Defining` nested under a `Term` (gcc's `bound_cancels`, alldiff's
`Gone_hole_root`, element's root-residue cancels) asks the claim index exactly the same way,
found it empty, and minted `rup <lit> >= 1` with nothing on the page to propagate from.
3.0.2 refused it: gcc 565, 1948, 12008, 23043, 26887; mix 11984, 12008, 12062, 24788;
seven `ad` seeds (25920 among them).

**Why the guard existed.** M4-T2 added the trace write so a `Defining` cites a line that is
there; it gated it so a root conflict that consults nothing kept its proof byte for byte.
That reason is still good: `test_matrix`'s depth-0 lanes pin "no trace and no nogood" and
"blanking the trace breaks the proof", and an unconditional write fails six of their checks
(measured) and puts 2..8 uncited lines on 11 of 124 model proofs (all root UNSAT, all still
verify).

**The rule.** `root_needs_trace` walks the whole derivation -- every `Term`, both sides of
every `Cut`, through `Deferred` -- and answers true on any leaf `Justify` writes as a `rup`
against the page: `Defining`, `Linear`, `Clause` (the last never reaches it, being routed to
`close_root_conflict`, which writes the trace itself; true anyway, since erring true costs
lines and erring false costs the proof). Including `Linear` is not speculative: it renders
as `rup` and needs the page just as a minted `Defining` does. Measured: byte-identical
`.opb`/`.pbp`/stdout over every model (hashed before and after, with and without the
`Linear` arm), `test_matrix` unchanged.

Rejected: "unconditional" (above), and "contains a `Defining`" alone (leaves a nested
`Linear` the same hole). The cost of the walk is a list of constructors to keep in step
with justify.ml; the comment on `root_needs_trace` names it.

Lanes `root_nested_defining_gcc_unsat` (gcc 565 shrunk; pre-fix refused at line 4,
`rup +1 ~n0_1_ge_2 >= 1 ;`, "not implied by reverse unit propagation") and
`root_nested_defining_alldiff_unsat` (ad 25920 shrunk; line 31, `rup +1 ~x1_eq_3 >= 1 ;`).
No SAT lane can exist: the arm is reached only by the refutation itself. The break is a
REFUSAL, which D-0066's vacuity cannot produce.

### (b) An interior Regin removal concludes the ORDER clause

**The defect.** `remove_one`'s explanation ended on `~y_eq_v`; the hole's trace line, and
every other propagator's hole (element's since D-0084), is `~y_ge_v \/ y_ge_(v+1)`. Element's
`excl_hole` embeds the remover's explanation and pairs it off against two order-literal rows,
so with an element RESULT in an all_different scope nothing cancelled and a root conflict's
row was "not contradicting" (18 `ad` seeds, 24319 and 25012 among them).

**The rule.** The convention belongs to the hole, not to its embedder: alldiff's
`in_order_currency` adds the value's forward channelling row `y_eq_v \/ ~y_ge_v \/ y_ge_(v+1)`,
divisor 1, to an INTERIOR removal (a removal at a bound is a bound move and keeps its form) --
element.ml's own function, one module over. Bridging in `excl_hole` instead was rejected:
it would make every future embedder learn which propagator punched a hole. Alldiff's own
derivations never read the entry's explanation (`gone_of` cites holes by level or facts), so
they are untouched. Measured: byte-identical over every model without all_different;
`alldiff_search_unsat`'s proof gains the cited row and verifies.

Lane `alldiff_regin_hole_element_unsat` (ad 24319 shrunk; the binary of the (c) commit is
refused at line 43, `conclusion UNSAT`, "not contradicting"). No SAT lane: a scratch search
of 20 000 SAT-biased all_different + element models found no instance under a decision; the
break is again a refusal.

### (c) The pigeonhole push's telescope stops at y's declared top

**The defect.** Neither a View nor an unmaterialised ladder: the rung asked for exists in no
encoding. `pass`'s pigeonhole arm pushes a contained y to `b + 1`, with `b` some variable's
upper bound. `overshoot_cancel` cancelled the residue `y_ge_(b+1)` by rungs from `hi(y)+1` to
`b` -- but when `b >= decl_hi(y)` that residue is the constant false and the rung
`y_ge_(decl_hi+1) -> y_ge_decl_hi` is not a row (its own comment states the condition; its
guard did not). Element was only the route that moved y's upper bound below the interval
end at the root (27 `ad` crashes). Reducing it found the sibling: `prune_summands`'s
telescope ran over `[lo(y) .. b]` regardless of y's declaration, so the plain pigeonhole
`var 1..3: a,b,c; var 1..2: d; all_different_int([a,b,c,d])` crashed with
`d_fwd has no constraint id` -- exit 2 on a four-variable legal model.

**The rule.** Both telescopes are capped at `decl_hi(y)`; the overshoot cancel runs only
when `b < decl_hi(y)`. Byte-identical over every existing model. Lanes
`alldiff_pigeonhole_narrow_unsat`, `alldiff_pigeonhole_narrow_sat` (the push under a
decision in a satisfiable model) and `alldiff_overshoot_decl_top_unsat` (ad 25203 shrunk);
the pre-fix binary exits 2 on all three.

### The sweep (bench/fuzz, seeds 1..30000 per mode)

| Mode | Before: rejected / crash | After: rejected / crash |
|---|---|---|
| gcc  | 5 / 0  | 0 / 0 |
| elem | 0 / 0  | 0 / 0 |
| mix  | 4 / 0  | 0 / 0 |
| ad   | 25 / 27 | 0 / 0 |

Before: `43b68bb`, binary sha256 `a57f296130906c3e7d9744f83f07928235828280bcc40b5661ccceb94f686ab4`.
After: `wave33-root` at M7-T22 (b), sha256 `7443a8a24907e9050c3df2dcd8de1f19048957d653d23931b997c089ae97be4b`.
120 000 models, no new failing shape. The invocation is in `bench/fuzz/README.md`.

## D-0087  M6-T13: Search's per-node cost stops scaling with the store, Opb's name tables are string-specialised, and global_cardinality_low_up is routed to gcc (unflattened)

**Status**: **SHIPPED (i), (ii) byte-identical; (iii) UNFLATTENED-UNTESTED**, 2026-10-02,
agent-speed2 (M6-T13), branch `wave34-speed2`. The node `fataepyc-07` was unreachable, so
every number is LOCAL (WSL2 laptop), minimum of 3 runs, `--proof` on, `ulimit -v 4000000`.
Ratios inside +-10 % are noise. Closes D-0085's two leftover requests and M7-T18's mznlib one.

### Binaries and the byte-identity verdict

`bench/m6t11/byte_identity.sh` (unchanged), every `test/models/*.fzn` plus the generated
extras `ne 7 {0,200,2000}`, `wide 400 300 400`, `knap 10 2 3 1` under `/tmp`:

| step | binary md5 | verdict |
|---|---|---|
| base (`bcfa43e`) | `e3a4a689aa43c10ddfa67b074c42c84a` | -- |
| (i) | `f00d22d9b28c5b56b246fa2743c7f365` | base -> (i): 399 artefacts / 133 models BYTE-IDENTICAL |
| (ii) | `c7d41e10b48b57387e9ae457953a66a0` | (i) -> (ii): 399 / 133 BYTE-IDENTICAL |
| (iii) | `c7d41e10b48b57387e9ae457953a66a0` | no OCaml changed; base -> final: 411 artefacts / 137 models BYTE-IDENTICAL |

### (i) `Search`: the staged form of a `seq_search` order

**Before.** At every node `dfs` built `unfixed store` (a scan of every store variable, list
then array) and `sequence` put every candidate in a fresh `Hashtbl` to ask which of a
phase's variables were live. Per-node cost O(store), constrained or not.

**After.** `sequence` records a STAGED form of its closure in `Search.staged_orders`, an
`Ephemeron.K1.Bucket` keyed by physical identity (a dropped order stays collectable), with a
one-entry cache in front, so `dfs` pays one `==` per node to find it. The staged form reads a
phase's live subset straight off the store (`Domain.size > 1`, `unfixed`'s own test, and an
out-of-store variable is never live) in the phase's array order; `dfs` builds
`unfixed store` only when every phase is exhausted, and then does exactly what it did
before. `unfixed` itself counts then fills (no list).

**Why it is the same search.** `dfs` only ever hands an order `unfixed store`, and against
that array "v is a candidate" is "Domain.size v > 1". So the staged answer equals the full
order's answer on `unfixed store` in every state; the fallback is reached in exactly the same
states with exactly the same array. SPEC 3.4 is untouched: which variable, which tie-break,
which value. The `order` TYPE did not change, and `sequence`'s closure is still a complete
order on ANY candidate array (test_compile's `decision_of ~cands` passes subsets that are not
`unfixed store`, and still gets the membership semantics). Orders with no staged form
(`spec_order`, `random_order`, the tests' own) take the old path unchanged.
test_compile.ml checks staged-vs-full agreement in the three states (first phase live, first
exhausted, all exhausted) and that a seq_search order HAS a staged form, since losing it would
be silent: correct and O(store) again.

**Not done, and why.** The unannotated default (`spec_order` = first_fail over everything)
is still O(unfixed) per node: choosing a minimum over all live variables is the heuristic,
and making it sub-linear needs a priority structure restored on backtrack -- a different row,
and one whose tie-break (earliest index among equals) would have to be re-proved, not just
re-measured. Padding variables that ARE live are still candidates there by SPEC 3.4.

| model (local, min of 3) | before | after | ratio |
|---|---|---|---|
| `ne 7 0` cpu | 1.24 s | 1.35 s | noise |
| `ne 7 200` cpu | 1.49 s | 1.23 s | 1.21x |
| `ne 7 2000` cpu | 3.49 s | 1.28 s | 2.73x |
| `timing.sh` ne7_pad2000 wall | 3.32 s | 1.18 s | 2.81x |
| `timing.sh` ne7 / knap8 / knap10 / knap12_nl100 wall | 1.40 / 0.43 / 3.41 / 1.47 | 1.22 / 0.40 / 3.39 / 1.47 | 1.15x / 1.07x / 1.01x / 1.00x |

The padded run is now padding-independent (1.35 / 1.23 / 1.28 s at 0 / 200 / 2000). A
3 % knap10 slowdown seen once against the (i)-only binary was layout: the two profiles were
symbol-for-symbol the same (`Pb` 30 %, no `Search` symbol above 0.04 %), and the final
binary measures 1.01x.

### (ii) `Opb`: string-specialised name tables, no `Printf` per term

`normalise`, `var_names`, `rename_comments` and `write`'s variable count use `Opb.Names`, a
`Hashtbl.Make` over `String.equal` and `Hashtbl.hash` (Encoding.Names' shape) in place of the
polymorphic table and its `compare_val` probe; `normalise` does one `find_opt` where it did
`mem` + `find`. `constr_body` and `objective_to_string` write `"%+d %s "` by hand ("+" for
`a >= 0`, "+0" included). **The key is still the RENDERED name.** `Lit.sanitize` is not
injective ("a.b" and "a_b" are two `pbvar`s and one OPB variable) and merging by name is the
current semantics; keying on `Lit.pbvar` would be faster and would change it, so it was not
done -- it needs an argument that no two live owners of one model collide, which nobody has
made. test_proof.ml pins the collision (`+1 a.b_ge_1 +2 a_b_ge_1` normalises to `+3 a_b_ge_1`)
and the sign rule. No table is iterated: every output order is an explicit list, so swapping
the table cannot move a byte.

| `gen.py wide 400 300 400` (min of 3, wall) | before (i) | after (ii) | ratio |
|---|---|---|---|
| local | 3.67 s | 3.28 s | 1.12x |
| `timing.sh` base -> final | 3.73 s | 3.08 s | 1.21x |

`compare_val` leaves the wide profile; what remains is GC and `caml_string_equal`/`caml_hash`
over rendered names (`Lit.render` per term) -- the pbvar key is the next step and it is the
argument above, not a table.

### (iii) `mznlib/fzn_global_cardinality_low_up.mzn`

The predicate is M7-T18's request text with one word changed: the counts array is
`array [int] of var int`, not `array [index_set(cover)]`, because the comprehension is 1-based
and a direct call with a cover not indexed from 1 would be an index-set mismatch (std's
`global_cardinality_low_up` passes `array1d(cover)`, where the two agree). Each count is
`var max(0, lbound[i])..min(length(x), ubound[i])`; equal bounds flatten to a constant, which
the front end takes as a view (D-0082). The `include "fzn_global_cardinality.mzn";` is
load-bearing (it declares `baguette_global_cardinality`).

**UNFLATTENED-UNTESTED.** There is no MiniZinc on this machine. What exists: the lanes
`test/models/gcc_low_up_{sat,unsat}.fzn`, HAND-WRITTEN as the flattener would emit them (one
`baguette_global_cardinality` call, counts `var 1..2`, `var 0..1` and the constant `2`), both
proofs VERIFIED (sat: unique `x = [1, 2, 3, 3]`; unsat: the refutation needs a low_up upper
bound and the constant); their provenance sources `mznlib/test/gcc_low_up_src_{sat,unsat}.mzn`,
named apart from the lanes so `check_mznlib.sh` does not byte-compare a hand-written body; and
three new directives in `check_mznlib.sh` -- `MUST-EMIT`, `MUST-NOT-EMIT`, `SOLVES-AS` (solve
the flattened model, verify its proof, diff against `test/expected/<name>.out`) -- exercised
here with a fake flattener in both directions (copying the lane: 7 ok; copying a decomposition:
both low_up sources FAIL on all three directives). Until someone runs, on a node with a
flattener,

    MZN=/path/to/minizinc mznlib/test/check_mznlib.sh

the `.mzn` is a file nobody has type-checked.

### Node plan (fataepyc-07 unreachable)

1. `MZN=<minizinc> mznlib/test/check_mznlib.sh` -- the (iii) validation; expect `mznlib: 7 ok, 0 failed`.
2. `bench/m6t11/byte_identity.sh` base vs final over the suite plus the corpus instances that
   carry a `seq_search`/`int_search` annotation, then `bench/m6t11/timing.sh` base vs final.
3. Re-run D-0081's shared-set comparison (`scripts/compare_run.sh`) with the final binary and
   read the median: (i) moves only annotated instances with many unannotated variables, (ii)
   moves compile-dominated wide instances.

---

## D-0088  M6-T14: per-variable trail histories replace the support and remover scans

**Mechanism.** `Store` keeps, per variable, the trail positions of its live entries in
increasing order: `lo_hist` (the entries that raised its lower bound), `hi_hist` (the ones that
lowered its upper bound) and `all_hist` (every entry on it). `apply` pushes onto them where it
already writes `lo_sup`/`hi_sup`, and `undo_to` pops them as it pops the entry, which is always
the newest, so always the top. By I-D3 each entry's `old` is its predecessor's `now`, and bounds
and domains only shrink. So "which entry established `x >= v`" is the FIRST lower-bound move
whose `now` reaches `v`, and that entry counts only if its `old` does not already reach `v`.
"Which entry removed value `u`" is likewise the first entry whose `now` lacks `u`, and it
counts only if its `old` held `u`. Each is a binary search, and each answer is unique among
live entries, so "strictly below `before`" is one comparison, not a search.
`Store.bound_support` replaces `Analysis.scan_support`'s downward walk. That walk ran once per
fact per resolution step, so the cost was quadratic in trail depth. `bound_support` keeps the
walk's `name_rep` semantics: with duplicate names it takes the max over the class, which is
built lazily and only exists when some name is shared, i.e. never in a `Compile` store.
`Store.remover` gets the same treatment, and so does `Pb_analysis.falsified_at`, whose scan
compares `Var.equal` and so uses `Store.var_support` on the exact variable. `Store.establishes`
now holds the one predicate (moved from `Analysis`, which re-exports it), so the history search
and the scan share it, including its `>=`/`<=` asymmetry.
All three scans (`Analysis.scan_support`, `Store.remover_scan`, `Pb_analysis.falsified_at_scan`)
survive for one wave as `BAGUETTE_DEBUG` cross-checks and as the unit tests' oracles. Delete
them next wave.

**Cost.** One int per trail entry in `all_hist`, plus one per bound move in `lo_hist`/`hi_hist`
(two for a `fix`). The arrays are allocated on a variable's first move and doubled when full.
A lookup is O(log moves of that variable) instead of O(|trail|).
`check_invariants` asserts that each history is sorted, names live entries on its own variable
that moved its bound, has the O(1) array's answer at its top, and that the `all_hist` lengths
sum to the trail length.

**Byte identity.** `bench/m6t11/byte_identity.sh` over the suite (132 models, 396 artefacts):
**BYTE-IDENTICAL** for both commits. OLD is `main`'s base (md5 `c7d41e10…`). NEW is `5c29c62`
(md5 `57f2ee14…`, support history only) and `08d01b2` (md5 `acd28dc2…`, plus `remover`). Under
`BAGUETTE_DEBUG=1` none of the three cross-checks fires on any suite model. Four element models
die on a PRE-EXISTING D-0026 agreement check, and the OLD binary dies the same way (filed as a
cross-session request).

**On the node** (fataepyc-07, `--time-limit 55`, the node under a running sweep; OLD =
`/scratch/arthur/baguette` md5 `8b8d4718…`, NEW = `08d01b2` md5 `df3a0c6f…`):

| instance | OLD nodes / 55 s | NEW nodes / 55 s | ratio |
|---|---|---|---|
| 2014_mario | 262 | 1494 | 5.7x |
| 2023_chessboard | 1486 | 1806 | 1.22x |

The support history alone (`5c29c62`) gave 520 and 1785. Neither instance finishes within
300 s on NEW: mario reaches 5989 nodes, chessboard 6654 nodes and 2523 learned. Both 55 s proofs
are `s VERIFIED NO CONCLUSION` under veripb 3.0.2 (278 s and 14 s).

**What remains in the profile** (60 s `perf record -g` on NEW). `Store.name_rep`,
`Store.trail_entry` and `Analysis.go` are gone from the top. On 2014_mario, 40 % of self time is
`Trace.position_of`, a linear walk over `done_` by physical identity, and 5 % is `@`, from
`Trace.add_fact`'s `acc @ [l]`. Both are in `lib/core/trace.ml`, which is not this row's file
(filed). On 2023_chessboard nothing dominates: the GC (`do_some_marking`, `oldify_one`,
`pool_sweep`, `caml_shared_try_alloc`, about 21 % together), `compare_val`, `List.map` and
`Pb.status`, each 3–5 %. That is allocation, not a walk.

## D-0089  The first three-solver comparison, and the wave-31..34 tip on the corpus: 84 solved, 0 rejected, 0 disagreements

**Status**: **MEASUREMENT**, recorded 2026-10-02 by the orchestrator from five runs on
`fataepyc-07`, all complete (`DONE-` markers checked), all with veripb 3.0.2 on every proof
baguette or GCS produced. Chuffed 0.14.0 (`d3079869…`, the MiniZinc 2.10.1 bundle, annotation
search, no free search); GCS commit `5882c294` (`ebffdc08…`, `--prove`, 16 GB proof-file cap);
Chuffed and GCS flatten with THEIR libraries plus `mznlib/compat_mzn1.mzn` for the 1.x models
(D-0081). The pinned data pairing is `bench/corpus/answers.tsv`. Harness: `scripts/compare_run.sh`
(M6-T4) and `scripts/corpus_run.sh` (M7-T4, with M6-T9's `UNKNOWN-LIMIT`).

### 1. The overnight runs (2026-10-01 → 02), binary `b37ec100…` = `main` at `56ae463`

Wave 31 merged except M6-T9, so no `--time-limit`. The node also carried agent-perf's sweep,
so the `TIMEOUT` columns of these two runs are pessimistic against D-0079's.

**Corpus (`corpus-out-w31`)**: `TIMEOUT-SOLVE` 291, `REFUSED-RESOURCE` 58, **`OK-PROOF-VERIFIED`
58**, `NO-DATA` 20, `FLATTEN-FAIL` 4, `SOLVE-ERR-134` 3, `REFUSED-MODEL` 1 (`connect`, bounded
below only), `FLATTEN-TIMEOUT` 1, **`PROOF-REJECTED` 0**.

**Three solvers (`compare-out-w31`)**, 436 × 3:

| status | baguette | Chuffed | GCS (proofs on) |
|---|---|---|---|
| SAT / UNSAT / OPT | 15 / 4 / 41 = **60** | 44 / 10 / 218 = **272** | 29 / 6 / 59 = **94** |
| TIMEOUT (300 s) | 289 | 139 | 40 |
| CAPPED (16 GB proof) | 0 | 0 | **273** |
| REFUSED | 59 | 0 | 0 |
| ERROR | 3 | 0 | 4 |
| proofs verified / rejected / check-timeout / check-error | **60 / 0 / 0 / 0** | — | 46 / **15** / 32 / 1 |

Agreement: **114 AGREE, 0 DISAGREE**, 0 mismatches against the pinned answers. On the 40
instances all three solved: median wall baguette **5.87 s**, Chuffed **0.12 s**, GCS **0.22 s**;
PAR2 over 436: 524 / 240 / 479; median `.pbp` baguette 2.9 MB vs GCS 6.0 MB; median check
0.52 s vs 1.22 s.

**GCS's 15 rejected proofs** are a finding about GCS or about the one checker, not about this
project, and every one of them is on an instance where all three solvers agree on the optimum:
`2011_prize-collecting_pc`, `2011/2012/2014_ship-schedule`, `2013_mario`, `2014_mario`,
`2013_proteindesign12_wcsp`, `2014_smelt`, `2014_stochastic-fjsp…det`, `2023_table-layout`,
`2025_atsp`, `2025_mondoku…balance` ("not implied by reverse unit propagation"); `2015_is_model`,
`2019_stochastic-vrp…det`, `2025_is_model` ("the propagated assignment does not satisfy the
constraint"); plus `2013_fjsp` where the checker itself aborted (rc 134). Artefacts under
`/scratch/arthur/compare-out-w31/log/`. GCS with proofs on hits the 16 GB cap on 273 of 436;
GCS with proofs OFF solves 149 (D-0081).

### 2. The wave-31..34 tip, binary `8b8d4718…` = `main` at `9ff90da` (2026-10-02, node otherwise idle)

**The 27 formerly-rejected instances (`corpus-out-w35-rejected`, `--time-limit 280`)**: 26
`UNKNOWN-LIMIT` — every stopped proof **VERIFIED NO CONCLUSION** — and `2025_stripboard`, the
one whose 1.5 GB proof was rejected under D-0080's config (d), now **solved to proved optimality**
(`s VERIFIED BOUNDS 90 <= obj <= 90`, 1.65 GB). **0 `PROOF-REJECTED`**: D-0084's two fixes held
on the real instances. The 26 run at 2–20 nodes/s, which is what opened M6-T14.

**Corpus with `--time-limit 280` (`corpus-out-w35`)**, `PAR=64`:

| outcome | count | note |
|---|---|---|
| **`OK-PROOF-VERIFIED`** | **81** | 58 → 81; **23 new, 0 lost** against wave 30 |
| `UNKNOWN-LIMIT` | 189 | stopped itself, proof checked: **all accepted** |
| `TIMEOUT-SOLVE` | 60 | killed from outside: 49 in a single slow node, 11 before the handler (parse/compile/.opb) |
| `TIMEOUT-CHECK` | 12 | solved, but veripb exceeded 900 s on proofs of 31–163+ MB |
| `REFUSED-RESOURCE` | 64 | widths 10 000 – 78 million (58 → 64: inference bounded four `var int`s wide) |
| `REFUSED-LIMIT` / `SOLVE-ERR-134` / `REFUSED-MODEL` | 2 / 2 / 1 | all width-shaped except `connect` |
| `NO-DATA` / `FLATTEN-FAIL` / `FLATTEN-TIMEOUT` | 20 / 4 / 1 | the corpus's |
| **`PROOF-REJECTED`** | **0** | over 270 checked proofs |

Nodes/s on the 189 stopped runs: min 0.004, p25 2.15, **median 9.6**, p75 21.6, max 161.

**Baguette alone through the comparison harness (`compare-out-w35-baguette`, no time limit)**:
**84 solved** (21 SAT, 5 UNSAT, 58 OPT), 83 proofs verified + 1 check timeout, 258 TIMEOUT,
67 REFUSED. Joined with the wave-31 Chuffed and GCS tables: **127 AGREE, 0 DISAGREE, 0 pin
mismatches**. On the 51 instances all three solved:

| solver | median wall | mean | PAR2 (436) | median `.pbp` | median check |
|---|---|---|---|---|---|
| baguette | **4.22 s** | 33.5 s | 492.6 | 8.2 MB | 1.42 s |
| Chuffed | 0.12 s | 0.26 s | 240.5 | — | — |
| GCS (proofs) | 0.42 s | 17.0 s | 478.9 | 23.3 MB | 4.13 s |

### 3. What it says

1. **The oracle is clean.** Over every instance any two solvers both answered, 0 disagreements and
   0 pinned-answer mismatches; over 353 checked baguette proofs today, 0 rejected. The 26 defects
   D-0080 surfaced are gone on the instances that surfaced them.
2. **Coverage**: 58 → 81 solved under the corpus harness, 60 → 84 under the comparison harness,
   with nothing lost. Chuffed solves 272, GCS 94 with proofs (149 without). Baguette's PAR2 is
   now within 3 % of GCS-with-proofs; both are twice Chuffed's.
3. **Speed is still the gap**: 35× Chuffed and 10× GCS at the median on the common set, and the
   median stopped run does 9.6 nodes/s. The profile behind the slow quartile is in `Trace`
   (D-0088, M6-T15) now that `Analysis`'s scans are gone (M6-T14, merged after these runs — so
   every figure here is BEFORE M6-T14's 5.7× on mario).
4. **Proof size is a strength**: a third of GCS's at the median, checked three times faster.
   But 12 solved instances could not be checked within 900 s, and the proofs of the 189 stopped
   runs are tens of MB each: M4-T5's RUP hints are the row that would move the check column.
5. **The width wall** (64 + 2 + 2 instances) is D-0028's and untouched; a different encoding of
   wide domains is a decision not yet taken.
### Addendum, 2026-10-02 evening: the 1-shifted geometric mean

At the user's request the summary statistic is the **1-shifted geometric mean**
(exp(mean(log(1 + x))) − 1, in x's unit) rather than the median, and
`tools/compare/compare.py`'s report now prints it beside PAR2. The same two common sets as
above:

| set | solver | sgm+1 wall | PAR2 (436) | sgm+1 `.pbp` | sgm+1 check | checked n |
|---|---|---|---|---|---|---|
| wave 31, 40 common | baguette | **8.51 s** | 524.3 | 3.5 MB | 0.88 s | 40 |
| | Chuffed | **0.16 s** | 240.5 | — | — | — |
| | GCS | **1.80 s** | 478.9 | 21.4 MB | 4.81 s | 36 |
| wave 35 baguette + wave 31 others, 51 common | baguette | **7.26 s** | 492.6 | 8.5 MB | 2.33 s | 50 |
| | Chuffed | **0.20 s** | 240.5 | — | — | — |
| | GCS | **2.28 s** | 478.9 | 35.7 MB | 6.62 s | 42 |

Pairwise, on every instance both solved: baguette/Chuffed n=84, 9.35 s vs 0.40 s;
baguette/GCS n=51, 7.26 s vs 2.28 s. So the gap on the common set reads **36× Chuffed and
3.2× GCS**, and the proofs are **4× smaller than GCS's**. The check column counts only
VERIFIED proofs, which flatters GCS (42 of 51).

## D-0090  M6-T15: `Trace.position_of` from the entry's own trail position, `add_fact` by a reversed accumulator

**Mechanism.** `Store.entry` gains one immutable field, `pos`: the trail position the entry
was pushed at (`-1` for `dummy_entry`). `apply` is the only constructor, and it pushes the
record it builds at exactly `trail_len`. No entry is ever re-pushed, so an entry occupies one
trail position for its whole life. `push_entry` asserts `e.pos = trail_len` under
`BAGUETTE_DEBUG`. `Trace.position_of` becomes `if 0 <= p < n_done && done_.(p) == e then Some p
else None` with `p = e.pos`. No second data structure is needed. `remember` is the only writer
of `done_`, and it is called only from `emit`, with `done_.(i) <- Store.trail_entry store i`. So
an entry can be in `done_.(0 .. n_done-1)` only at its own `pos`. The walk's first hit is
therefore its only hit, and it is `e.pos` exactly when `done_.(e.pos) == e`. The `None` case is
that same test failing.

**Wipe rule.** Unchanged, because there is nothing new to wipe. `resync` still lowers `n_done`
to the common prefix with the trail, and `remember` still overwrites a slot when it is
refilled. Between a backtrack and the next `emit`, a popped entry is still "found" at its old
slot. The walk found it there too, and the new code reproduces that (the unit scene checks
it). **No line is written twice for one entry at different levels.** An entry has one `pos`,
and its level is `Store.level_of_index store pos`. A refilled slot holds a DIFFERENT entry, and
`remember` clears that slot's `line_ids` first.

**`add_fact`.** It is now `add_fact_rev`, which conses onto a reversed accumulator.
`settle_facts` reverses `base` once, folds, and reverses once at the end. It does the same for
its `cited` list, which also appended with `@`. The dedup still asks `List.exists Lit.equal`
over the same set, so first-occurrence semantics and the written order are unchanged. With no
settled-over holes, `settle_facts` returns `base` itself, as the fold over `[]` did.

**Cross-check, one wave.** The old walk survives as `Trace.position_of_scan`. Under
`BAGUETTE_DEBUG` it is compared with `position_of` at every call. `test_trace` adds a scene that
writes lines at levels 0, 1 and 2, wipes level 2, re-pushes it with different entries, re-emits,
and then backtracks to 0. It checks every entry's position against both the walk and the
expected value at each step: 60+ checks, plus 5 `add_fact_rev` cases checked against the old
`acc @ [l]`. Mutation: dropping the `done_.(p) == e` guard turns 7 of those checks red. Under
`BAGUETTE_DEBUG=1` the cross-check fires nowhere: 0 hits over the 132 suite models and 0 in
`dune runtest --force`. The debug fatals that remain are pre-existing and belong to M6-T8: the
four element models' D-0026 check and one `test_learn` I-S4 lane.

**Byte identity.** `bench/m6t11/byte_identity.sh` reports **BYTE-IDENTICAL, 396 artefacts over
132 models**. OLD is `6b277a7` (md5 `acd28dc2…`) and NEW is `89991e0` (md5 `8f84d6f6…`).

**On the node** (fataepyc-07, `--time-limit 55`, `ulimit -v 32000000`, four jobs at once).
Both binaries were built in `/scratch/arthur/baguette-speed4`: OLD is `6b277a7` (md5
`df3a0c6f…`, the same md5 as D-0088's NEW) and NEW is `89991e0` (md5 `71b2f9f3…`). The
`/scratch/arthur/baguette` checkout is at `f61aaa6`, which predates M6-T14 (md5 `8b8d4718…`), so
it was not used as OLD.

| instance | OLD nodes / 55 s | NEW nodes / 55 s | ratio |
|---|---|---|---|
| 2014_mario | 1697 | 2575 | 1.52x |
| 2023_chessboard | 3003 | 3027 | 1.01x |

Peak RSS on NEW is 596 MB for mario and 373 MB for chessboard. veripb 3.0.2 gives `s VERIFIED NO
CONCLUSION` on both NEW proofs (mario in 488 s, chessboard in 20 s). Chessboard was never
trace-bound, as D-0088 already noted, so 1.01x is expected.

**What remains** (60 s `perf record -g` on NEW, 2014_mario, 2696 nodes). `Trace.go` is gone from
the profile. The top four self-time symbols are `Stdlib.@` (9.3 %), `caml_apply2` (4.7 %),
`caml_shared_try_alloc` (4.2 %) and `oldify_one` (4.2 %). Next come `do_some_marking` 3.6 %,
`pool_sweep` 3.2 %, `Alldiff.go` 3.1 % and `Analysis.same_slot` 2.9 %. The remaining `@` does not
come from `Trace`. A DWARF call-graph sample attributes 83 % of it to an anonymous function in
`Analysis`. That is almost certainly `lib/core/analysis.ml:395`'s node merge, `out @ [ n ]`
after a `List.map` with `same_slot`, which is quadratic in the frontier. Filed as a request,
because `analysis.ml` is not this row's file.
## D-0091  M6-T8: `BAGUETTE_DEBUG=1` is clean on every model; the four element fatals were the agreement check over-reading a ROOT `Defining`

**Status**: **SHIPPED** on `wave36-debug`, 2026-10-02 (agent-debug). Two unit binaries
(`test_compile`, `test_learn`) still need a harness edit in files this row does not hold.
Both are filed as requests, and both edits were measured to make their binary clean.
Every artefact is byte-identical: 396 over 132 models, base `acd28dc2…` against new
`a9fcf487…`. The predicate only runs under `Debug.enabled`.

### The four models: one call, classification (c)

| Model | Fatal | Class | Fix |
|---|---|---|---|
| `alldiff_regin_hole_element_unsat` | D-0026 reverse arm: `reason [-]` vs a combine whose top level is `2*defining(~x4_ge_4)` | (c) | predicate |
| `element_crossed_root_unsat` | same, `defining(x6_ge_4) + defining(~x6_ge_5)` | (c) | predicate |
| `element_moved_unsat` | same, `2*defining(~c_ge_3)` | (c) | predicate |
| `element_shared_result_root_unsat` | same, `2*defining(~x1_ge_5)` | (c) | predicate |

The backtraces show that all four fatals come from one call:
`Element.no_position_conflict`, reached from `filter_index`'s emptying removal at the root.
Its reason is `Reason.none` on purpose. `Trace.conflict_line` would write a `rup` over the
reason's facts, and the counting argument is not RUP once a hole is involved. Its derivation
cancels each root-established residue bound with a top-level `Explanation.Defining`
(`residue_cancel`, M7-T21/D-0084). `Explanation.top_weaken_owners` counted a `Defining` exactly
like a `Weaken`, so the reverse arm required the empty reason to name that variable.

The reverse arm exists for I-P5. If a reason omits a variable the derivation read, the trace
line ends up over too short a tail, and a learned clause built from it is not entailed. That
harm cannot happen for a fact the ROOT holds. D-0064's construction rule lets a `Defining`
cite only a model consequence (`established_at_root` in element and alldiff, `root` in gcc).
Its unit line sits at level 0 and is never wiped, and `Analysis` drops root nodes from every
cut. A fact like that is in no branch's dependency, so a reason that leaves it out is not
short in the I-P5 sense. D-0038 says the same thing for the forward arm: a bound the
derivation cites *by id* does not have to appear as a literal. So the check was wrong about
what "uses" means for this term, and neither propagator was at fault.

**The fix is in the predicate, and the store decides it.** `Store.reverse_owners` is
`top_weaken_owners` minus each top-level `Defining` on an order literal that `Store.root_holds`
confirms. That means the current bound implies the literal, and the entry supporting the bound
was pushed at level 0 or never moved. The arm still requires every `Weaken`, every `Defining`
on a bound set under a decision (the D-0064 violation), and every direct-literal `Defining`. No
caller in `lib/` needs the direct-literal case, and settling whether a hole is root-held would
need `remover`. `test_core.ml` (`test_agreement_root_defining`, 11 checks) pins the arm with
pairs that differ only in the level the bound was set at. `test_prop.ml`
(`test_d0091_element_root_defining`, 6 checks) asserts the predicate on
`element_moved_unsat`'s real conflict. It also shows the scene exercises the arm: the
`Defining` on `c` is present, and the empty reason does not name `c`. As a break, putting the
old arm back fails 4 of these checks.

`store.ml` is held by agent-speed4 for the entry position. This row's edit is limited to
`agreement_holds` and the three helpers above it (`at_root`, `root_holds`, `reverse_owners`),
and speed4's hunks are elsewhere in the file.

### No fix was a (b), but there is a (b)-shaped finding

No reason in these four was incomplete in a way that could make a learned clause unsound. One
sentence is still worth keeping. **Element's conflicts carry `Reason.none` at every depth.**
That under-states what their dead-position terms read: the bounds and holes of the index and
the result. The D-0026 check cannot see this, because it does not look inside `Term`s. It is
sound only because of two guards, neither of which exists for this case. `Trace.conflict_line`
writes nothing over an empty tail. `Learn.at_conflict` returns `None` on an empty cut: the
1UIP postcondition `count <= 1` holds vacuously, and `ls = []` declines. The search then falls
back to the full decision nogood. So an element conflict under a decision never yields a 1UIP
clause. That is an explanation-quality gap in D-0054's sense (the reason is not *useful* to
propagation), not a soundness defect. Closing it needs a conflict line that `rup` can check:
an explicit `pol` before the line, which is D-0039's move. That means work in `trace.ml`, and
it is not done here.

### The harness fatals

Each of these was hidden behind an earlier death in the same binary.

- **`test_prop`** (fixed). `arith_root_box`, `arith_root_domains`, the Regin oracle scene and
  the staging scene propagate alldiff with no proof started. The D-0026 check forces every
  justification at push time, so alldiff's `need` raised (`d_fwd`/`at-least-one has no
  constraint id`). The guard did its job; the harness was the problem. Fix: `sink_proof` /
  `with_proof_sink` start a proof into `/dev/null`, as the CLI always does. The binary now
  gives 518 ok with the flag and 518 ok without it.
- **`test_compile`** (requested). `test_element_oracle` and `test_element_view` have the same
  element shape. Two `Encoding.start_proof` lines make the binary clean: 221 ok with the flag,
  221 without.
- **`test_learn`** (requested). Under the flag, the `b BREAK` lane of `test_i_s4_ordering`
  (`break_i_s4 = true`) is stopped by `Search`'s own I-S4 `Debug.check`. **The debug gate is
  catching the break**, which is right. The lane assumes the flag is off. The measured patch
  makes the lane assert the `Failure` when `Debug.enabled`, and makes no other change: 167 ok
  with the flag, 169 without.

### What `BAGUETTE_DEBUG=1` now covers end to end

All 132 model tests pass under the flag. 21 of the 23 unit binaries run clean under it, and the
other two run clean once their requested edits land. Nothing was weakened. No check, test or
expected output was relaxed to pass. The one predicate change narrows a requirement only where
the store proves it cannot matter.

## D-0092  M6-T16: `Analysis` merges its frontier and accumulates its antecedents in linear time

**Date.** 2026-10-02. **Row.** M6-T16 (agent-speed5, `wave37-speed5`), from D-0090's request.

**The finding.** After M6-T15, `Stdlib.@` was the top self-time symbol on 2014_mario (9.3 %), and
83 % of it was in `Analysis`. Each resolution step folded `add_node` over the facts it added.
`add_node` maps the whole frontier with `same_slot` and then appends with `out @ [ n ]`, so one
step costs O(|frontier| x |facts|). `add_antecedent` used `List.mem` and then `@`, and `folds`
was appended with `@` as well.

**Mechanism.**
- `Analysis.Frontier` holds a list of mutable CELLS in frontier order, plus one monomorphic
  `Hashtbl.Make(String)` table per bound direction that maps a variable's name to its cell. The
  table lives for one `analyse` call. An incoming fact whose slot is already present merges into
  that cell in place, as `stronger existing new`. On a tie this keeps the existing node, exactly as
  `add_node` did. A fact on a new slot gets a new cell, appended after every existing cell in
  first-arrival order. Later facts on that slot merge into the cell and do not move it.
  **Position goes to the first occurrence; `stronger` decides the content.** `Frontier.remove` is
  the expansion step's `List.filter` on slot and value. It also drops the cell's table entry, so a
  later fact on the expanded slot is treated as a new slot and goes at the end, as before. `mk_node`
  still runs once per fact, in order, so its counters and its `Bad` exception fire in the same order.
- `Analysis.Uniq` is an insertion-ordered int set (a `Hashtbl` beside a reversed list). It returns
  elements in first-occurrence order, which is what `List.mem`/`@` produced. `folds` is a reversed
  accumulator, reversed once at the end.
- `add_node` stays as the SPECIFICATION. `test_analysis` builds a frontier by hand that covers every
  case: in-place strengthening, a tie, a weaker fact, a new slot merged again later, both bounds of
  one variable, an empty frontier, and remove-then-re-add. It checks that the sequence matches the
  `add_node` fold and a hand-written expected string. A second check compares `Uniq` with the old
  `List.mem`/`@` and with a literal list. To show the tests can fail, three mutants were built.
  Swapping the tie made 3 checks fail. Dropping fresh cells crashed the binary. Dropping the table
  removal in `remove` failed the re-add check, and two scene-2 checks failed with it.

**A first version was rejected, and the reason is the lesson.** The first version rebuilt a
polymorphic `(string * bool) Hashtbl` from the whole frontier at every step. It was byte-identical
(NEW md5 `d7c7d33d…`) and gave 1.36x on mario, but **0.91x on 2023_chessboard**, reproduced three
times (3004/2996/3019 old vs 2713/2740/2736 new). In chessboard's profile, `caml_hash` (4.8 %),
`compare_val` (3.1 %) and `caml_hash_mix_string` (2.5 %) replaced the `same_slot`/`String.equal`
scans. Re-hashing every frontier node on every step with tuple keys and polymorphic compare cost
more than chessboard's short scans. The persistent table with monomorphic keys hashes only incoming
facts.

**Byte identity.** `bench/m6t11/byte_identity.sh` reports **BYTE-IDENTICAL, 396 artefacts over
132 models**. OLD is `63ca870` (local md5 `8f84d6f6…`) and NEW is `47a4e2c` (local md5 `34f25113…`).

**On the node** (fataepyc-07, `--time-limit 55 --stats --proof`, `ulimit -v 32000000`, two rounds
of four jobs each). Both binaries were built from `/scratch/arthur/baguette-speed5{,-base}`. OLD is
`63ca870` (md5 `71b2f9f3…`, the same md5 as D-0090's NEW) and NEW is `47a4e2c` (md5 `59eb7654…`).

| instance | OLD nodes / 55 s (r1, r2) | NEW nodes / 55 s (r1, r2) | ratio |
|---|---|---|---|
| 2014_mario | 2534, 2581 | 3576, 3569 | 1.40x |
| 2023_chessboard | 3037, 3048 | 3250, 3253 | 1.07x |

veripb 3.0.2 on the NEW r1 proofs: chessboard `s VERIFIED NO CONCLUSION` (22 s, 105 MB). mario:
`s VERIFIED NO CONCLUSION` (732 s, 206 MB).

**What remains** (60 s `perf record -g -F 999` on NEW, 2014_mario). `Stdlib.@` fell from 9.3 % to
about 1.0 % (`@_dps` 0.79 %, `@` 0.22 %). All of `Analysis` together is about 1.6 % inclusive. The
top four self-time symbols are now `caml_apply2` 7.0 % (closure dispatch, under
`Search.branch_split`), `Alldiff.go` 4.7 %, `caml_hash` 4.1 % and `compare_val` 3.6 %. Next come
`Hashtbl.do_bucket` 3.0 %, `Store.trail_entry` 2.7 %, GC (`oldify_one`, `do_some_marking`,
`caml_shared_try_alloc`, each about 2 %) and `Store.remover` 2.1 %. A DWARF sample gives only
partial unwinds. Where it does unwind, the generic hashing (`caml_hash`, `compare_val`,
`Hashtbl.do_bucket`/`fold`/`filter_map_inplace`) sits under `Justify`'s memo and
`Justify.wipe_level`/`Writer.wipe_level` (about 2.1–2.5 % inclusive each). It does not sit under
`Analysis`.

**The profile is now flat.** No symbol is above 7 %, and the leaders are generic runtime costs:
closure application, polymorphic hashing and compare, and GC. They are spread over `Search`,
`Justify`, `Writer` and `Alldiff`, with no single quadratic hotspot left. This is the point where
constant-factor work stops paying for itself one row at a time. What remains are the design-level
proposals in D-0085/D-0087: a watched-slack PB/linear propagation, and a priority structure for the
default `first_fail` in place of a per-node scan over all variables. The one constant-factor lead
left is that the `wipe_level` tables in `Justify`/`Writer` are generic `Hashtbl`s, folded or
filtered whole at every backtrack. It is filed as a request, because those files are not this row's.

## D-0093  The week's final binary on the corpus: 87 verified + 25 unchecked solves, 92 in the comparison, PAR2 within 1 % of GCS

**Status**: **MEASUREMENT**, recorded 2026-10-02 (evening) by the orchestrator from two complete
runs on `fataepyc-07` (`DONE-` markers checked), binary md5 `9bdd6f16bce396296199d57867523d69` =
`main` at `5c299cb`: waves 31–37 whole — M6-T9/T10/T11/T13/T14/T15/T16 on speed, M7-T17..T22 on
proofs and coverage, M6-T4's harness. Statistic: PAR2 and the 1-shifted geometric mean (D-0089
addendum). Same protocol as D-0089 §2, same node, the node otherwise idle.

### Corpus with `--time-limit 280` (`corpus-out-w36`, `PAR=64`) against D-0089 §2

| outcome | wave 35 (`9ff90da`) | **final (`5c299cb`)** | note |
|---|---|---|---|
| **`OK-PROOF-VERIFIED`** | 81 | **87** | 6 new, 0 lost |
| `TIMEOUT-CHECK` | 12 | **25** | solved, proof not checked within 900 s: **solved total 93 → 112** |
| `UNKNOWN-LIMIT` | 189 | 178 | stopped itself; every proof accepted |
| `TIMEOUT-SOLVE` | 60 | 51 | killed from outside, in one slow node or before the handler |
| `REFUSED-RESOURCE` / `-LIMIT` / `SOLVE-ERR` / `REFUSED-MODEL` | 64 / 2 / 2 / 1 | 66 / 2 / 1 / 1 | the width wall (D-0028), unchanged in kind |
| `NO-DATA` / `FLATTEN-FAIL` / `FLATTEN-TIMEOUT` | 20 / 4 / 1 | 20 / 4 / 1 | the corpus's |
| **`PROOF-REJECTED`** | 0 | **0** | over 265 checked proofs |

Nodes/s on the stopped runs: p25 2.15 → **5.39**, median 9.6 → **18.1**, p75 21.6 → 29.4,
max 161 → 174. (Before wave 31 the median was 1.44, D-0080.)

### Baguette through the comparison harness (`compare-out-w36-baguette`), joined with wave 31's Chuffed and GCS

| | start of week (`56ae463`) | `9ff90da` | **final (`5c299cb`)** | Chuffed | GCS (proofs) |
|---|---|---|---|---|---|
| solved (SAT / UNSAT / OPT) | 60 | 84 | **92** (20 / 5 / 67) | 272 | 94 |
| proofs verified / rejected / check-timeout | 60 / 0 / 0 | 83 / 0 / 1 | **89 / 0 / 3** | — | 46 / 15 / 32 |
| PAR2 over 436 | 524.3 | 492.6 | **483.6** | 240.5 | 478.9 |
| sgm+1 wall, instances all three solved | 8.51 s (40) | 7.26 s (51) | **6.23 s** (53) | 0.20 s | 2.44 s |
| sgm+1 `.pbp`, same set | 3.5 MB | 8.5 MB | 9.9 MB | — | 40.0 MB |
| sgm+1 check, same set (n verified) | 0.88 s (40) | 2.33 s (50) | 2.44 s (51) | — | 7.45 s (43) |

Agreement: **133 AGREE, 0 DISAGREE**, 0 mismatches against the pinned answers. Pairwise on
instances both solved: baguette/Chuffed n=92, sgm+1 **9.38 s vs 0.48 s**; baguette/GCS n=53,
**6.23 s vs 2.44 s**. Week over week on the 83 instances both of today's binaries solved:
sgm+1 **8.94 s → 6.45 s**.

### What it says

1. **Correctness held through seven speed changes**: 0 rejected over 265 + 92 checked proofs,
   0 disagreements, and every change was byte-identical on the suite except M2-T6 (not yet
   merged) by design.
2. **Coverage**: 60 → 92 in the comparison, 58 → 87 verified on the corpus, plus 25 solved
   instances whose proofs the checker cannot finish in 900 s — the **check column is now the
   bottleneck the solve column used to be**: 25 solved-but-unchecked against 12 before, and
   `.pbp` sizes on the common set grew (3.5 → 9.9 MB sgm+1) as the solver reaches deeper
   searches. M4-T5's RUP hints (O(hints) checking) are the row this names; until then a
   `CHECK_TIMEOUT` of 900 s under-reports what was solved.
3. **Speed**: PAR2 within 1 % of GCS-with-proofs; 2.6× GCS and 47× Chuffed in sgm+1 on the
   common set (pairwise 20× Chuffed). The stopped runs' median nodes/s went 1.44 → 9.6 → 18.1
   across the week. The profile is flat (D-0092); what remains is design-level: M2-T6's wake
   discipline (727 vs 103 propagator runs per node against GCS, measured on
   `2014_stochastic-fjsp…det`), watched slack for `Pb.propagate` (D-0085), a priority structure
   for the un-annotated `first_fail` (D-0087).
4. **The width wall** is 69 instances and untouched; `connect` is the one remaining front-end
   refusal.
## D-0095  M4-T9: `array_int_maximum` / `array_int_minimum` as a propagator over one clause row per threshold

**Date.** 2026-10-02. **Row.** M4-T9 (agent-maxmin, `wave38-maxmin`). **Census.** 94 of 436
MiniZinc Challenge models name `maximum`/`minimum`; every one was decomposed into reified rows.

**The split.** `m = max_i x_i` is `(/\_i m >= x_i) /\ m <= max_i x_i`, and the two halves are
posted differently.

- The **conjunctive** half is `n` ordinary `int_lin_le` rows `x_i - m <= 0`, one `Linear`
  instance each. These ARE the model rows. They carry two rules with `Linear`'s `pol` and nothing
  new: **R1** `lo(m) >= lo(x_i)` and **R2** `hi(x_i) <= hi(m)`.
- The **disjunctive** half, `m <= max_i x_i`, is one new instance (`lib/core/prop/maxmin.ml`,
  name `array_int_maximum` / `array_int_minimum`) with two rules and a conflict:
  - **R3** `hi(m) <= H` where `H = max_i hi(x_i)`;
  - **R4** `lo(x_j) >= lo(m)` when `j` is the only position with `hi(x_j) >= lo(m)`;
  - **conflict** when `H < lo(m)`.

**What the `.opb` holds for the disjunction.** One clause per threshold `v`:

    C_v :  ~[m >= v] \/ [x_1 >= v] \/ ... \/ [x_n >= v]

Over all `v` this is exactly `m <= max x` in the order encoding. Literals the declared bounds
settle are folded. A constant-false literal is dropped. A constant-true one makes the clause
vacuous, and a vacuous clause is not posted. So the posted thresholds are
`v in [max(dlo m, Lx + 1), min(dhi m, max(Hx + 1, dlo m))]`, where `Lx`/`Hx` are the largest
declared lower/upper bound of any `x`. Below `Lx + 1`, some `x` is `>= v` by declaration. Above
`dhi m`, the antecedent is false. Above `Hx + 1`, the clause is the unit `~[m >= v]`, and the
ladder already gets that from `C_(Hx+1)`. When `dlo m > Hx`, the single row is the empty clause.

**Justification: every Maxmin explanation is one posted row, restated.**

- R3 cites `C_(H+1)`. Its facts are `x_i <= H`, and it claims `m <= H`.
- R4 cites `C_(lo m)`. Its facts are `m >= lo m` and `x_i <= lo m - 1` for `i <> j`, and it
  claims `x_j >= lo m`.
- The conflict cites `C_v` at `v = max(H + 1, dlo m)`.

Each such `v` lies in the posted range. The proof: R3 has `lo(m) <= H < hi(m)`, so
`dlo m < v <= dhi m`, `v >= Lx + 1` because `H >= every lo(x)`, and `v <= Hx + 1`. R4 has every
`x` either unable to reach `lo m` or below it on `lo`, so `Lx < lo m <= Hx`. The conflict has
`H >= Lx` and `v <= lo(m)`. `Maxmin.expl_at` raises rather than render a threshold outside the
range. Each fact is the negation of one literal of the clause, so the trace line and the clause
agree literal for literal. That is D-0026's check: clean under `BAGUETTE_DEBUG=1`, asserted on
hand-built stores in test_prop.ml. The explanation is `Explanation.clause C_v`, the `clause.ml`
(M2-L12) shape. **No new `Explanation` constructor, no row id, nothing `Deferred`.** The clause
for each threshold is built once at `make` and shared, so Justify's memo on physical identity
fires. I-X10: **Single_row**, classified in test_trace.ml's closure gate.

**The worked derivation of the `hi(m)` clause, against the checker.** The scene is `m, a, b in
0..5`, the posted rows of `m = max(a, b)`, and the units `a <= 2`, `b <= 3`. It is
SATISFIABLE (m = 3), so a RUP line here is not vacuous (D-0053, D-0066).

1. R3 says `hi(m) <= 3`. The line `rup +1 ~m_ge_4 >= 1` is ACCEPTED. Negating it gives `m >= 4`.
   `C_4` then needs `a_ge_4 \/ b_ge_4`, and the two units falsify both, so the clause propagation
   is the whole derivation.
2. One unit stronger, `rup +1 ~m_ge_3 >= 1`, is REFUSED with the checker's RUP judgement in full
   ("The constraint is not implied by reverse unit propagation (RUP) from core and derived
   database.").
3. The honest line from (1) against an `.opb` holding only the two linear rows is REFUSED with the
   same judgement. Neither `m >= x_i` nor the ladder gives `hi(m)`. **The per-value rows are the
   derivation.**

These are three lanes in test_prop.ml (`test_maxmin_veripb`).

**Why per value and not a selector per position.** The alternative is `b_i -> m <= x_i` (big-M)
plus `\/_i b_i`, which is the shape of `int_lin_ne`'s `_neN` selector. It was not taken:

- it needs `n` auxiliary 0-1 variables, which the solver must search on or keep in step;
- each big-M row expands both `m` and `x_i` over their whole ladders, so it is not smaller;
- its prunings are RUP only through two rows and the ladder, where here every one is a single row.

**Minimum is the same propagator over negated views (D-0058).** `m = min x <=> -m = max(-x)`.
`make ~dir:Min` negates every view, and from then on there is one code path. A negated view's
`>= v` literal IS the base's `<= -v` literal, so a minimum's rows are `C_v` in the mirror over the
bases' own literals, and no second encoding exists. A constant operand is a `View.Const` whose
literals all fold. `int_max(x, y, z)` / `int_min(x, y, z)` are accepted by the front end as the
array form over `[x, y]`. They write a byte-identical `.opb` (test_compile.ml).

**Consistency: BOUNDS, for the instance's own relation `m <= max x`.** For that relation R3 and R4
are bounds(Z). The evidence:

- a brute force over all 2000 sub-boxes of `m, a, b in 0..3`, both directions, checking I-P1,
  I-P2, I-P3 and support of every bound;
- `BAGUETTE_CONSISTENCY=1` over the four model lanes audits `array_int_maximum`/`_minimum` at
  `bounds` 20 times with no violation.

The engine fixpoint with R1/R2 is the textbook bounds rule set for max.

**MiniZinc.** std has no `fzn_array_int_maximum`. `maximum`, `minimum`, `max(array)` and
`min(array)` lower to `array_int_maximum`/`array_int_minimum`, and std's
`redefinitions-2.0.mzn` is what gives those two a body (a chain of `int_max` auxiliaries). So
`mznlib/redefinitions-2.0.mzn` SHADOWS it. It declares both bodyless and keeps the rest of std's
file verbatim (`bool_clause_reif` and the float forms). `redefinitions.mzn`'s `int_max`/`int_min`
become `array_int_maximum(z, [x, y])`. The orchestrator's brief named
`mznlib/fzn_array_int_maximum.mzn`. **That file would be dead, and it was not written.**
`check_mznlib.sh` on fataepyc-07 (MiniZinc 2.10.1) reports **10 ok, 0 failed**. Three new sources
carry `MUST-EMIT: array_int_maximum`/`_minimum`, `MUST-NOT-EMIT: int_eq_reif` and `SOLVES-AS`.

**D-0083 inference.** Keeping the constraint whole removed the rows that used to bound an
undomained result. `2010_filters_filter`'s objective is `var int` and was REFUSED at first. The
builder now infers from the `m >= x_i` linear facts, plus `F_hull`: `m <= max hi(x)` once every
`x` has an upper bound, mirrored for min. docs/SPEC.md 2.1's list of bound-carrying builtins
needs `array_int_maximum`/`_minimum` and `int_max`/`int_min` added, and that is filed as a
request.

**Measured on the corpus** (fataepyc-07, `--time-limit 120 --stats --proof`,
`ulimit -v 32000000`, veripb 3.0.2). `main` is `/scratch/arthur/baguette/_build/default/bin/main.exe`
at `5c299cb`, sha256 `2bbdd45a…`, flattened with main's mznlib. Mine is `cd6d47e`, sha256
`4ea426bb…`.

| instance | max/min calls (mine) | main: nodes, wall, .pbp | mine: nodes, wall, .pbp | outcome, both | veripb, both |
|---|---|---|---|---|---|
| 2008_radiation | 160 | 888, 13.8 s, 37.1 MB | 775, 7.9 s, 25.9 MB | optimum 370 | VERIFIED BOUNDS 370 |
| 2009_open_stacks_01 | 1 | 2211, 20.9 s, 44.9 MB | 2281, 18.8 s, 43.2 MB | optimum 9 | VERIFIED BOUNDS 9 |
| 2010_filters_filter | 1 | 1247, 2.0 s, 3.76 MB | 1247, 2.0 s, 3.79 MB | optimum 15 | VERIFIED BOUNDS 15 |
| 2010_depot_placement | 1 | 5338, 120 s limit, 202 MB | 5308, 120 s limit, 200 MB | incumbent 106 at the limit, 10 solutions | VERIFIED NO CONCLUSION |

On radiation, the flattened model goes from 1028 constraints to 388. Its `.opb` goes from 13539
rows to 23939, because the per-value clauses are many and short, but it is 0.7 % smaller in
bytes. filters is node-identical, and depot is within 1 % on nodes: main already flattened its one `maximum` without reified
equalities. **Not measured:** the width cost of `C_v` on a wide `m`. The rows are at most
`dhi m - dlo m + 1` clauses of width `n + 1`, which is the same order as `m`'s own ladder
(D-0028), but no corpus instance here exercises a wide one.

**PROOF-FORMAT section 4 gets one sentence:** `m >= x_i` is `n` `int_lin_le` rows; the
disjunction is one `.opb` clause per threshold, `~[m >= v] \/ [x_1 >= v] \/ ... \/ [x_n >= v]`,
and every pruning of the `maxmin` instance is `rup` of exactly one of them, restated.

**What would reverse this.** A corpus instance with a wide `m`, where the `C_v` family costs
more than the selector encoding's `2n` big-M rows, would reverse it. Then the comparison above
would have to be measured rather than argued.
## D-0094  M2-T6: propagation counters under `--stats`, and the self-wake veto with its two guards

**Date.** 2026-10-02. **Row.** M2-T6, reopened (agent-wake, `wave38-wake`). Commits `1dd1724`
(counters), `262c8db` (veto, aliased-scope rule, claim re-checker), `621c350` (`vetoed`/`seeded`).

**The counters, defined so that they compare with GCS's `-s` output.** Per engine
(`Engine.counters`, created with the engine, and a solve builds one engine in `Compile.compile`),
counted by the fixpoint loop in `Engine.propagate` and never read from the proof (M1-T36's rule):

- `props`: propagator runs taken off the queue. This is GCS `propagations`.
- `eff`: runs that returned `Fixpoint` and grew the trail, i.e. changed at least one domain. This
  is GCS `effectfulPropagations`.
- `contra`: runs that returned `Conflict`. This is GCS `contradictingPropagations`. A run that
  pruned and then failed counts here and not in `eff`, so the two are disjoint and
  `props - eff - contra` is the runs that did nothing.
- `wakes` and `masked` are the M2-T5 pair, now per engine. `vetoed` counts self-wakes the veto
  dropped. It counts per trail ENTRY, so it is an upper bound on the runs saved, because the
  queue dedupes. `seeded` counts the runs that `propagate`'s every-instance seeding enqueued.

The re-run audits (`check_fixpoint`, `check_claim`, the M2-T10 oracle) are not counted, so a
`BAGUETTE_DEBUG` run reports the same figures as a plain one. Under `--stats` each counter is a
`stats:` line. `props=`, `eff=` and `contra=` are on both `limit:` lines (`report_limit` and the
SIGTERM handler), and `scripts/corpus_run.sh`'s `limit_detail` appends them to the detail column
when the run printed them.

**Baseline** (node fataepyc-07, `/scratch/arthur/tmp-guess/s4.fzn` = 2014_stochastic-fjsp…det,
OLD = `1dd1724`). On `2014_stochastic-fjsp…det` the baseline was 129 403 runs over 178 nodes,
**727.0 runs/node**, of which 4 464 were effectful (25.1/node, **3.4 %**) and 47 contradicting.
GCS on the same instance did 308.6 M runs over 3.0 M nodes, 103/node, with 22 % effectful. Per
node, baguette does 7x GCS's runs, and 97 % of those runs change nothing.

**The discipline.** It copies GCS's two guards and not its claim/replay engine.

1. *Self-wake veto.* `Propagator.instance` has a new field `inst_idempotent`, which claims that
   one call reaches the instance's own fixpoint. When that claim is honoured, `Engine.propagate`
   passes `~self:id` to `watchers_of_new_entries`, and the running instance's own id is dropped
   from the wake lists of the entries it just pushed. Dropping it gives a subsequence of the old
   list and never a reordering. `pack ?idempotent` defaults to `Propagator.claims_idempotence`.
   That is a table by packed name holding **`int_lin_le`, `int_le` and `int_lt` only**, and
   `linear.ml:22-29` is its argument. The arithmetic rows are `Linear.t` too, but they share their
   names with the arithmetic guard faces, which are reifications, so they are left unclaimed.
   `Pb` rows run over literals that can be rungs of one ladder, so they alias by construction and
   are unclaimed. Every other family is unclaimed as well.
2. *Aliased-scope rule.* A claim is honoured (`Engine.honours_claim`) only if `inst_vars` names no
   variable twice. The rule is decided per instance when the instance is registered (`create` and
   `add`), and `Compile`'s merging of duplicate terms is not assumed. The idempotence argument is
   over distinct variables. With x in two terms of opposite sign, moving x through one term moves
   the other term's minimum. `test_engine`'s `2x - x <= 2` scene shows it: honoured, it stops at
   x <= 3, and refused, it reaches x <= 2.
3. *Claim re-checker.* This shipped in the same commit as the veto, which is GCS #889's lesson.
   Under `BAGUETTE_DEBUG`, when an honoured instance has just pruned and its self-wake is about to
   be skipped, `Engine.check_claim` runs it once more at that point. If the re-run prunes or
   fails, it raises `Not_at_fixpoint` and names the instance. `check_fixpoint` at the end of the
   loop catches most wrong claims too. It cannot catch one whose loss a later, unrelated wake
   happens to cover up. A re-run that prunes nothing writes nothing, so a debug run answers and
   proves byte-identically. Tests: a deliberately wrong claim (`Step_down`) is caught both by
   `check_claim` and inside `propagate` under debug, and its unclaimed control settles.

**Before and after** (fataepyc-07, two runs each, `--time-limit 55 --stats --proof`,
`ulimit -v 32000000`; OLD `1dd1724` md5 `08d33b1f…`, NEW `621c350` md5 `2db35c28…`. OLD is
main plus the counters, and it is byte-identical to main on all 396 suite artefacts per
`bench/m6t11/byte_identity.sh`. main itself cannot report the counters.)

| instance | runs/node OLD → NEW | effectful/node OLD → NEW | nodes in 55 s OLD → NEW |
|---|---|---|---|
| 2014_stochastic-fjsp (s4, solves in 0.5 s) | 727.0 → 742.6 | 25.1 → 27.3 | 178 → 178 (complete) |
| 2014_mario | 2082.0, 2085.2 → 2076.9, 2077.2 | 33.7 → 33.8 | 3584, 3602 → 3539, 3547 |
| 2023_chessboard | 6455.4, 6451.1 → 6476.5, 6463.8 | 137.4 → 138.3 | 3290, 3278 → 3283, 3256 |

The answers are the same on all six pairs: stdout is byte-identical, s4 reaches optimum 242,
and the incumbents at the stop are 0 and 41. veripb 3.0.2 on every NEW proof: s4
`VERIFIED BOUNDS 242 <= obj <= 242`, both runs; chessboard `VERIFIED NO CONCLUSION`, both runs (22 s,
100 MB); mario `VERIFIED NO CONCLUSION`, both runs (745 s and 767 s, 210 MB).

**The veto does not pay at our scale, and the measurement says why.** Of NEW's runs, **`seeded` is
84.5 % on s4, 75.8 % on mario and 78.6 % on chessboard**: 628, 1 575 and 5 090 seeded runs per node,
against 16.6, 4.2 and 3.2 vetoed wake entries per node. `propagate` enqueues **every** instance on
every call, and `Search` calls it once per node. A veto can save at most one run per effectful
run of a claimant, and effectful runs are 2–4 % of the total. That is GCS-COMPARISON §1.3's
caveat, measured here. On s4 the veto even costs 2 % more runs and 9 % more effectful runs,
because of the queue's dedupe. Before the veto, a claimant re-woken by itself was already in the
queue when a second propagator woke it, so it kept its early place and absorbed both changes in
one run. With the veto it is enqueued at the back, after other runs, and its pruning lands in a
different interleaving. The fixpoint is the same and the order is not. On mario and chessboard
the change is within the run-to-run noise. The veto stays in, because it makes the API honest
(the claim is stated, checked and counted) and because GCS-COMPARISON §1.3 calls it the
prerequisite for the rest. It is not a speed-up.

**The lever is the seeding.** It is not this row's veto. A propagate that seeds only the watchers
of the trail entries since the last fixpoint, plus instances added since then, would remove the
75–85 %. That needs `Store` to report the trail's low-water mark since the engine last looked,
because after a backjump the engine sees a short trail and cannot tell where the restore point
was. `store.ml` is not this row's file. It also needs every input a propagator reads to be on the
trail. That holds for domains. It has to be checked for any propagator that keeps mutable
internal state, such as an objective bound. The I-P2 re-run under `BAGUETTE_DEBUG` is the
instrument that would catch a miss. This is filed as a cross-session request and proposed as a
new row.

**Suite verdict** (`bench/m2t6/identity.sh main NEW` over 132 models): **stdout byte-identical
on all 132**, `.opb` identical on all 132, **1 proof changed**, and **all 132 NEW proofs verify**.
The changed proof is `root_nested_defining_gcc_unsat`, 18 → 20 lines. A different propagator
reports the root conflict first, so the refutation is a `rup` pair plus a `pol` in place of one
`pol`. It ends in `s VERIFIED UNSATISFIABLE`. The search order is unchanged (SPEC §3.4): the
domains at each fixpoint are the same, so branching is the same, and no SAT model's first
solution moved. The model suite is 132/132, both plain and under `BAGUETTE_DEBUG=1`, so the
claim re-checker ran on every honoured claim in the suite and never fired. The unit suite under
`BAGUETTE_DEBUG=1` has 0 FAIL.

**Left open.** There are two items. (a) The name table should become `~idempotent:true` at
`Compile.pack_linear` and `pack_arith_row`, the latter honest only for the row faces. This is a
cross-session request, because `compile.ml` is not this row's file. (b) The incremental seeding
above.
