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
Status: OPEN — M4
Date: 2026-09-14

Context: Hall-interval pruning for bounds-consistent `all_different` has a known
cutting-planes justification; domain-consistent (Régin/matching-based) pruning does not
have an obvious cheap one.

Decision: pending. M4-T1 does bounds consistency first precisely so that M4-T2 can be
evaluated against a working baseline.

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
Status: DECIDED
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
Status: DECIDED
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
Status: DECIDED
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
