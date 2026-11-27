# Glossary

Words this project uses in a specific way. CP and proof-logging vocabulary overlap
badly — "constraint", "reason", "explanation" and "clause" all mean different things on
either side of the fence, and sessions drift apart when they are used loosely.

---

**1UIP** (first unique implication point) — the cut of the implication graph that
conflict analysis takes: the learned clause keeps exactly one literal of the conflict's
decision level. `lib/core/learn.ml` computes it over order literals.

**Asserting level** — the second-highest decision level among a learned clause's literals.
Going back there leaves the clause with one unassigned literal, which it then propagates.
Only the CDCL loop (`--cdcl`, D-0219) backjumps to it; the default depth-first search does not.

**Assignment** — a map from variables to single values. *Total* if every variable is
fixed.

**Big-M row** — a linear row made conditional on a Boolean by a large coefficient on it:
`M*b + sum a_i x_i >= c` holds trivially when `b` is 1 and is the row itself when `b` is 0
(or the reverse, with the literal negated). The reified rows of `reif_lin_le.ml` and the
selector rows of max/min over bits are written this way.

**Bits encoding** — Booleans `x_bit_i` meaning "bit i of `x - lo` is set", for wide
domains (`--bits-above W`, D-0130, D-0132). A bits variable has no `x_ge_v` in the `.opb`.
The default since D-0201 is `--bits-above 0`, so every eligible integer variable is on bits.

**Bounds consistent** — a propagator that guarantees `lo` and `hi` of each variable can be
extended to a solution of that constraint, saying nothing about interior values.

**Checking** — the weakest consistency level a propagator may declare
(`Propagator.Checking`): it promises only what `docs/SPEC.md` §3.2 asks of every
propagator, that with all its variables fixed it fails if and only if the assignment
violates its constraint. It may prune more, and usually does, but claims nothing about
what it leaves. `cumulative`, `gcc`, `inverse`, `circuit`, `member` and `table` declare it.

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

**Epoch** — a wipe count stored with a written proof line (`Explanation.line`), so that
`Justify` can tell whether the line is still on the page: a line written before a wipe
that deleted it has an older epoch and is written again instead of being cited.

**Explanation** — *this project's* term for the reason attached to a pruning or a failure,
in a form the proof layer can render. It is a value of `Explanation.t`. Distinguish from:

**Fact** (bound fact) — one statement `x >= v` or `x <= v` about a variable's current
domain, a `Reason.fact`. A pruning's reason is the list of facts it read, and its proof line
says "these facts imply the new bound" (D-0018, D-0026).

**Hash-consing** — building each distinct `Explanation.t` value once and sharing it, so that
a sub-derivation two prunings share is written to the proof once and cited by id
afterwards. On by default; `BAGUETTE_HASHCONS=0` turns it off for comparison.

**Higher-order explanation** — the project's name for an explanation that is a
cutting-planes expression over model rows and facts (a `pol` derivation), not only a clause
of literals. D-0003 left the phrase open; D-0026 settled it in that sense: reasons are
declarative data, justifications are cutting planes.

**Justification** — the concrete proof step(s) an explanation renders to. Explanations are
solver-side; justifications are proof-side. `lib/core/justify.ml` is the boundary (it lives in `core`, not `proof`: the dependency direction is `core -> proof`, so `proof` cannot see `Explanation`).

**Ladder** — the chain of order-encoding rows `x_ge_(v+1) -> x_ge_v` that makes the order
literals of one variable consistent with each other. `lib/core/ladder.ml` lifts a linear
reason onto the rungs that carry its strength (D-0028, D-0010).

**LBD** (literal block distance) — the number of distinct decision levels among a learned
clause's literals. Glucose's measure of a clause's usefulness; the `lbd` and `tiered`
retention policies and the Glucose restart policy read it.

**Learned constraint** — a PB inequality derived by conflict analysis and added to the
database, of which a learned clause is the degree-1 case (`lib/core/learned.ml`, D-0044).

**Level 0** (root level) — the decision level before any decision. What holds there holds
in every branch, so a fact at level 0 needs no decision in its reason.

**Model row** — a proof constraint of the `.opb`, written by `lib/flatzinc/compile.ml` for
a model constraint. An explanation cites it by id (`Explanation.Model_row`). Contrast with
a derived line of the `.pbp`.

**Needs derivation** — a propagator family whose prunings are not RUP against the `.opb`
alone, because they rest on a counting argument over several rows: `alldiff`, `gcc`, `cumulative`,
`member` and `circuit`, per `test/unit/test_trace.ml`'s I-X10 table. Such a pruning is made under
`Store.deriving_ahead`, and its `pol` derivation is written ahead of its trace line so that
the line becomes RUP (I-X10, D-0040, D-0082).

**Nogood** — an assignment fragment known to extend to no solution. Learned from
conflicts. A clause over encoding literals.

**OPB** — the pseudo-Boolean model file format that VeriPB reads alongside a proof.

**Order encoding** — Booleans `x_ge_v` meaning `x >= v`. The default here because bound
prunings become single literals.

**pol** — VeriPB's cutting-planes rule, reverse Polish over proof-constraint ids.

**Propagator** — code that removes values from domains given one model constraint.
"Propagation" is running them to fixpoint.

**Pruning** — removing values from a domain. Every pruning carries an explanation (I-P4).

**Reason** — since D-0026, a distinct value from the explanation: `Reason.t`
(`lib/core/reason.ml`) says WHICH facts justify a pruning, and `Explanation.t` says HOW the
checker is convinced that they do. A mutator takes both, as one `Reason.justified`.

**Red** — VeriPB's redundance-based strengthening rule, which adds a constraint with a
witness substitution. It is vacuous over a contradictory database (CLAUDE.md, "Proof
discipline"), so it is tested on satisfiable models only.

**Retention** — the policy that decides which learned constraints stay in the database and
which are evicted (`lib/core/retention.ml`). `tiered` is the default since D-0226;
`BAGUETTE_RETENTION` selects `keep_all`, `fifo:N`, `lbd:N` or `tiered`.

**Root lemma** — a constraint derived at the start of the proof from the model rows alone
and kept to the end, so that later trace lines can rely on it by unit propagation
(`Encoding.add_root_lemma`). A *cited* lemma (`Encoding.add_cited_lemma`) is one a `pol`
derivation names by id.

**RUP** (reverse unit propagation) — a proof step checked by propagating the negation to
contradiction. Cheaper to emit, more expensive to check than `pol`.

**Selector** — a Boolean store variable standing for one alternative of a disjunction:
one per position in `member`, one per tuple in `table`, one per operand of a max/min over
bits. Its rows say "if the selector is true, this alternative holds".

**Slack** — for a linear row `sum a_i x_i <= c`, the distance `c - sum min(a_i x_i)`
between the bound and the smallest value the left side can take. A term whose own range
exceeds the slack can be pruned; a negative slack is a conflict.

**Trail** — the undo log making domain mutation backtrackable.

**Trace** *(D-0018)* — the sequence of per-pruning proof lines a failing branch writes
before its nogood, each stating "these bound facts imply that bound". Every line is
globally valid and mentions no decision; what the decisions do is make the nogood over
them RUP *along* the trace. Not a synonym for **Trail**: the trail is solver-side undo
state, the trace is what gets written into the proof from it.

**View** — an affine image `+-x + k` of a store variable, or a constant, used where a
propagator needs `x + 1` or `-x` without an auxiliary variable (`lib/core/view.ml`,
D-0058). A view has no domain, trail slot or PB variable of its own.

**Value consistent** — a propagator that only ever removes values it can name, without
claiming anything about the values it leaves behind. Weaker than **Domain consistent**,
which additionally guarantees every remaining value extends to a solution. `int_ne`
declares this level (M1-T9) although its algorithm happens to achieve domain consistency
for a disequality — declaring the weaker level is deliberate, since `Propagator.consistency`
is a promise the proof layer is entitled to rely on.

**Wipe** — deleting every proof line tagged with decision level `L` or deeper, once per
backtrack (D-0008). VeriPB 2.0 had a `w L` command for it; 3.0 has none, so
`Writer.wipe_level` keeps the level tags itself and writes the deletions (D-0024).
