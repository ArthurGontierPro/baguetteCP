# The VeriPB contract

Everything `baguette` emits and the vocabulary it is allowed to use.

Emitted proof format: **3.0** by default (M1-T19), **2.0** under
`BAGUETTE_PROOF_FORMAT=2.0`. 3.0 is what this project emits and what its checker of
record speaks (D-0023); **section 2a is the live contract** and section 2 documents the
2.0 grammar, which is still emitted on request and still fully tested. They are separate
grammars, not options on one — a 2.0 proof is a syntax error to a 3.0 reader and a 3.0
proof is refused outright by veripb 2.2.2.

The whole suite is green under both: 925 unit checks either way, and the model tests
pass under each. That is the property that makes the fallback meaningful rather than
decorative — a 2.0 escape hatch nothing exercises would rot inside a week.

---

## 1. Files, and which checker checks them

```
PREFIX.opb     the model, in OPB format
PREFIX.pbp     the proof
```

Verified with `veripb PREFIX.opb PREFIX.pbp`. `scripts/verify_proof.sh` wraps this and
is what the test suite calls.

**Which `veripb`** is decided in exactly two places, which must agree:
`scripts/checker.sh` (shell) and `lib/proof/checker.ml` (OCaml). Run
`scripts/checker.sh` to print the one that would be used, and its version. The order is

1. `$VERIPB`, if set. An explicit choice wins and a broken one is an **error**, never a
   silent fall-through to a different checker.
2. `~/.cargo/bin/veripb` — VeriPB **3.0.2**, the Rust implementation. The checker of
   record; see D-0023.
3. `~/.local/bin/veripb` — VeriPB 2.2.2, the Python implementation. Fallback.
4. `veripb` on `$PATH`.

`$PATH` is last deliberately. Both builds are installed on the development machine and
`~/.local/bin` comes first on `$PATH`, so "whatever is on `$PATH`" silently meant 2.2.2.

**No checker is a failure, not a skip.** `verify_proof.sh` used to `echo SKIP; exit 0`
when it could not find `veripb`, so a machine with no checker made every proof test
pass — the one outcome a suite built on "a test that does not check the proof is half a
test" must never produce. Every entry point now fails loudly. There is no
`BAGUETTE_SKIP_PROOFS` escape hatch and none should be added.

The proof's first line MUST be exactly one of, and is the first by default:

```
pseudo-Boolean proof version 3.0
pseudo-Boolean proof version 2.0
```

and the rest of the file must be in that format throughout. The `.opb` is part of the
choice too: 3.0 labels its rows (section 2a) and 2.0 cannot. `Encoding.write_opb_for`
takes the writer and so cannot get the two out of step; `write_opb` alone can.

## 2. Rule vocabulary, 2.0

These are the VeriPB 2.0 rules this project uses. Anything outside this list needs a
decision record before it appears in emitted proofs — an unfamiliar rule in a proof is a
debugging problem for whoever reads the failure next.

Every row below was checked empirically against veripb 2.2.2. Where this document once
disagreed with the checker, the checker won; see the traps at the end of this section,
because two of those errors silently corrupt a proof rather than failing it.

| Rule | Syntax | Meaning | Used for |
|---|---|---|---|
| `f` | `f N` | load N model constraints, numbering them 1..N | proof preamble |
| `pol` (`p`) | `pol <rpn>` | cutting-planes derivation in reverse Polish | the workhorse: most propagator justifications |
| `rup` (`u`) | `rup <terms> >= <n> ;` | reverse unit propagation | prunings whose reason is clausal |
| `red` | `red <constraint> ; <witness>` | redundance-based strengthening | definitions: reified vars, direct-encoding channelling |
| `del` (`d`) | `del id N M ...` | delete constraints by id | retiring an individual reason |
| `#` | `# <level>` | **set the current level** | opening a decision level |
| `w` | `w <level>` | wipe every constraint at or above that level | backtracking — see section 5 |
| `core` | `core id N ...` | move constraints to core | after a solution improves the bound |
| `sol` | `sol <lits>` | log a solution, adding nothing | SAT answers |
| `solx` (`v`) | `solx <lits>` | log a solution *and* add the excluding clause | enumeration; **yields an id** |
| `soli` (`o`) | `soli <lits>` | log an improving solution; needs an objective | optimisation; **yields an id** |
| `obju` | `obju ...` | update the objective | optimisation |
| `output` | `output NONE` | declare the output mode | **mandatory**, immediately before `conclusion` |
| `conclusion` | see SPEC section 4.3 | final claim | every proof ends with one |
| `end` | `end pseudo-Boolean proof` | end of proof | last line, exact text |
| `a` | | add a constraint assumed-checked | **forbidden in release builds** — debugging only |
| `*` | `* text` | comment | readability of emitted proofs |

`pol` syntax is reverse Polish over constraint ids: `pol 3 4 + 2 d` means "constraint 3
plus constraint 4, divided by 2". Literal axioms are written `~x1` / `x1`. Its weakening
operator `w` takes a **variable, not a literal** — it ignores any sign you give it, and
VeriPB only logs a warning rather than failing, so a sign there is a silent no-op.

The three operators, as checked against veripb 2.2.2 rather than assumed:

| Op | Effect |
|---|---|
| `w <var>` | drops the variable's term and subtracts its coefficient from the right-hand side, **clamped at 0**. Exactly equivalent to adding `|a|` copies of that literal's axiom, which is how D-0013's derivation was first written |
| `s` | saturation: caps every coefficient at the current right-hand side, per literal; the right-hand side is unchanged |
| `d N` | divides **every coefficient and the right-hand side**, rounding each **up** |

The division row is the one to read twice: this document previously said `d` rounds only
the right-hand side. It rounds the coefficients too, by the same ceiling. Checked: from
`+3 x1 +1 x2 >= 1`, `2 d` gives `+2 x1 +1 x2 >= 1` — under truncation it would have given
`+1 x1 >= 1`, forcing `x1`, and a `rup` of `x1` after the division is rejected, which is
what settles it.

**Rule**: prefer `pol` over `rup`. A `pol` step states the actual reasoning and is cheap
to check; `rup` makes the checker search. A propagator that can only produce `rup` should
say so in its module header and explain why.

### Traps

Five things this document previously got wrong. The first two are the dangerous ones,
because they corrupt ids rather than producing an error you would notice:

1. **An `.opb` line with `=` counts as TWO constraints** for the `f` rule — the checker
   splits it into `>=` and `<=`. Get the count wrong and every later id is shifted, so
   `pol` steps silently reference the wrong constraints. `Opb.n_checker_constraints`
   computes the header count the checker's way; `Encoding.add_constraint` refuses `Eq`
   outright and `Encoding.add_equality` emits the two `>=` lines explicitly, returning
   both ids. **Closed in 3.0**, where citations are labels rather than numbers — see
   section 2a. Note that the `f` count itself was never the silent part: both checkers
   reject a wrong one and name the right number. What was silent was a `pol` citing a
   real but wrong constraint after our own counter had drifted.
2. **`sol`, `solx`/`v` and `soli`/`o` differ in id accounting**: `sol` adds no constraint,
   the other two each add one. Treating them as interchangeable desynchronises our id
   counter from the checker's.
3. **`#` is not a comment or section marker.** It is the set-level rule and takes an
   integer; `#` followed by prose is a parse error. Only `*` introduces a comment.
4. **Deletion takes an identifier kind**: `del id N`, not `del N`. Same for `delc` and
   `core` (`id` / `range` / `find` / `spec`).
5. **`conclusion SAT : <assignment>` is not propagated by every checker.** 2.2.2 unit-
   propagates the inline assignment and fills in encoding auxiliaries (the `_neN`
   selectors of section 3) that the solver has no value for; 3.0.2 does not, and reads
   an unmentioned variable as false. `ne_conflict_sat.fzn` needs a selector *true*, so
   its honest proof was rejected by 3.0.2 and accepted by 2.2.2 — the single
   disagreement between the two checkers over this project's proofs (M1-T18). Log the
   assignment with `sol` and conclude with the bare `conclusion SAT`: a *logged*
   solution is propagated by both. `Writer.conclusion` does this for `Sat`. `solx` is
   not an alternative — 3.0.2 refuses it outside a preserved set.

## 2a. The 3.0 rule vocabulary *(D-0023)*

3.0 is **not** a dialect of 2.0. Flipping the version line alone makes every proof in
this project a syntax error. Every row was run against 3.0.2; where a row says
something is refused, the checker's own words are quoted.

`BAGUETTE_PROOF_FORMAT` switches emission, and **the default is 3.0** — D-0025 moved it,
and `Writer.format_from_env` returns `V3_0` for an unset or empty variable. Set
`BAGUETTE_PROOF_FORMAT=2.0` to get the older dialect, which is still emitted and still
checked (by the Python VeriPB 2.2.2; see section 1). D-0023's "what is NOT done" describes
the state *before* that move and its count of 2.0-pinning test files no longer holds: as of
2026-09-17 only `test_proof.ml` (two `V2_0` sites) and `test_random.ml` name the format at
all, and they name it explicitly rather than relying on a default.

| Rule | 2.0 | 3.0 | Note |
|---|---|---|---|
| version | `pseudo-Boolean proof version 2.0` | `... version 3.0` | 2.2.2 rejects a 3.0 proof outright ("Unsupported version") |
| load | `f N` | `f N ;` | the count is still required, and a wrong one is still a hard error in **both** |
| comment | `* text` | `% text` | `*` is refused: "Expected a top level rule name" |
| cutting planes | `pol <rpn>` | `pol <rpn> ;` | operands may be labels |
| RUP | `rup <c> ;` | `rup <c> ;` | unchanged: the constraint already carries the terminator, and a second `;` is an error |
| **implies / assert** | `ia <c> ; <id>` | `ia <c> : @hint ;` | **Was missing from this table until M1-T51 and is present in BOTH checkers.** Asks whether `<c>` is *syntactically implied* by the one constraint at the hint — no propagation, no search. Yields an id. See the trap below |
| **equals** | `e <c> ; <id>` | `e <c> : @hint ;` | same shape; asks for syntactic *equality* rather than implication. Rejections: 3.0.2 "Expected constraint is not equal to the constraint at the hint.", unhinted "Constraint not found in database." |
| redundance | `red <c> ; <witness>` | `red <c> : <witness> ;` | the witness moves **before** the terminator. After a `;` it is silently not a witness |
| delete | `del id N M` | `del id N M ;` | also `del range LO HI ;`, **half-open: `[LO, HI)`, so `HI` survives** (measured against 3.0.2, M1-T22); tolerant of an already-deleted id and of a reversed range |
| delete from core | `delc id N` | `delc N ;` | `delc` loses its `id`; `del` and `core` keep theirs |
| core | `core id N` | `core id N ;` | |
| set level | `# l` | **gone** | `#` introduces a proofgoal id; `# 1` is a parse error. See section 5 and D-0024 |
| wipe level | `w l` | **gone** | `w` is only the weakening operator inside a `pol` |
| solution | `sol <lits>` | `sol <lits> ;` | may **not** carry a label: "the rule `sol` cannot be prefixed with a label" |
| solution + exclude | `solx <lits>` | `solx <lits> ;` | unusable as-is: "only possible if a preserved set is specified" |
| improving solution | `soli <lits>` | `soli <lits> ;` | M5; untested here |
| objective update | `obju ... ;` | `obju ... ;` | needs explicit subproofs: "Proofgoal #1 could not be autoproven". M5 |
| output | `output NONE` | `output NONE ;` | guarantees are `NONE`, `DERIVABLE`, `EQUISATISFIABLE`, `EQUIOPTIMAL`, `EQUIENUMERABLE` |
| conclusion | `conclusion X` | `conclusion X ;` | `ENUMERATION_COMPLETE` / `ENUMERATION_PARTIAL` are new |
| end | `end pseudo-Boolean proof` | `... proof ;` | |
| short forms | `u` `p` `d` `v` `o` | **gone** | |
| label | — | `@name <rule> ;` | see below |

### `ia`'s hint is load-bearing, and misplacing it fails open *(M1-T51)*

`ia` is the only rule here that states what a *derivation concluded*, which is what makes
it the checker-level control `pol` never had. Three measured facts about it, all of which
cost something to learn:

**The hint is not optional in practice.** Both checkers accept `ia <c> ;` with no hint,
but unhinted it searches the **whole database**, and 3.0.2 says so when it fails:
`Constraint not syntactically implied by any constraint in the database`. So an unhinted
`ia` can be satisfied by an order-encoding ladder clause, or by some older derivation,
rather than by the `pol` on the line above it — a control that passes on something other
than its subject. `Writer.implied` makes the hint mandatory for exactly this reason.

**Misplacing the hint fails OPEN, silently.** In 3.0 the hint goes after a `:` and
*before* the terminator, as `red`'s witness does. After the `;` it is not a hint at all —
it is parsed as the **label of the next rule** — so this verifies clean:

```
ia +1 x1 +1 x2 >= 1 ; @NOPE     <- @NOPE is not a hint, and no error is raised
```

Measured against 3.0.2: `s VERIFIED`. Compare the correctly-placed form, which rejects as
it should. This is worse than trap 1 in section 2, which labels closed: a drifted *citation*
is now a parse error naming the label, but a drifted *hint* is not a citation and nothing
catches it. If you write an `ia` by hand, put the hint before the `;`.

**The two checkers' rejections share no substring**, as everywhere else in this project:

| | wording on a hint that does not imply the claim |
|---|---|
| 3.0.2 | `Expected constraint is not syntactically implied by the constraint at the hint.` |
| 2.2.2 | `Hint: ('1 x1 >= 1', '1 x1 1 x2 >= 1')` — a bare tuple of claim and antecedent, with no sentence at all |

Never match on one alone.

### Labels, and the trap they close

A constraint can be given a name, in the `.opb`:

```
@c1 +1 ~x_ge_3 +1 x_ge_2 >= 1 ;
```

and in the proof, on any rule that yields an id (`pol`, `rup`, `red`, `solx`, `soli`);
the name is then how later rules refer to it: `pol @c1 @c2 +`, `del id @c1`,
`del range @c1 @c7`, `core id @c1`, `conclusion UNSAT : @c13`. That `del range` deletes
`@c1`..`@c6` and **not** `@c7`; section 5 has the measurement and what it costs the
writer.

The writer labels **every** constraint `@c<id>` in 3.0 mode, model rows included, and
cites nothing by number. **Trap 1 below is therefore closed in 3.0**: a citation that
has drifted is a parse error naming the label ("The label `@NOPE` is not assigned to a
constraint ID"), not a silently different constraint. 3.0 also refuses a label on an
`=` row ("Expected inequality constraint"), which is the checker enforcing the
never-write-`=` discipline `Encoding.add_constraint` already imposed.

Two things labels do **not** do, and neither should be implied:

- **A label is not a group.** Binding one name twice rebinds it; it does not name both,
  so `del id @L` deletes one constraint. Labels cannot stand in for the level stack.
- **They do not remove the `f` count.** The count is still required and is still checked
  — by both checkers, loudly. That half of trap 1 was never the silent half.

## 3. Encoding *(normative — names are part of the contract)*

### Order encoding

For an integer variable named `x` in FlatZinc with initial domain `[l, u]`, emit Boolean
variables

```
x_ge_v        for l < v <= u        meaning  x >= v
```

with consistency constraints, for each `l < v < u`:

```
1 ~x_ge_(v+1) 1 x_ge_v >= 1 ;        i.e.  x >= v+1  ->  x >= v
```

Then `x >= l` is the constant true and `x >= u+1` the constant false; neither gets a
variable. Bound prunings become unit literals over this family, which is exactly why the
order encoding is the default: `lo := k` is the single literal `x_ge_k`, and `hi := k` is
`~x_ge_(k+1)`.

#### The consistency clauses are in the `.opb`, and they are load-bearing *(normative — M1-T25)*

The `u - l - 1` consistency clauses ("the ladder") are written into the `.opb` eagerly, by
`Encoding.declare_int`, for every declared variable. That is a requirement, not an
implementation choice, and the reason is not the one it looks like:

- **No derivation this project emits ever cites a ladder id.** `Encoding.consistency_id`
  has **no** caller in `lib/` or `bin/` at all — only `test/unit/test_proof.ml` — and the
  one place in `lib/` that reads the id table, `derive_at_most_one`, is itself called only
  from that same test file. Read from the emission side, the ladder looks like dead weight.
- **The checker's unit propagation needs it anyway.** Every `rup` in this project — the
  D-0018 trace lines of section 4 above, and the branch nogoods that are RUP *along*
  them — is checked by propagating from the model rows. A model row is the order
  encoding's expansion (section 3's substitution, `Encoding.expand_int_lin_le`), in which
  every literal of one variable carries the *same* coefficient, so the row constrains only
  **how many** of `x`'s literals hold. Nothing but the ladder ties "`x_ge_k` holds" to
  "at least `k - l` of them hold". Without it, `~x_ge_k` propagates nothing, the row's
  slack never goes negative, and the trace line is not RUP.

Measured rather than argued, because "nothing cites it" is a tempting thing to act on.
Strip every ladder row out of each model's `.opb` (labels are explicit in 3.0, so the
survivors keep their names; only the `f` count moves) and re-run the checker:

| | models | what they have in common |
|---|---|---|
| still accepted | 13 of 20 | no trace line whose RUP check needs a count |
| rejected | 7 of 20 | `chain_sat`, `guess_wrong_sat`, `ne_conflict_sat`, `near_limit_ne_sat`, `near_limit_unsat`, `offset_unsat`, `width_sat_depth` — and in every one the **first** line to fail is the first trace line |

The `.opb` is therefore Θ(declared width) per variable twice over: once for the ladder and
once for each row the variable appears in. That is a cost the project has accepted, not
one it has failed to notice; **D-0028** owns the justification half of the same root cause
and **D-0031** owns this half, including the measurement of what deferring the ladder
would cost.

#### Introducing a ladder rung mid-proof, if it is ever wanted

It can be done, and the witness is not the obvious one. Measured against VeriPB 3.0.2:

```
red +1 ~x_ge_(v+1) +1 x_ge_v >= 1 : <witness> ;
```

- **A swap witness — `x_ge_v -> x_ge_(v+1)  x_ge_(v+1) -> x_ge_v` — works only while the
  rung has no neighbour.** It is the natural witness (a model row counts literals, so
  swapping two of them leaves every row invariant), and it is accepted for the first rung
  of a variable and refused for the second: *"Proofgoal 2 could not be autoproven"*. The
  goal it fails on is the neighbouring rung's image, which is genuinely false, so no
  explicit subproof rescues it. Tried on the real models: 5 of 6 rejected.
- **A rotation witness works.** Introduce the rungs in increasing `v`, and let the witness
  cycle the whole already-laddered prefix down by one, `x_ge_(l+1) -> x_ge_(v+1)` together
  with `x_ge_u -> x_ge_(u-1)` for `u` in `l+2 .. v+1`. Each existing rung's image is then
  the rung below it (already in the database) and the bottom one's image is satisfied by
  the negated claim. Accepted on all 8 models it was tried on.

The price is that the witness for rung `v` is Θ(v) entries, so a whole ladder is Θ(w²)
of proof text where the `.opb` spends Θ(w). Measured on `width_sat_depth`: `.opb`
16 153 → 9 237 B, `.pbp` 29 859 → 221 525 B. That is why the rungs stay in the `.opb`;
see D-0031.

### Direct encoding

Introduced lazily, only for variables that an `element` or `all_different` propagator
touches (M4). **Not** for disequalities — see "Disequalities" below; that sentence used
to name them and was wrong:

```
x_eq_v        for l <= v <= u       meaning  x = v
```

channelled to the order encoding by, for each `v`:

```
x_eq_v  <->  x_ge_v  /\  ~x_ge_(v+1)
```

emitted with `red` as a definition. Exactly-one over `x_eq_*` follows from the
channelling and MUST be derived, not assumed.

The test for when the direct encoding is genuinely forced is whether a *reason* has to
mention a hole. A reason that does cannot be negated into a clause without a single
literal standing for `x = v`. A disequality's reasons never do — they are only ever
"these variables are fixed to these values" — which is why M1-T9 needs none of this.

### Disequalities *(M1-T9)*

The order encoding cannot state `x = v` as a single **literal**, which is what the
section above is about. But a `rup` target is a **clause**, and a disequality is two
ordinary order literals:

```
x <> v   <->   ~x_ge_v  \/  x_ge_(v+1)
```

Constant halves drop at the declared bounds, and a declared-fixed variable yields the
**empty** clause — which is correct, being the false clause, and renders as `rup >= 1 ;`.

In the `.opb`, a disequality is carried as two big-M rows over the order encoding with
one fresh selector Boolean `_neN`, `L` and `U` the span of `sum a_i x_i` over declared
domains:

```
row A:  sum a_i x_i - (U - c + 1) b  <=  c - 1      (b = 0  ->  sum <= c-1)
row B:  sum a_i x_i - (c + 1 - L) b  >=  L          (b = 1  ->  sum >= c+1)
```

Both are posted through `add_int_lin_le`, so both are plain `>=` lines and **the
`=`-counts-as-two trap in section 2 is not in play**. The `.opb` must carry the
disequality at all because it is what `conclusion SAT` is checked against; the selector
is filled in by the checker's own unit propagation, which is checked rather than
assumed. Aux names are minted as `$neN`, which FlatZinc cannot spell, and sanitised to
`_neN` on the way into the file.

### Booleans

`Lit.pbvar` has no Boolean constructor. A `var bool` is encoded as the order encoding on
`[0, 1]`: "b is true" is `b_ge_1`, via `Lit.bool_true` / `Lit.bool_false`. Do not invent a
bare `b` name for a Boolean — that would be a second naming scheme for the same thing, and
the point of this section is that there is only one.

### Naming

Variable names in the OPB file are the FlatZinc identifier with the suffixes above.
Identifiers that are not valid OPB names are rewritten by `Lit.sanitize` and the mapping
is dumped as comments at the head of the `.opb`. Do not invent a second naming scheme —
grep-ability of proofs against models is the point.

## 4. Per-propagator justification

Each propagator module MUST document, in its header comment, the shape of the proof step
it emits. The table below is the index; it is maintained as propagators land.

| Propagator | Consistency | Justification |
|---|---|---|
| `int_le` | bounds | the instance `1*x + -1*y <= 0` of `int_lin_le`, and therefore `int_lin_le`'s `Combine` (D-0013/D-0015) — **not** the `Cut (Trivial, Linear, 1, 1)` this row claimed until M1-T13 |
| `int_lt` | bounds | the same, at rhs `-1` |
| `int_eq` | bounds | `int_lin_eq` on `x - y = 0`. A domain-consistent version would intersect domains value by value and name the excluded value rather than a bound chain — not built |
| `int_lin_le` | bounds | `pol` — the model row, every *other* term weakened away by literal axioms or cited by the id that established it, then one division by the pushed coefficient (`Combine`, D-0013/D-0015). Under a decision each push also gets a D-0018 trace line. The older "M1 emits `rup` of the stated bound" is no longer true |
| `int_lin_eq` | bounds | two `int_lin_le` derivations |
| `int_ne` | value (domain, in fact) | `rup` over **order**-encoding literals: the claim disjoined with the negation of its reason, which is D-0018's trace-line shape. No direct encoding — see section 3, "Disequalities" |
| `int_lin_ne` | value | the same, over every term |
| `bool_clause` | — | `rup` |
| `all_different` | *TBD* | Hall-set reasoning; see M4 and D-0004 |
| `element` | *TBD* | M4 |

### The trace line *(D-0018, D-0021 — normative)*

Every pruning writes one line, **root-level prunings included**:

```
rup 1 <claim> 1 ~<fact> 1 ~<fact> ... >= 1 ;
```

- **claim** — the order literal the pruning established. `set_lo x k` gives `x_ge_k`;
  `set_hi x k` gives `~x_ge_(k+1)`.
- **facts** — the bound facts the propagator actually read, negated. For `int_lin_le`,
  each *other* term contributes `x_i >= lo(x_i)` when `a_i >= 0` and `x_i <= hi(x_i)`
  when `a_i < 0`. A bound still at its declared value contributes **nothing**: its
  negation is false, so including it would weaken the clause for no reason.
- The line mentions **no decision** and is a consequence of one model row, so it is
  globally valid. That is the whole point: the decisions appear only in the nogood, and
  the nogood is RUP *along* the trace.
- Each line is tagged with the decision level of the **trail entry** that produced it, not
  the writer's current level, so one `w` per backtrack retires exactly the lines whose
  prunings were undone.
- Level-0 lines are covered by no `w` and MUST be deleted explicitly before `conclusion`,
  or I-X2 fails.

The facts are a *different projection of the reason* from the one a `pol` needs: `Weaken`
carries the full declared-width chain, the trace line carries the current bound. Derive
both from **one** snapshot, or they will drift and the checker will accept the mismatch
(that is D-0009's failure mode, which cost a whole round).

To check a single line in isolation, write a one-rule proof — `f N`, the line, then
`conclusion NONE`. VeriPB accepts that and reports `VERIFIED NO CONCLUSION`. A trace line
must verify this way (it is decision-free); a nogood must **not**.

## 5. Backtracking and deletion

**In 2.0**, use levels, not individual deletions. `# <level>` sets the current level,
everything derived afterwards is tagged with it, and `w <level>` wipes every constraint
at or above that level in a single rule. One proof line per backtrack instead of one
`del` per reason — which matters because the alternative makes the proof grow with the
size of the search rather than with the interesting part of it.

`w` on a level that was never set is an error (*"Tried to wipe level N that was never
set"*), so levels must be opened before they are wiped. That mirrors the solver's own
decision levels exactly, which is the point.

**In 3.0 there is no level stack at all** — neither `#` nor `w` exists (section 2a), so
the paragraph above describes a mechanism the checker no longer has. `Writer` keeps the
tags itself and `wipe_level` emits the deletions `w` would have performed, compressed
into `del range` where the ids are consecutive, which they usually are. The interface is
unchanged: `Writer.set_level` / `Writer.wipe_level`, and callers do not know the
difference. The asymptotic argument above is what this costs; D-0024 has the detail and
is honest that it is a loss, not a wash.

The set retired is "every id **tagged** at level >= l", not "every id derived since the
level was set". They differ as soon as a level is re-entered after a spell at a lower
one, which is what search does on every branch: `# 1`, `# 0`, prune at the root, `# 1`,
prune under the decision, backtrack. The root prunings must survive.

### What `del range LO HI` deletes *(measured, not assumed — M1-T22)*

**`del range LO HI` deletes the half-open span `[LO, HI)`. The constraint named by `HI`
is not deleted.**

That sentence is a statement about **VeriPB 3.0.2**, the checker `scripts/checker.sh`
resolves, and about nothing else. It is phrased that way deliberately: this project has
already shipped a bug because "checked against veripb 2.2.2" was written down as a fact
about proofs in general and stopped being true when the checker changed (M1-T18, and
trap 5 in section 2). `test_v3_del_range_semantics` in `test/unit/test_proof.ml`
re-measures it on every run, and `report_checker` at the top of that file prints which
binary and which version answered. If a later checker disagrees, that test goes red and
**this section is what changes**, not the test.

How it was established, with controls in both directions, because "the checker accepted
it" on its own is not evidence:

| Probe after deriving `@a1 @a2 @a3` | 3.0.2 | what it settles |
|---|---|---|
| no deletion, then `pol @a3` | verified | the probe is valid when the id is live |
| `del id @a3`, then `pol @a3` | error: *"Trying to access constraint with ID 5 that has already been deleted"* | a rejection really does mean "gone from the database" |
| `del range @a1 @a3`, then `pol @a3` | **verified** | `@a3` **survived** the range that names it |
| `del range @a1 @a3`, then `pol @a2` | error, ID deleted | the interior is deleted |
| `del range @a1 @a3`, then `pol @a1` | error, ID deleted | `LO` is deleted |
| `del range @a1 @a4`, then `pol @a3` | error, ID deleted | widening `HI` by one is what retires the old `HI` |

Two consequences the writer depends on, measured the same way:

- **An unbound label is a parse error**, not a tolerated bound: `del range @a1 @a6` with
  no `@a6` gives *"The label `@a6` is not assigned to a constraint ID"*. A *numeric*
  upper bound past the last id **is** tolerated, but the writer cites nothing by number
  in 3.0 (section 2a) and a bare integer here would reintroduce trap 1 by hand.
- **An already-deleted label still resolves**, so a range may name an upper bound that
  an earlier deletion has retired.

So `Writer.del_run` writes the *inclusive* run `[lo, hi]` as `del range lo (hi+1)`, and
falls back to an explicit `del id` list — still one line, `del id` takes a list — when
`hi` is the newest id the writer has handed out and there is therefore no `@c(hi+1)`
label to name. Until M1-T22 it wrote `del range lo hi`, so every run of two or more ids
left its last id live in the checker while `t.tags` and `t.live` had dropped it: an I-X3
mirror violation, present in 7 lines across 5 of the 15 shipped models, and invisible to
the audit because the audit checks our own bookkeeping against itself.

That is why the regression test runs the checker rather than pinning the emitted string.
The bug *was* a disagreement between our string and the checker's reading of it, and the
test that pinned the string was green throughout.

A 3.0 proof marks a level with a `% level N` comment where the rule used to be. It is
emitted unconditionally, not under `--proof-comments`: without it nothing in the proof
says where a decision began. A test that detects branching by grepping a proof must look
for that marker under 3.0 — grepping for `# 1` there is not a failing test, it is a test
that silently stops testing.

### `drop-line` fails on the grammar in BOTH formats *(corrected — D-0030)*

Deleting a derivation step from an emitted proof — the mutation harness's `drop-line`
lane — does not test the derivation, in **either** format. It un-defines the step, so the
next rule that refers to it cannot be read at all:

| format | the checker's own words |
|---|---|
| 3.0 | ``The label `@c3` is not assigned to a constraint ID`` |
| 2.0 | `Accessing the database out of bound with index 3` |

This was written down in several places as a **3.0 quirk** — the roadmap said so, D-0023
said so, and this section was cited as saying it. It is not one; 2.0 fails the same way
for the same reason, one id short instead of one label short. D-0030 measured both and
records the correction, and the two messages above are the measurement, not a reading of
a grammar. The knob is unfixable as a text edit: a step is deleted *precisely because*
something later cites it. The lane stays registered as `Unevaluated` and still runs;
what actually judges an inference on that step is the `Truncate_derivation` knob, which
keeps the leftmost operand so the step still binds its label.

The general rule this is an instance of, and the one to apply to the next lane: **a lane
rejected without the checker ever judging an inference is not a pass.** See D-0020 and
D-0030.

`del id N ...` is still right for retiring a constraint not tied to a decision level,
such as a learned clause being forgotten.

Failing to delete does not make a proof wrong, but makes it grow without bound and makes
checking quadratic. `BAGUETTE_PROOF_AUDIT=1` asserts the live-id set is empty at
`conclusion`.

**What the audit covers**: the live set holds only ids *handed back by rule emission*.
Model constraints introduced by `f` are excluded — ARCHITECTURE §6 says "an id you
received is an id you are responsible for deleting", and nobody receives those;
`Writer.model_ids` lists them separately. A contradiction consumed by
`conclusion UNSAT : <cid>`, and the lower-bound id in `BOUNDS`, count as discharged by
the conclusion, since they cannot be deleted before being referenced.

## 6. Debugging a rejected proof

1. Run with `--proof-comments` — every rule is preceded by a `*` comment naming the
   propagator, the decision level, and the pruning.
2. `veripb --trace` shows the rule that failed.
3. Shrink: `scripts/shrink.sh MODEL` re-runs with propagators disabled one at a time to
   find which one emits the bad step.

Do not "fix" a rejected proof by switching the step to `rup`, or by using `a`. A rejected
step means the propagator pruned something it could not justify — that is a soundness bug
in the propagator until proven otherwise.
