# The VeriPB contract

Everything `baguette` emits and the vocabulary it is allowed to use.

Emitted proof format: **VeriPB 3.0, and only 3.0** (M1-T19 built it, D-0025 made it the
default, **D-0046 removed everything else**). There is no format switch and no second
checker. **Section 2a is the contract.**

Section 2 is kept as **history**: it records what format 2.0 did and what it cost this
project to learn, because several of those findings still explain code that survives the
format. It does not describe anything `baguette` emits. Where a fact in it is still live,
it says so and says where the live statement is.

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
3. `veripb` on `$PATH`.

`$PATH` is last deliberately. This project once had two builds installed side by side
with the other one first on `$PATH`, so "whatever is on `$PATH`" silently meant a checker
nobody had chosen (M1-T18). Naming the path we mean is what closed that; a `$PATH` entry
is whatever the machine happens to offer.

**There is one checker, and D-0046 states what that costs.** Two independently written
checkers agreeing that a proof verifies is stronger evidence than one, and several of
this project's findings came from the two disagreeing. After D-0046, veripb 3.0.2 is the
**sole oracle**: a bug in it is a bug we have no way to see. That was weighed and
accepted, and it is recorded so nobody rediscovers it and assumes it was overlooked.

**No checker is a failure, not a skip.** `verify_proof.sh` used to `echo SKIP; exit 0`
when it could not find `veripb`, so a machine with no checker made every proof test
pass — the one outcome a suite built on "a test that does not check the proof is half a
test" must never produce. Every entry point now fails loudly. There is no
`BAGUETTE_SKIP_PROOFS` escape hatch and none should be added.

The proof's first line MUST be exactly:

```
pseudo-Boolean proof version 3.0
```

The `.opb` is part of the same artefact: every row carries a label (section 2a), and a
`.pbp` citing a label the `.opb` never bound is a **parse error**, so the checker stops at
the grammar and judges nothing. `Encoding.write_opb` labels unconditionally and is the
only way to write one, which is what keeps the pair in step — this used to be a switch,
and every time the two sides of it disagreed a lane went green for the wrong reason
(M2-L5, M2-T14).

## 2. Rule vocabulary, 2.0 — *HISTORICAL (removed by D-0046)*

> **Nothing in this section describes what `baguette` emits.** Format 2.0 and the Python
> VeriPB 2.2.2 that read it left the project on 2026-09-18 (D-0046). The section is kept
> because it is the record of what 2.0 did and what it cost to learn — D-0024's account
> of `w` explains `Writer.wipe_level`, which survives, and the traps below are the
> measurements that shaped the encoding. Deleting the reasoning along with the format
> would have thrown away the expensive half.
>
> **The live contract is section 2a**, which is where the still-true parts of this
> section now live: the `pol` operator semantics, the rule preferring `pol` over `rup`,
> and the traps.

These were the VeriPB 2.0 rules this project used. Every row was checked empirically
against veripb 2.2.2. Where this document disagreed with the checker, the checker won.

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

*(The `pol` operator semantics, the `pol`-over-`rup` rule and the traps that used to
close this section are live facts, not 2.0 facts, and have moved to section 2a.)*

## 2a. The 3.0 rule vocabulary *(D-0023, D-0046)*

**This is the contract.** Every row was run against veripb 3.0.2; where a row says
something is refused, the checker's own words are quoted. Anything outside this list
needs a decision record before it appears in an emitted proof — an unfamiliar rule in a
proof is a debugging problem for whoever reads the failure next.

3.0 was **not** a dialect of the 2.0 this project used to emit, which is why D-0046 could
remove that format outright rather than deprecating it: there was no shared subset to
keep. The "2.0" column that used to sit in this table is gone with it; section 2 holds
the old grammar for anyone reading an archived proof.

| Rule | Syntax | Note |
|---|---|---|
| version | `pseudo-Boolean proof version 3.0` | the first line, exactly |
| load | `f N ;` | the count is required and a wrong one is a hard error naming the right number |
| comment | `% text` | `*` is refused: "Expected a top level rule name" |
| cutting planes | `pol <rpn> ;` | operands are labels; see the operators below |
| RUP | `rup <c> ;` | the constraint already carries the terminator, and a second `;` is an error |
| **implies / assert** | `ia <c> : @hint ;` | **Was missing from this table until M1-T51.** Asks whether `<c>` is *syntactically implied* by the one constraint at the hint — no propagation, no search. Yields an id. See the trap below |
| **equals** | `e <c> : @hint ;` | same shape; asks for syntactic *equality* rather than implication. Rejections: "Expected constraint is not equal to the constraint at the hint.", unhinted "Constraint not found in database." |
| redundance | `red <c> : <witness> ;` | the witness goes **before** the terminator. After a `;` it is silently not a witness |
| delete | `del id N M ;` | also `del range LO HI ;`, **half-open: `[LO, HI)`, so `HI` survives** (measured, M1-T22); tolerant of an already-deleted id and of a reversed range |
| delete from core | `delc N ;` | `delc` takes the reference directly; `del` and `core` keep their `id` |
| core | `core id N ;` | |
| set level | **does not exist** | `#` introduces a proofgoal id; `# 1` is a parse error. See section 5 and D-0024 |
| wipe level | **does not exist** | `w` is only the weakening operator inside a `pol` |
| solution | `sol <lits> ;` | may **not** carry a label: "the rule `sol` cannot be prefixed with a label" |
| solution + exclude | `solx <lits> ;` | unusable as-is: "only possible if a preserved set is specified" |
| improving solution | `soli <lits> ;` | M5; untested here |
| objective update | `obju ... ;` | needs explicit subproofs: "Proofgoal #1 could not be autoproven". M5 |
| output | `output NONE ;` | guarantees are `NONE`, `DERIVABLE`, `EQUISATISFIABLE`, `EQUIOPTIMAL`, `EQUIENUMERABLE` |
| conclusion | `conclusion X ;` | see SPEC section 4.3 |
| end | `end pseudo-Boolean proof ;` | last line, exact text |
| label | `@name <rule> ;` | on any rule that yields an id; see below |
| `a` | | add a constraint assumed-checked — **forbidden**, debugging only |

### The `pol` operators

`pol` is reverse Polish over constraint references: `pol @c3 @c4 + 2 d` means "constraint
`@c3` plus constraint `@c4`, divided by 2". Literal axioms are written `~x1` / `x1`. The
weakening operator `w` takes a **variable, not a literal** — it ignores any sign you give
it, and VeriPB only logs a warning rather than failing, so a sign there is a silent no-op.

The three operators, measured against the checker rather than assumed:

| Op | Effect |
|---|---|
| `w <var>` | drops the variable's term and subtracts its coefficient from the right-hand side, **clamped at 0**. Exactly equivalent to adding `|a|` copies of that literal's axiom, which is how D-0013's derivation was first written |
| `s` | saturation: caps every coefficient at the current right-hand side, per literal; the right-hand side is unchanged |
| `d N` | divides **every coefficient and the right-hand side**, rounding each **up** |

The division row is the one to read twice: this document once said `d` rounds only the
right-hand side. It rounds the coefficients too, by the same ceiling. Checked: from
`+3 x1 +1 x2 >= 1`, `2 d` gives `+2 x1 +1 x2 >= 1` — under truncation it would have given
`+1 x1 >= 1`, forcing `x1`, and a `rup` of `x1` after the division is rejected, which is
what settles it.

**Rule**: prefer `pol` over `rup`. A `pol` step states the actual reasoning and is cheap
to check; `rup` makes the checker search. A propagator that can only produce `rup` should
say so in its module header and explain why.

### Traps

Things this document has previously got wrong, restated for the format that ships. The
first is the dangerous shape, because it corrupts ids rather than producing an error you
would notice:

1. **An `.opb` line with `=` counts as TWO constraints** for the `f` rule — the checker
   splits it into `>=` and `<=`. Get the count wrong and every later id is shifted, so a
   `pol` step silently references the wrong constraint. `Opb.n_checker_constraints`
   computes the header count the checker's way; `Encoding.add_constraint` refuses `Eq`
   outright and `Encoding.add_equality` emits the two `>=` lines explicitly, returning
   both ids. **Labels closed the silent half**: a citation is a name, so a drifted one is
   a parse error rather than a different constraint (see *Labels* below). The `f` count
   itself was never the silent part — a wrong one is rejected and the right number named.
2. **`sol`, `solx` and `soli` differ in id accounting**: `sol` adds no constraint, the
   other two each add one. Treating them as interchangeable desynchronises our id counter
   from the checker's.
3. **`#` is not a comment marker.** It introduces a proofgoal id. Comments are `%`.
4. **Deletion takes an identifier kind**: `del id N`, not `del N`. Same for `core`
   (`id` / `range` / `find` / `spec`). `delc` is the exception and takes the reference
   directly.
5. **`conclusion SAT : <assignment>` is not propagated.** 3.0.2 reads every variable the
   assignment does not mention as false, and the assignment the solver has covers the
   *model* variables only — not the encoding auxiliaries (the `_neN` selectors of
   section 3), which nothing in the solver knows values for. `ne_conflict_sat.fzn` needs
   a selector *true*, so its honest proof is REJECTED in that form. Log the assignment
   with `sol` and conclude with the bare `conclusion SAT`: a *logged* solution **is**
   propagated. `Writer.conclusion` does this for `Sat`. `solx` is not an alternative —
   3.0.2 refuses it outside a preserved set. *(Historically this was the one point on
   which the 2.2.2 this project also checked against disagreed, which is how it was
   found; M1-T18.)*

### `ia`'s hint is load-bearing, and misplacing it fails open *(M1-T51)*

`ia` is the only rule here that states what a *derivation concluded*, which is what makes
it the checker-level control `pol` never had. Three measured facts about it, all of which
cost something to learn:

**The hint is not optional in practice.** The checker accepts `ia <c> ;` with no hint,
but unhinted it searches the **whole database**, and says so when it fails:
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
it should. This is worse than trap 1 above, which labels closed: a drifted *citation* is a
parse error naming the label, but a drifted *hint* is not a citation and nothing catches
it. If you write an `ia` by hand, put the hint before the `;`.

**Match the rejection's wording, at full strength.** The wording on a hint that does not
imply the claim is

> `Expected constraint is not syntactically implied by the constraint at the hint.`

A lane that asserts only a non-zero exit is green the moment the file stops PARSING, at
which point the checker has judged nothing — M2-T14 found four lanes passing that way.
So assert the sentence, not the exit code, and not a fragment weaker than the claim: on a
RUP failure the checker says *"reverse unit propagation"*, which would equally match any
other RUP failure in the file.

*(This rule used to read "never match on one checker's wording alone", because two
checkers worded their rejections differently and a lane matching one was vacuous against
the other — M1-T46. With one checker, D-0046, matching its wording **is** the correct
thing to do. What survives of M1-T46 is the part above: match the JUDGEMENT, at full
strength.)*

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

The writer labels **every** constraint `@c<id>`, model rows included, and cites nothing by
number. Labelling is unconditional and there is no knob for it (D-0046). **Trap 1's silent
half is therefore closed**: a citation that has drifted is a parse error naming the label
("The label `@NOPE` is not assigned to a constraint ID"), not a silently different
constraint. The checker also refuses a label on an `=` row ("Expected inequality
constraint"), which is it enforcing the never-write-`=` discipline
`Encoding.add_constraint` already imposed.

Two things labels do **not** do, and neither should be implied:

- **A label is not a group.** Binding one name twice rebinds it; it does not name both,
  so `del id @L` deletes one constraint. Labels cannot stand in for the level stack.
- **They do not remove the `f` count.** The count is still required and is still checked,
  loudly. That half of trap 1 was never the silent half.

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

- **claim** — what the pruning established, as a **clause**, not necessarily a single
  literal. `set_lo x k` gives `x_ge_k`; `set_hi x k` gives `~x_ge_(k+1)`; and a pure hole
  removal — which until M1-T56 got no line at all, on the mistaken grounds that no order
  literal states it — gives the two-literal clause `x <= v-1 ∨ x >= v+1`, i.e.
  `+1 ~x_ge_v +1 x_ge_(v+1) >= 1`. That is `Encoding.ne_clause_lits`, which §4 already
  names as `int_ne`'s justification: a claim never had to *be* a literal.
- **facts** — the bound facts the propagator actually read, negated, **plus the facts of
  any holes a settle walked over** (M1-T57). `Domain.settle` can carry a bound past holes
  to re-establish I-D2, so the bound on the trail is stronger than the one the propagator
  asked for; a line that cited only the propagator's facts would then claim more than they
  justify. On `root_hole_unsat` that line claimed `v0 >= 1` with an **empty** tail, i.e.
  unconditionally — I-P5's worst case, and false. For `int_lin_le`,
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

#### Standalone RUP: what is still true, and what is not *(corrected — M1-T57, D-0039)*

To check a single line in isolation, write a one-rule proof — `f N`, the line, then
`conclusion NONE`. VeriPB accepts that and reports `VERIFIED NO CONCLUSION`.

This section used to say "a trace line must verify this way (it is decision-free)". **That
is no longer true, and the counter-example is in the suite.** Measured on
`test/models/trace_settle_holes_sat.fzn` against 3.0.2: of its eight trace lines, six
verify standalone and **two are refused**. The settle line
`rup +1 x_ge_4 +1 w_ge_3 +1 y_ge_3 >= 1` is refused against the `.opb` alone and
**accepted** once the hole line `rup +1 ~x_ge_3 +1 x_ge_4 >= 1` precedes it.

The property that replaces it is weaker but still sharp. A trace line is RUP against the
`.opb` **plus the trace lines already emitted**, and it remains **decision-free** — it
mentions no decision and is globally valid, which is what the nogood story needs. What it
is no longer is individually derivable from the model. So:

- a **nogood** must still **not** verify standalone; that half is unchanged;
- a trace line for a bound move that crossed no hole still verifies standalone;
- a **settle** line, and any line citing a hole, does not, and a test that asserts
  standalone validity for *every* line is asserting something false. Assert the count per
  model, as `test_trace.ml` now does.

There is a consequence for deletion, and it is load-bearing: a line that cites a hole
line is only supported while that hole line is live. See **I-S4**.

## 5. Backtracking and deletion

**There is no level stack in the checker** — neither a set-level rule nor a wipe rule
exists (section 2a, D-0024). `Writer` keeps the level tags itself and `wipe_level` emits
the deletions the checker's own `w` would once have performed, compressed into
`del range` where the ids are consecutive, which they usually are. The interface is
`Writer.set_level` / `Writer.wipe_level` and callers do not see the difference.

**What that costs, because it is a loss and not a wash.** The mechanism this replaces was
one proof line per backtrack: `# <level>` set the current level, everything derived
afterwards was tagged with it, and `w <level>` wiped every constraint at or above that
level in a single rule. The alternative — one `del` per reason — makes the proof grow
with the size of the search rather than with the interesting part of it, and that
asymptotic argument is the whole reason levels existed. Runs recover most of it, but
"most" is not "all". D-0024 is the record; it is kept, and it is what `Writer.wipe_level`
exists to imitate.

The set retired is "every id **tagged** at level >= l", not "every id derived since the
level was set". They differ as soon as a level is re-entered after a spell at a lower one,
which is what search does on every branch: level 1, level 0, prune at the root, level 1,
prune under the decision, backtrack. The root prunings must survive.

### What `del range LO HI` deletes *(measured, not assumed — M1-T22)*

**`del range LO HI` deletes the half-open span `[LO, HI)`. The constraint named by `HI`
is not deleted.**

That sentence is a statement about **VeriPB 3.0.2**, the checker `scripts/checker.sh`
resolves, and about nothing else. It is phrased that way deliberately: this project has
already shipped a bug because a measurement against one checker was written down as a
fact about proofs in general and stopped being true when the checker changed (M1-T18, and
trap 5 in section 2a). That risk is larger now, not smaller: 3.0.2 is the sole oracle
(D-0046), so nothing else will contradict it.  `test_v3_del_range_semantics` in
`test/unit/test_proof.ml`
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
  (section 2a) and a bare integer here would reintroduce trap 1 by hand.
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

A proof marks a level with a `% level N` comment where the rule used to be
(`Writer.level_marker`). It is emitted unconditionally, not under `--proof-comments`:
without it nothing in the proof says where a decision began. A test that detects branching
by grepping a proof must look for that marker — and must ask `Writer` for the spelling
rather than hardcoding one, because a grep for a spelling that has moved is not a failing
test, it is a test that silently stops testing.

### `drop-line` fails on the grammar, and does not test a derivation *(D-0030)*

Deleting a derivation step from an emitted proof — the mutation harness's `drop-line`
lane — does not test the derivation. It un-defines the step, so the next rule that refers
to it cannot be read at all:

> ``The label `@c3` is not assigned to a constraint ID``

Every id is a **label**, so dropping its defining line is a parse error *whichever* line
you drop, and the checker never reaches the reasoning. The knob is unfixable as a text
edit: a step is deleted *precisely because* something later cites it. The lane stays
registered as `Unevaluated` and still runs; what actually judges an inference on that step
is the `Truncate_derivation` knob, which keeps the leftmost operand so the step still
binds its label.

*(History, because the correction cost something to get right. This was first written down
as a **3.0 quirk**, which it is not — the 2.0 this project also emitted failed the same
way, one id short instead of one label short. D-0030's amendment then refined that
further: a 2.0 id was **positional**, so dropping a line **renumbered** everything after
it, the citations still resolved (to different constraints), and the checker read a
well-formed proof and judged an inference. So under 2.0 `drop-line` was sometimes an
evaluating lane and sometimes not, depending on which line went. Whether `expect` should
therefore be per-format was **M2-T15**; D-0046 dissolved that question by leaving one
format, and it is closed.)*

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
