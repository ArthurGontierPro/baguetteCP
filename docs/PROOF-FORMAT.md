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
| `red`, **vacuity** | — | **over a CONTRADICTORY database every `red` is accepted, wrong witness or none at all** | measured on 3.0.2, D-0053. A redundance goal discharges trivially from a contradiction, so *"veripb accepted the `red`"* is **not evidence** unless the model is satisfiable. Any `red` emitted after the search has derived a conflict is rubber-stamped |
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
| redundance | `red <c> : <witness> ;` | the witness goes **before** the terminator. After a `;` it is silently not a witness. **A missing witness is a `Warning`, not an error** (3.0.2: *"A witness must be specified for the red-rule"*), and the run continues — what fails is the redundance goal further down, *if* anything fails at all. See the next row |
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

**Rule** *(amended 2026-11-10 from D-0127, designed into both arms by D-0130;
M8-bits-encoding-T5 implements it for the order arm)*: write a justification as `rup`
wherever the checker's unit propagation closes it -- the order encoding's ladder walks, and any
clause over atoms that already exist -- and as `pol` only where it cannot, which is every bound
that crosses a bits row and every step that needs a division. Measured on VeriPB 3.0.2
(D-0127): the same Θ(w)-rung cancellation at w = 10⁶ is 197 bytes and ~0.7 s of checking as a
`rup`, 28 MB and ~381 s as an explicit `pol` -- quadratic, because every addition of a rung into
an accumulator of Θ(w) terms costs Θ(w), while weakening is linear; the elaborator re-emits a
`pol` as it is and a `rup` as a hint list seven times smaller, which `cake_pb` checks faster
(34 s against 49 s). On bits a `rup` is refused at every width, and the `pol` is three citations,
flat from 10³ to 10⁶. `--stats` counts tokens per `pol`, so a Θ(w) one is visible rather than
argued. A propagator that can only produce `rup` should still say so in its module header and
explain why.

*(Until 2026-11-10 this rule read: "prefer `pol` over `rup`. A `pol` step states the actual
reasoning and is cheap to check; `rup` makes the checker search. A propagator that can only
produce `rup` should say so in its module header and explain why." That is true for a
derivation of O(1) citations and false for one of Θ(w): there the search IS the cheap part,
because unit propagation along the ladder is linear and the explicit arithmetic is not --
D-0127, point 1. The sentence is kept because D-0013 and every module header written before
that date cite it.)*

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

### Bits encoding *(normative — M8-bits-encoding-T2, D-0130 §4–§5, D-0132)*

A variable declared wider than `--bits-above W` (default `0` since D-0201: every eligible variable; `none`: no variable) whose scope
is eligible (D-0130 §3.4: no `all_different`, `global_cardinality`, `array_int_element`
or `cumulative` row names it, and no declared holes; width 0 and 1 stay order by rule;
M8-bits-encoding-T3, D-0134, released `array_int_maximum`/`minimum` (choice groups,
below), `int_ne`/`int_lin_ne`, `int_eq_reif`/`int_ne_reif` and `bool2int` (§4)) is
encoded on `n = bit_length(u − l)` Booleans, the least `n` with `2^n > u − l`:

```
x_bit_i        for 0 <= i < n        meaning  bit i of (x − l), unsigned
```

with two bound rows in the `.opb` and **no ladder**:

```
+1 x_bit_0 +2 x_bit_1 ... +2^(n-1) x_bit_(n-1) >= 0 ;              x >= l
-1 x_bit_0 -2 x_bit_1 ... -2^(n-1) x_bit_(n-1) >= -(u - l) ;       x <= u
```

Both rows are always posted, consecutive, even where one is trivially true, so that a
derivation weakens a bits term in either direction by one citation. A model row over `x`
carries `a·2^i` on `x_bit_i` with the same fold of `a·l` into its constant as the order
expansion (`Encoding.linear_terms_int_lin_le`); a row may hold both shapes.

**The order atoms keep their names.** `[x >= v]` is `x_ge_v` whether `x` is on the ladder
or on bits; what differs is that for a bits variable the name is not a variable of the
`.opb` but a proof-level atom, minted into the `.pbp` on demand by `Encoding.ensure_atom`,
at level 0, memoised per `(x, v)`, for `l < v <= u` only (`x >= l` and `x >= u+1` are
constants and are never minted), as a `red` pair whose witness touches only the fresh atom
(`k = v − l`, `K = 2^n − k`):

```
red +1 x_bit_0 ... +2^(n-1) x_bit_(n-1)  +k ~x_ge_v >= k : x_ge_v -> 0 ;     x_ge_v -> x >= v
red +1 ~x_bit_0 ... +2^(n-1) ~x_bit_(n-1) +K x_ge_v  >= K : x_ge_v -> 1 ;     x >= v -> x_ge_v
```

Measured on 3.0.2 (D-0132 §1): both orders are accepted for a fresh atom; the flipped
witness is refused at *"Proofgoal #1 could not be autoproven. Please add an explicit
subproof for proofgoal #1."* on a satisfiable model whose database does not decide the
atom, and **only then** — over a contradictory database, or for an atom the model decides,
the second half's flipped witness is accepted (D-0053, D-0127), which is why every test of
the pair mints under a decision. When an atom is minted between two already minted
neighbours `u < v < t`, two links `pol @B1_v @B2_u + s (v−u+1) d` and `pol @B1_t @B2_v + s
(t−v+1) d` (each pinned by `ia` to its clause `~x_ge_v ∨ x_ge_u`) keep the chain
`x_ge_t → x_ge_v → x_ge_u` walkable by unit propagation; links are never deleted before the
conclusion. Every atom, link, bridge and bound line is a level-0 id retired by the
end-of-run sweep (I-X2).

**An order variable in a row that has a bits term** is cited through the same shape, by a
`rup` bridge pair written once at level 0 (`k = v − l`, `K = (u − l) − k + 1`):

```
rup +1 x_ge_(l+1) ... +1 x_ge_u  +k ~x_ge_v >= k ;      x_ge_v -> at least k rungs
rup +1 ~x_ge_(l+1) ... +1 ~x_ge_u +K x_ge_v >= K ;      at least k rungs -> x_ge_v
```

and, at its declared bound, the degree-0 lines `rup Σ x_ge_w >= 0` / `rup Σ ~x_ge_w >= 0`,
also once. A `var bool`'s bridge is the tautology `+1 b_ge_1 +1 ~b_ge_1 >= 1`, one line.

**A pruning or conflict of a row with a bits term is not RUP** (D-0127: a bound does not
cross a bits row by unit propagation, at any width) and is written as one `pol` deriving
exactly its trace clause, pinned by `ia` (§4, `Linear`); the trace line of a row with no
bits term is the `rup` of §4 unchanged. The `sol`/`soli` assignment lists `x_bit_i` for a
bits variable, from which the checker propagates the atoms through their pairs; an
optimisation's bound literal over a bits objective is bridged from the `soli` constraint by
`pol @soli @B + s`, and at the floor its contradiction is derived (`pol @soli @lb +` or
`@ub +`) and cited, because the improving constraint over bits is not contradictory on its
own as the ladder's count is.

**Choice groups** *(M8-bits-encoding-T3, D-0134)*. A family whose order-arm rows are one
clause per VALUE cannot post them over a bits variable, and posts a choice group instead:
fresh `.opb`-only Booleans `$mxN` (`_mxN_ge_1` in the files, minted by the same
`fresh_aux_name` as `_neN`), one big-M row per alternative and one clause over the
selectors. `array_int_maximum(m, xs)` with a bits variable in its scope is the first: in
max coordinates (a minimum negates every view),

```
+1 m  -1 x_i  +M_i $mx_i <= M_i      M_i = dhi(m) − dlo(x_i)       one per operand
+1 _mx1_ge_1 ... +1 _mxn_ge_1 >= 1
```

after the `n` linear rows `x_i − m <= 0`; nothing is posted when the disjunction holds by
declaration (empty threshold range, or `m` among the operands). A scope with no bits
variable keeps the per-value rows of §4 byte for byte. The selectors are never searched on:
**`sol`/`soli` list them** after the bindings, the first operand attaining `m` true and the
others false, because at a tie neither selector is propagated by the rows and the checker
refuses the solution (*"The propagated assignment does not satisfy the constraint with ID
…"*, D-0134 §1 a6/a8).

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

### 3b. The second contract: `cake_pb_cp`'s names, under `--e2e` *(normative for `--e2e` only — M14-e2e-verification-T3, D-0187)*

Everything above is baguette's own `.opb`, and stays the only naming scheme of a default
run. Under `--e2e` the proof is checked against the `.opb` that CakeML's verified encoder
`cake_pb_cp` writes for the model's `.scp` (D-0174), and its head (`lib/proof/e2e.ml`) cites
that file's rows by label. Baguette never reads the file. What it relies on is this section,
transcribed from the HOL4 sources of the build it was checked against: **`cake_pb_cp` sha256
`ca92491e`, CakePB `438b8f83`, CakeML `14856fcf`** (`cp_encScript.sml`, `cp_to_ilpScript.sml`,
`ilpScript.sml`, `ilp_to_pbScript.sml`, `cp_to_ilp_linearScript.sml`,
`cp_to_ilp_primScript.sml`, `cp_to_ilp_logicalScript.sml`, `cp_to_ilp_countingScript.sml`,
`int_bitwiseExtraScript.sml`; for T6, `cp_to_ilp_extensionalScript.sml` and
`cp_to_ilp_schedulingScript.sml`). A different build may break it. That shows as a refused line,
never as a verified wrong answer, because every cited row is checked against cake's file.

**The translator's names** (`tools/e2e/fzn2scp.py`, part of the contract). The k-th FlatZinc
constraint item, counted from 1 in file order, is `.scp` constraint `c<k>`; a variable is its
FlatZinc name with every character outside `[A-Za-z0-9_]` replaced by `_` (written `X` below);
the k-th variable with a set domain with holes, in declaration order, gets `(d<k> in (v ...) X)`.

**Integers.** X over `[l, u]` is its two's-complement bits: `i[X][b<j>]` with weight `2^j`,
`j < h`, and `i[X][sign]` with weight `-2^h` when `l < 0` (`bit_width`: `h` is the bit length
of `u`, or of the larger of `l` and `u` when `l < 0`, a negative `i` counting as `-i - 1`). Its
bound rows are `@i[X][lb]` (`B >= l`) and `@i[X][ub]` (`B <= u`).

**Atoms**, written only where a constraint asks for one: `i[X][ge<k>]` (`B >= k`), defined by
`@i[X][ge<k>][f]` (`B >= k -> atom`) and `@i[X][ge<k>][r]` (`atom -> B >= k`); `i[X][eq<k>]`,
defined by `@i[X][eq<k>][f]` and `[r]` over `i[X][ge<k>]` and `i[X][ge<k+1>]`, which exist
with it; a constant `K` in a reify tuple is `n[K][ge<k>]`, `n[K][eq<k>]`, likewise. A negative
`k` is written `-3`.

**Rows** (ilp_to_pb's `>=` form; `c[N]` is `mk_name`, `@c[N][tag]`):

| `.scp` | rows | flags |
|---|---|---|
| `less_equal x y`, `less_than x y`, `lin_less_equal (a x ...) c` | `@c[N]`: `y - x >= 0`, `y - x >= 1`, `-sum a x >= -c` | |
| `equals x y`, `lin_equals` | `@c[N][ge]` (`x - y >= 0`), `@c[N][le]` | |
| `not_equals x y`, `lin_not_equals` | `@c[N][gt]` (`x - y >= 1` unless `~b[N][ne]`), `@c[N][lt]` (`y - x >= 1` unless `b[N][ne]`) | `b[N][ne]` |
| `all_different (x0 ... )` | per pair `i < j`: `@c[N][<i>gt<j>]`, `@c[N][<i>lt<j>]` | `x[N][<i>_<j>]` |
| `or (t ...) t0`, `and` | `@c[N][pos]`, `@c[N][neg]` over the tuples' eq atoms | |
| `less_equal_iff t x y`, `lin_less_equal_iff` | `@c[N][r]` (`t -> ...`), `@c[N][f]` (`... -> t`) | |
| `equals_iff t x y` | `@c[N][ge]`, `@c[N][le]` guarded by `t`; `@b[N][gt][r]`, `@b[N][lt][r]`; `@c[N][al1]`: `lt + gt + t >= 1` | `b[N][gt]`, `b[N][lt]` |
| `not_equals_iff t x y` | the same guarded by `~t`, both flags with `[f]` and `[r]`, `al1` over `lt + gt + ~t` | `b[N][gt]`, `b[N][lt]` |
| `d<k> in (v ...) X` | `@c[d<k>][al1]` over `i[X][eq<v>]` | |
| `element (a0 ...) (I 1) Z` *(T3b)* | `@c[N][lb]` (`I >= 1`) when I's range starts below 1, `@c[N][ub]` (`-I >= -n`) when it ends above n; per position p from 0, `@c[N][<p>ge]` (`a_p - Z >= 0`) and `@c[N][<p>le]` (`Z - a_p >= 0`), each unless `~i[I][eq<1+p>]` | |
| `gacglobalcardinality (X ...) (v ...) (C ...)` *(T3b)* | per cover value j from 0, `@c[N][<j>_ge]` (`sum_i [X_i = v_j] - C_j >= 0`) and `@c[N][<j>_le]` (the reverse); a constant C_j moves to the degree | |
| `array_max (X ...) Y`, `array_min` *(T3b)* | per operand i from 0, `@x[N][<i>][f]` and `@x[N][<i>][r]` (the flag iff `X_i >= Y`, resp. `X_i <= Y`), `@c[N][<i>le]` (`Y - X_i >= 0`; resp. `<i>ge`), `@c[N][al1]` over the flags | `x[N][<i>]` |
| `max X Y Z`, `min` *(T3b)* | `@b[N][lge][r]`, `@b[N][rge][r]` (flag -> `X >= Z`, `Y >= Z`; resp. `lle`, `rle`), `@c[N][lle]`, `@c[N][rle]` (resp. `lge`, `rge`), `@c[N][al1]` | `b[N][lge]`, `b[N][rge]` (resp. `lle`, `rle`) |
| `inverse ((X ...) ox) ((Y ...) oy)` *(T3b)* | `@c[N][X_<k>_lb]`, `X_<k>_ub` (X_k in oy..oy+n-1), `@c[N][Y_<k>_lb]`, `Y_<k>_ub`, k from 1; per (i, j) from 0, `@c[N][<i+1>_<j+1>ge]` (`[X_i = oy+j] - [Y_j = ox+i] >= 0`) and `...le` (the reverse) | |
| `c<k>_<p> equals_if (b = 1) X Y` *(T3b, member)* | `@c[c<k>_<p>][ge]`, `@c[c<k>_<p>][le]` guarded by `i[b][eq1]`; then `or` over the selectors' tuples with `(1 = 1)` | |
| `abs X Y` *(T6, D-0195)* | the atom `i[X][ge0]`; `@c[N][posge]` (`X - Y >= 0`), `@c[N][posle]` (`Y - X >= 0`) unless `~i[X][ge0]`; `@c[N][negle]` (`Y + X >= 0`), `@c[N][negge]` (`-X - Y >= 0`) unless `i[X][ge0]` | |
| `regular (X0 ...) n ((edges of 0) ...) (f ...)` *(T6)* | per position idx (0..len) `@c[N][pos<idx>al1]`, `am1` over `x[N][<idx>_<q>][st]`, `q < n`; `@c[N][st<len>al1]` over the finals' flags at the end; `@c[N][st0]`; per position, state q and value index vi of `X_idx`'s BOUNDS (holes included), `@c[N][<idx>_<q>_<vi>t]`: `~st[idx][q] + ~i[X][eq<v>] + OR st[idx+1][targets] >= 1`; the eq atoms of every value | `x[N][<idx>_<q>][st]` |
| `cumulative (S ...) (d ...) (r ...) cap` *(T6)*, constants d, r, cap | `@c[N][cap_ge0]`, `@c[N][h_<i>_ge0]`; per task i from 0 and time t of `[lb S_i, ub S_i + d_i - 1]`: `@v[N][<i>_<t>][cb][f]`, `[r]` (the flag iff `S_i <= t`), `@v[N][<i>_<t>][ca][f]`, `[r]` (iff `S_i + d_i >= t + 1`), `@c[N][<i>_<t>_acta|actb|actcal1]` (`cact` iff both), `@c[N][<i>_<t>_cge]` (`r_i ~cact + sum_b 2^b cc_b >= r_i`), `_cle`, `_cz`; per t of the windows' union, `@c[N][cap_<t>]`: `- sum over the tasks covering t of their cc bits >= -cap` (a negative t written `-3`) | `v[N][<i>_<t>][cb|ca|cact]`, `v[N][<i>_<t>_<b>][cc]` |

Constants are folded into the degree (`mk_constraint_ge`, `mk_lin_constraint_ge`), integer
terms are kept per occurrence, and a guard's big-M is `max(0, c - min)` (`bits_imply`) or
`max(0, 1 - c + max)` (`imply_bit`) over the terms' BIT range, not their declared bounds.

**What the prefix adds**, all of it fresh names baguette's own `.opb` uses in the same sense:
`@A1[x_ge_v]`, `@A2[x_ge_v]` (`red`, minting `x_ge_v`), `@E1[...]`, `@E2[...]` (the halves of
`B = l + S`), `@L[x_ge_v]` (the rung), `@S[<cake label>]` (a cake row with `B -> l + S`),
`@Q<p|n|t|f|a|b>[<atom>]` (an atom's value as a clause), `@D1[s]`, `@D2[s]` (a selector `s`
defined as a flag), `@W[n]` (a candidate a pin cites), then each of baguette's rows under its
own `@cN` (`ia` or `rup`), and the proof has **no `f` line**. Each `soli` is labelled
`@O[c<id>]` and `@c<id>` derived from it by the objective's half (D-0182).

**T3b (D-0188)** adds, still fresh names in the sense baguette's `.opb` uses: `@Ep[e]`,
`@Em[e]` (an INTERIOR eq atom `e = [x = v]` as `x_ge_v - x_ge_(v+1)`, each one `pol` of the
atom's definition and its ge atoms' clauses), `@Y1[y_ge_v]`, `@Y2[y_ge_v]` (`red`, a gcc copy's
rung defined as its original's; `@L[y_ge_v]` follows from them), and pins written as ONE `pol`
under the row's own label when a cake row LINEARISED at the row (each `B_z` cancelled by
`@A1`/`@A2` at the row's threshold or by z's bound row, saturated, its atoms replaced) is the row
itself: element's clauses, maxmin's per-value clauses (the operands' `[r]` rows so linearised,
plus `@c[N][al1]`), member's and inverse's range clauses. A `@cN pol` pin is the row exactly;
any other is still `ia` against a `@W`. A substitution `@S[...]` is written only when a pin
cites it, or before a `rup` pin of its constraint.

**T6 (D-0195)** adds the translator's three far families. `int_times` and `int_div` are not
covered (refused before the search). **regular**: the translator leaves mznlib's state flags out
of the `.scp` (they are existential in `fzn_regular`) and renumbers the states by
`pi(q) = (q - q0) mod Q`, cake's NFA starting in 0; an edge `(smin + j  pi(d))` per non-zero entry
of row q of the flattened table, finals `pi(F)`. The prefix DEFINES each flag `s(i,q)` (baguette's
`s_ge_1`, fresh) as cake's `x[c<k>][<i>_<pi(q)>][st]` by a red pair `@D1[s]`, `@D2[s]`, and swaps it
in as a selector; the layer rows, the start and the accept row are `ia`, a forward clause over a
symbol run `ia` (one value) or `rup` through the transition clauses and the letters' eq atoms
(`@Qn` at an end of the range, `@Ep` inside). **cumulative**: each capacity row of baguette at t is
`ia` against ONE `pol`: `@c[N][cap_<t>]` plus, per covering task with `r_i > 0`, `@c[N][<i>_<t>_cge]`,
`r_i` times `@c[N][<i>_<t>_actcal1]`, and `r_i` times each flag's clause `@K[v[N][<i>_<t>][cb]]`
(`cb + s_ge_(t+1) >= 1`, one `pol` of its `[f]` row and `@A2` at t + 1, saturated; at t + 1 past
the range its bound row, the unit) and `@K[v[N][<i>_<t>][ca]]` (`ca + ~s_ge_(t+1-d) >= 1` with
`@A1`; at or below lb, the unit). **int_abs**: baguette's sign guard `S <-> x >= 0`, a model Boolean
with no `.scp` counterpart, is DEFINED as `x_ge_0` by `@D1`, `@D2`; a row no candidate implies (the
rows true in both signs, the hull, the guard's own rows) is derived **by contradiction**:
`@cN pbc ROW : subproof`, then `pol -k <candidate> + s ;` for each of the constraint's four
candidates and `rup >= 1 ;`, closed by `qed ;`.

**T7 (D-0196)** covers baguette's **bits arm** (`--bits-above`, the bits encoding above). Its
`x_bit_i` are the bits of `x - l`, unsigned; cake's are x's two's complement. Over cake's digits
`u_j` (`i[X][b<j>]` for `j < h`, `~i[X][sign]` at `j = h` when `l < 0`), `U = B + 2^h [sign]` is
unsigned on m digits and `x - l = U - L'` with `L' = l + 2^h [sign] >= 0`, so the digits of
`x - l` are those of `U + c`, `c = (2^m - L') mod 2^m`: a ripple-carry adder whose relation at
digit i is the linear row `d_i + 2 k_(i+1) = u_i + c_i + k_i` (`k_0 = 0`). The prefix writes, per
bits variable (`x` its sanitized name):

| label | rule | what |
|---|---|---|
| `@BK1[x_bitc_<i+1>]`, `@BK2[...]` | `red`, witness `k -> 0`, `k -> 1` | a carry once the previous is a literal: `T - 2k >= 0`, `2k - T >= -1`, `T = u_i + c_i + k_i` (both goals tautologies); while it is a constant the next carry is `0`, `u_i` or `1`, no line |
| `@BP[d]`, `@BN[d]` | `red`, witness `d -> 1`, `d -> 0` | the relation's two halves, defining `d = x_bit_i` (`i < n`) or the high digit `x_bith_i` (`n <= i < m`); goals `@BK2`, `@BK1` |
| `@BPs[x]`, `@BNs[x]` | `pol` | the halves summed with weights `2^i`: `S_all + 2^m k_m = U + c`, telescoped |
| `@BPk[x]`, `@BK[x]` | `pol`, `rup` | the final carry is 1 (`@BPs + @i[X][lb]`), when it is a literal |
| `@BNk[x]`, `@BZ[d]` | `pol`, `rup` | `-S_all >= -(u - l)` (`@BNs + @i[X][ub] + 2^m @BK`), and each high digit 0 |
| `@BE1[x]`, `@BE2[x]` | `pol` | the halves of `B = l + S`, `S = sum 2^i x_bit_i`: the order arm's `@E1`/`@E2` over the bits |
| `@BL[x]`, `@BU[x]` | `pol` | `@BE2 + @i[X][lb]` and `@BE1 + @i[X][ub]`: baguette's two bound rows, each `ia` against its own |

With `l = 0` and no sign every carry is 0 and each pair renames `x_bit_i` to `i[X][b<i>]`. The
substitution of cake's rows (`@S[...]`, `k * @BE2` or `|k| * @BE1`) is then the order arm's. A
guarded row whose big-M is baguette's own, over the declared bounds, where cake's is over the bit
range (`bits_imply`), is derived **by contradiction**: `@cN pbc ROW : subproof`, `pol -1
<candidate> + s ;` (the negation plus the candidate, saturated: a clause over the guards), `pol -2
<a * @BU[y] ...> + ;` (the negation plus each negated bits variable's ub row: no room left for
them), `rup >= 1 ;`, `qed ;`. A choice selector `_mxN` over bits (array_int_maximum/minimum, D-0134)
is defined as cake's flag `F_i` AND no earlier flag, as `sol` sets it (first operand attaining m):
`@C1[s]` `red (i+1) ~s + F_i + sum_{j<i} ~F_j >= i+1 : s -> 0`, `@C2[s]` `red s + ~F_i + sum_{j<i}
F_j >= 1 : s -> 1`, `@D1[s]` `pol @C1` with the earlier flags weakened (the first operand's is a
renaming, `@D1`/`@D2`). An int_abs sign guard over a bits variable is defined as cake's atom
`i[X][ge0]` (its order atom is minted later, by the solver's proof), and the atom's own rows
`@i[X][ge0][f]`, `[r]` are its rows' candidates.

## 4. Per-propagator justification

Each propagator module MUST document, in its header comment, the shape of the proof step
it emits. The table below is the index; it is maintained as propagators land.

| Propagator | Consistency | Justification |
|---|---|---|
| `int_le` | bounds | the instance `1*x + -1*y <= 0` of `int_lin_le`, and therefore `int_lin_le`'s `Combine` (D-0013/D-0015) — **not** the `Cut (Trivial, Linear, 1, 1)` this row claimed until M1-T13 |
| `int_lt` | bounds | the same, at rhs `-1` |
| `int_eq` | bounds | `int_lin_eq` on `x - y = 0`. A domain-consistent version would intersect domains value by value and name the excluded value rather than a bound chain — not built |
| `int_lin_le` | bounds | the explanation is still D-0013/D-0015's `Combine` (the model row, every *other* term weakened away by literal axioms or cited by the id that established it, one division by the pushed coefficient), but since **M8-bits-encoding-T5 (D-0131)** it reaches the page as `rup`, not as the Θ(w)-token `pol` fold: every push, at the root as under a decision, is its D-0018 trace line `rup <claim> ~<facts> >= 1`, which the checker closes by unit propagation along the ladder rows the `.opb` holds (D-0031); a conclusion stated through `Justify.emit_concluding` is `rup <literal> >= 1` for the same reason. The D-0013 `pol` is written only where a derivation is consumed as a ROW by arithmetic: a `Term` operand of another `pol`, a counting family's derivation ahead of its line, a learned PB row (`Pb_analysis.introduce`, where the claim is a row and the `ia` checks the arithmetic). Measured (D-0131): at w = 10⁶ the root refutation of D-0028's model is 138 B of proof against 29.8 MB, its elaboration 132 B against 29.8 MB, and `cake_pb` checks it in 66 s against 77 s; the exact D-0013 row is NOT reachable by RUP (its negation is a cardinality the ladder cannot propagate), the literal is, and the old `ia` of the literal against the D-0013 row was never syntactically implied either — `rup` is the only one of the two forms that could ever state a ladder-walk's conclusion |
| `int_lin_eq` | bounds | two `int_lin_le` derivations |
| `int_ne` | value (domain, in fact) | `rup` over **order**-encoding literals: the claim disjoined with the negation of its reason, which is D-0018's trace-line shape. No direct encoding — see section 3, "Disequalities" |
| `int_lin_ne` | value | the same, over every term. **Over a bits scope (M8-bits-encoding-T3, D-0134 §4)** the nogood is not RUP and is DERIVED as one `pol` (`Explanation.Resolve`): row A of the `_neN` pair with every term's bridge on A's coefficient, saturated (`sel ∨ ~facts`), plus row B with the bridges on the negated coefficients, saturated (`~sel ∨ ~facts'`), summed and saturated so the selector resolves away; both degrees are exactly 1 because the fixed terms sum to c. Pinned by `ia` to the nogood, the `pol` deleted |
| `int_eq_reif` / `int_ne_reif` | value | enforce-hold, and the half of entailment that REFUTES the condition, are `int_lin_le`'s, over the guarded LE/GE rows with the reifier as one more term. The two `Clause` pieces (enforce-not-hold's hole or conflict, and the entailment that pushes the reifier when every term is fixed with the sum on c) are `rup` over the guarded A/B pair and the ladder. **Over a bits scope (M8-bits-encoding-T3, D-0134 §8)** both are the `int_lin_ne` derivation above with the reifier as one more term in each half, on that half's guard coefficient (`−big` when the disequality side speaks at b = 0, `+big` at b = 1) and at the value that denies the equality: `pol @A <bridges> + <b's bridge> big * + s @B <bridges'> + <b's bridge> big * + s + s`, pinned by `ia`. The reifier's bridge is the width-1 tautology. For the entailment the reifier's term carries the negation of the claim, so the pinned clause is the trace clause |
| `bool2int` | bounds | `rup` over its two rows and the integer's ladder (`Bool2int`'s `Clause`s). **Over a bits integer (M8-bits-encoding-T3, D-0134 §9)** the same two rows are posted with an `int_lin_le` instance each, under a face reporting `bool2int`, and every pruning is `int_lin_le`'s bits `pol` |
| `int_times` / `int_div` / `int_abs` | bounds | as `int_lin_le`, over the guarded rows of the case split (D-0060); the case variable of `int_times` is its NARROWER operand since M8-bits-encoding-T3 (D-0134 §10), the second one at a tie |
| `bool_clause` | `Domain` | `rup` |
| `all_different` | domain (stage 1 Hall intervals on bounds, stage 2 Regin on values) | `pol` — the multi-row Hall derivation (D-0027, D-0061, M4-T1/M4-T2): one at-least-one line per Hall variable (narrowed by the channelling and the ladder, or a cited unit where the root established the bound — `Defining`, D-0064), one at-most-one per Hall value recovered from the pairwise `.opb` clause rows, summed to `sum ~y_eq_v >= |..|`. A **bound push** adds the forward channelling clauses of the kept values, which telescope to `~y_ge_lo + y_ge_(b+1)`; the telescope stops at y's DECLARED top, where the residue is the constant false (M7-T22, D-0086). A **value removal** drops the other values by literal axioms, leaving `~y_eq_v`; an INTERIOR removal then adds `y_eq_v \/ ~y_ge_v \/ y_ge_(v+1)` (divisor 1) and concludes the ORDER clause `~y_ge_v \/ y_ge_(v+1)`, the same currency as every other hole and as its trace line, which is what an embedder such as `element`'s `excl_hole` reads (M7-T22, D-0086). A removal at a bound is a bound move and keeps its form. The pigeonhole is a push that empties a domain, never a `rup` conflict line (I-X10, D-0040). No `Clause` in any derivation |
| `element` | domain | `pol` over the per-position rows `~idx_eq_p \/ c >= as[p]` and `~idx_eq_p \/ c <= as[p]` (guards spelled over the ORDER encoding in the `.opb`, recovered to the direct literal by the channelling halves), the result's ladder, and `Encoding.at_least_one_id` -- see `lib/core/prop/element.ml`'s header. Trace lines are `Single_row` and written bare; a pruning that READ a hole carries the hole puncher's facts (D-0075). **M7-T21 (D-0084)** adds three rules: (1) an index hole this instance did not punch, when a derivation needs it, is the clause `~idx_eq_p \/ ~<the puncher's facts>` (RUP against the hole's own trace line) and the bare unit `~idx_eq_p` only when the hole is a level-0 one -- the bare unit under a decision is the 23-of-26 corpus shape `rup +1 ~<v>_eq_<k> >= 1 ;`; (2) every pruning derivation cancels its root-established residue (`Defining`), so a derivation made at the root is exact; (3) an interior index removal's explanation is restated in the ORDER currency `~idx_ge_p \/ idx_ge_(p+1)` through the forward channelling line, because that is what another instance's `excl_hole` pairs off when this index is its result. **M7-T25 (D-0101)**: the empty-index CONFLICT carries its facts under a decision -- per dead position, the result or index bound it lies beyond, the result hole's REMOVER's facts, a deep index hole's puncher's facts -- and is made under `Store.deriving_ahead`, so `Trace.conflict_line` writes its `pol` (the at-least-one line narrowed by every position's exclusion, leaving exactly the negated facts) before `rup ~facts >= 1` and 1UIP learning resolves from it. At the root it stays factless and its `pol` closes to `0 >= 1` |
| `global_cardinality` | checking (bounds-level reasoning) | `pol` over the **order-encoded** counting rows `sum_i (x_i_ge_v - x_i_ge_(v+1)) = c_v - const_v` (no direct encoding is requested, D-0078); a constant count is the degree-side constant of the same row (M7-T18, D-0082). Rule A (interval capacity, the Hall rule generalised) sums one row per cover value of the interval and is **not** RUP against the `.opb` alone (I-X10), so its derivation goes on the page **ahead of** its trace line: the propagator makes the push under `Store.deriving_ahead`, the entry carries `ahead = true`, and `Trace.derive_ahead` writes the `pol` first. **That flag, set by the propagator, is the whole trigger** (M7-T17, D-0082) — it was `Encoding.has_direct` of the pruned variable until then. Rule C (count bounds) is SPLIT (M7-T21, D-0084): the UPPER push is RUP against its value's one `>=` row and is written bare; the LOWER push is **not** RUP against the `<=` row once two or more other scope variables hold the value strictly inside their window (unit propagation cannot sum the ladder rungs that make each indicator non-negative), so it is made under `Store.deriving_ahead` like rule A. A rule C push that EMPTIES the count against a bound the root set past the declared one closes by walking the count's rungs to that bound and citing it (`Defining`) -- rule A's "one more line". **Two single-value rules (M7-T24, D-0099).** (a) a SATURATED value (the x fixed to `v` number `hi(c_v) - const_v`) is removed from every other x: at a bound it is rule A's push over `[v, v]`; strictly inside a window it is the same counting stopped one step early, which concludes the ORDER clause `~x_ge_v \/ x_ge_(v+1)` -- D-0086 (b)'s one hole currency, so an embedder citing it through `Store.remover` needs no bridge -- and it is made **ahead** (with two other variables holding `v` inside their windows the counting row keeps slack, measured: the line alone is refused). (b) a FORCED value (the x whose window holds `v` number exactly `lo(c_v) - const_v`) fixes each candidate, both bounds: rule C's upper derivation with the target's indicator kept and the count's ladder paid from below; RUP against the `>=` row, so written **bare**, and its `pol` reaches the page where a later line consumes it (`gcc_forced_root_unsat`). The reasons name the BOUNDS the counting read, over the variables that declare a value of the interval, and never the trail reasons behind those bounds (D-0099: unfolding them made 2015_roster's proof 1.81 GB) |
| `array_int_maximum` / `array_int_minimum` (and `int_max` / `int_min`, the two-element case) | bounds | `m >= x_i` is `n` ordinary `int_lin_le` rows, justified by `int_lin_le`'s `pol`; the disjunction `m <= max_i x_i` is one `.opb` clause per threshold `v`, `~[m >= v] \/ [x_1 >= v] \/ ... \/ [x_n >= v]` (constant literals folded, vacuous ones not posted), and every pruning and conflict of the `maxmin` instance is `rup` of exactly one of those rows, restated (M4-T9, D-0095). A minimum is the same instance over negated views, so its rows are the mirror over the bases' own literals. **Over a bits variable (M8-bits-encoding-T3, D-0134)** the disjunction is §3's choice group and the same `C_v` is DERIVED as one `pol` (`Explanation.Resolve`): for each operand its selector row, plus `m`'s bridge `B1(m, v)` and `x_i`'s `B2(x_i, x_bound + 1)` with `x_bound = min(v − 1, dhi x_i)` (the declared bound row where that is the bound), divided by `D_i = v − x_bound` and saturated — the clause `~b_i ∨ ~[m >= v] ∨ [x_i >= v]` — then the `n` clauses plus the selector clause, saturated, which resolves the selectors away: `pol @S_1 @B1_m + @B2_x1 + s @S_2 @B1_m + @ub_x2 + 2 d s + @sel + s`, pinned by `ia` to `C_v` and the `pol` deleted. The claim variable's term carries the claim's negation, so the pinned clause IS the trace clause and no atom is added. I-X10: single-row |
| `cumulative` (and `disjunctive`, `disjunctive_strict` as cap 1, r 1) | checking (time-table filtering, bounds-level reasoning) | `pol` over one **order-encoded capacity row per time point** `sum_i r_i (s_i_ge_(t-d_i+1) - s_i_ge_(t+1)) <= cap - fixed load`, ends clipped to the declared range and folded, posted by `Cumulative.make` only where the declared may-load exceeds the capacity -- no auxiliary, no direct encoding (D-0096). A push of task j off t is gcc's rule A with a coefficient per task: the row, `r_i` x the at-least-one of every other task compulsory at t (its bound facts walked onto its window by ladder chains, `Defining` at the root, left in the row under a decision), `r_k` x the free ladder chain `I_k >= 0` of every other task in the row, ONE division by `r_j`, then j's own bound walked onto its window and D-0010's ladder lift (one unit per rung, O(w)). The REASON names only the compulsory tasks and the target, a decision's bound at its window literal (`s >= t-d+1`, `s <= t`: lifted), a root bound at its value and cancelled; the other tasks are cleared in a bound-free sub-derivation. Overload is the same push, past j's own upper bound, closed by that bound (gcc's "one more line"). **Not RUP** against the row once two tasks of the row are neither compulsory nor the target (measured, D-0096), so every push is made under `Store.deriving_ahead` and the `pol` precedes its trace line (I-X10, `Needs_derivation`). No new `Explanation` constructor |
| `diffn`, `diffn_nonstrict` (mznlib, no builtin of its own) | checking (std's pairwise disjunction, plus the time-table of its two cumulative relaxations) | No rows of its own. std's four `int_lin_le_reif` and one `bool_clause` per pair, each justified as its family is; plus `cumulative(x', lb dx, lb dy, Hy)` and `cumulative(y', lb dy, lb dx, Wx)` over ORDER COPIES `c` of the coordinates (two `int_lin_le` rows `c = x`, `Linear` `pol`s), the row above. The capacity rows are MODEL rows: they are consequences of diffn that mznlib states, so the checker trusts them as it trusts every mznlib redefinition (D-0213 section 3, checked by enumeration in test_compile) |
| `regular` (`fzn_regular`, `fzn_regular_set`, as `baguette_regular`) | domain (Pesant's layered graph; `Checking` when a letter repeats) | Over the letters' ORDER literals and `(n+1)*Q` state flags (store Booleans the mznlib route introduces), the `.opb` holds the DFA and nothing else: per layer `ALO_i` and `AMO_i` over its flags, `START` `s(0,q0)`, `ACCEPT` `OR_{f in F} s(n,f)`, and per layer, state and SYMBOL RUN (a maximal stretch of values with identical columns) the forward clause `~s(i,q) \/ x_i notin R \/ s(i+1, d[q,R])`. The backward chains `~s(i+1,q') \/ x_i notin R \/ OR_{d[q,R]=q'} s(i,q)` are ROOT LEMMAS: derived as `rup` by `Encoding.start_proof` before search (never posted, so a wrong one is a refused line), retired by the end-of-run sweep. Every pruning -- a flag killed forward or backward, a letter value with no live edge, a flag fixed as the last live state of its layer -- and every conflict (an empty layer, two flags set in one) is ONE `rup` with its bound facts on the tail: dead flags, the letter's bounds (last), and a hole cited through its remover's facts. I-X10: single-row (the lemmas are lines already on the page). No new `Explanation` constructor: `Explanation.clause`, deferred (M7-T28, D-0146). **Since D-0151 no tail names a flag the propagator moved**: where a line would cite a dead (or set) flag it cites the TAIL of that flag's own earlier trace line instead, so the tails are letter bounds (the weakest bound excluding the values a live state needs cut, the strongest per letter and direction after merging) and hole removers' facts; a flag a decision fixed is cited as itself. Each line stays one `rup`, now against the rows, the lemmas and those earlier lines |
| `inverse` (`fzn_inverse`, as `baguette_inverse(f, fmin, g, gmin)`) | checking (channel filtering, `j in dom(f_i) <=> i in dom(g_j)`), plus `all_different` over each array (domain) | The `.opb` holds std's semantics as CHANNEL clauses over order literals, both directions, each `x = v` split into its two halves: `f_i <> j \/ g_j >= i`, `f_i <> j \/ g_j <= i`, `g_j <> i \/ f_i >= j`, `g_j <> i \/ f_i <= j`, constant halves folded, plus a unit row where a declared domain reaches outside the other index set. A channel pruning is ONE `rup`: its tail is the weakest bound excluding `j` from `f_i` (or a hole's remover facts) LAST, after the pinning bound fact when the claim settles a bound. I-X10: single-row. STAGE 2: compile.ml posts `all_different` over each array of distinct variables (not when the model already does); its pairwise rows `x <> v \/ z <> v` are ROOT LEMMAS (`Encoding.add_cited_lemma`, each `rup` from two channel rows) whose ids `alldiff.ml`'s Hall `pol`s cite through its lemma-row hook. No new `Explanation` constructor (M7-T28, D-0151) |
| `member` (`fzn_member_int`, `fzn_member_bool`, as `baguette_member(x, y, b)`) | domain over x, y and the selectors (`Checking` when a variable repeats among x and y) | The `.opb` holds `OR_k b_k` and, per position, `b_k -> x_k = y` over the OVERLAP [a, b] of the declared hulls: four bound clauses `~b_k \/ [x_k >= a]`, `~b_k \/ ~[x_k >= b+1]` (and y's), and two big-M rows over the overlap's rungs, `sum_{v=a+1..b} ([x_k >= v] + ~[y >= v]) + (b-a) ~b_k >= b-a` and its mirror; constants folded, `~b_k` alone for disjoint hulls (M7-T34, D-0170; until then two clauses per threshold of the overlap, D-0159). These rows propagate the selector and refute two crossing bounds, but no ladder rung (every rung has coefficient 1), so the BOUND-form clauses `~b_k \/ ~[y >= v] \/ [x_k >= v]` and `~b_k \/ ~[x_k >= v] \/ [y >= v]` are now LEMMAS, each a `rup` from its big-M row and the ladders, written only ahead of a line whose argument walks a hole: a selector death across holes (one per switch of the hole's owner between x_k and y, at most one more), a hole carried under a set selector (one), a value of y one live position excludes by a hole (one); none at an end of the overlap, where a bound clause does it. Such a line is made under `Store.deriving_ahead`; its derivation is ONE `pol`: each lemma weakened back out by its literals' axioms, the line's clause scaled by k = 1 + the degree that cost, divided by k -- exactly the clause, cited by later derivations. A selector is a store variable: its death or its setting is a trail entry, and every later reason cites the TAIL of that line instead (D-0151 section 1's rule), so the reasons name x and y only. A value of y that two or more live positions exclude by a HOLE only needs a case split per selector: one lemma `~b_k \/ y <> v \/ ~F_k` per position (a `rup`; a dead position's own death line), then OR plus the lemmas divided by their count, the threshold lemmas weakened in front (D-0159). I-X10: `Needs_derivation` for the hole shapes. No new `Explanation` constructor (M7-T28, D-0159, D-0170) |
| `table` (`fzn_table_int`, `fzn_table_bool`, as `baguette_table(x, t, s)`) | domain over x and the selectors (`Checking` when a variable repeats in x) | The `.opb` holds `ALO: sum_t s_t >= 1` and per tuple ONE row `DEF_t: k ~s_t + sum_i ([x_i >= t_i] + ~[x_i >= t_i + 1]) >= k` over x's order literals, constant literals dropped, the unit `~s_t` when one is constant false (x is held on the order encoding under `--bits-above`, family `table`). A selector is a store variable, as member's. Every pruning is ONE `rup` with its facts on its tail: a tuple's death (K) cites the weakest bound past t_i or the hole's remover; `s_t := 1` (C) and an empty table (conflict) cite the other tuples' tails and rest on ALO; `x_i := t_i` under a set selector (E) cites its tail and rests on DEF_t; `x_i <> v` (S) cites the tails of the dead tuples carrying v and the bound pinning v, and rests on every DEF_t through x_i's ladder and ALO. Every tail cites a dead selector's own tail (D-0151), so the reasons name x only. I-X10: `Single_row`. No new `Explanation` constructor (M18-coverage-T1, D-0206) |
| `circuit` (`fzn_circuit`, as `all_different(x)` plus `baguette_circuit(x, pos, root)`) | checking over (x, pos), plus Chuffed's `prevent` | The `.opb` DEFINES the constraint by Miller-Tucker-Zemlin rows over one position store variable per node other than the root (the root's is the constant 0): with `G(u, v) = n ~[x_u >= v] + n [x_u >= v+1]` the arc's guard over x_u's order literals (x held on the order encoding, family `circuit`; pos expanded as any linear term, so bits by default), `GE(u, v): G + pos_v - pos_u >= 1` and `LE(u, v): G + pos_u - pos_v >= -1` between non-root nodes, `LE(r, v): G - pos_v >= -1` out of the root, `END(u): G + pos_u >= n - 1` into it, plus unit rows for a declared successor outside the node range or equal to its node. A PREVENT pruning (the arc from the end of a chain of fixed arcs back to its start, the chain shorter than n) and a closed short cycle's conflict cite the chain's arcs and rest on the SUBTOUR CUT, one `pol` written ahead (`Store.deriving_ahead`): GE around a cycle avoiding the root, or LE along the path from the root plus END, summed so every position cancels, then `n d`, which leaves `sum(guards) >= 1`. A position pinned along a fixed arc (`pos_v = pos_u + 1` from a pinned pos_u, `pos_v <= 1` out of the root, `pos_u >= n - 1` into it) is one `rup` against one row, its premise pinned on purpose (over bits, unit propagation turns `x >= c` and `x <= c` into every bit). I-X10: `Needs_derivation`. No new `Explanation` constructor (M18-coverage-T3, D-0217) |

### The root conflict *(D-0131 — normative)*

A conflict under no decision is closed exactly as a branch is closed (D-0018 with an empty
decision stack): the root's trace, one line per root pruning, oldest first; the conflict's
own `rup ~fact ... >= 1` when it carries facts; and the empty clause `rup >= 1 ;`, which
`conclusion UNSAT` (or the optimisation run's final `BOUNDS`) cites. The propagator's
derivation is written ahead of the close only where the empty clause rests on it: a
conflict with facts made under `Store.deriving_ahead` (`c_ahead`, the counting families),
and a factless derivation unless it is **one model row with literal axioms added** — a row
violated at its declared bounds, which the checker's propagation refutes unaided, and which
is what `int_lin_le`'s factless conflict always is. Until D-0131 the root had a second arm
that cited the D-0013 `pol` as the contradiction and three predicates to tell the arms
apart; that arm, and the Θ(w) `pol` per cited pruning it recursed into, are gone. What
`conclusion UNSAT` cites is therefore always a line the checker judged by RUP, and a break
that blanks the trace (`test_mutation.ml`'s `blank-trace`, `test_matrix.ml`'s negative
control at every depth) is refused at that line with *"The constraint is not implied by
reverse unit propagation (RUP) from core and derived database."*

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
