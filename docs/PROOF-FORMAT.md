# The VeriPB contract

Everything `baguette` emits and the vocabulary it is allowed to use.
Checker on this machine: `~/.local/bin/veripb`, proof format **version 2.0**.

---

## 1. Files

```
PREFIX.opb     the model, in OPB format
PREFIX.pbp     the proof
```

Verified with `veripb PREFIX.opb PREFIX.pbp`. `scripts/verify_proof.sh` wraps this and
is what the test suite calls.

The proof's first line MUST be exactly:

```
pseudo-Boolean proof version 2.0
```

## 2. Rule vocabulary

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

Four things this document previously got wrong. The first two are the dangerous ones,
because they corrupt ids rather than producing an error you would notice:

1. **An `.opb` line with `=` counts as TWO constraints** for the `f` rule — the checker
   splits it into `>=` and `<=`. Get the count wrong and every later id is shifted, so
   `pol` steps silently reference the wrong constraints. `Opb.n_checker_constraints`
   computes the header count the checker's way; `Encoding.add_constraint` refuses `Eq`
   outright and `Encoding.add_equality` emits the two `>=` lines explicitly, returning
   both ids.
2. **`sol`, `solx`/`v` and `soli`/`o` differ in id accounting**: `sol` adds no constraint,
   the other two each add one. Treating them as interchangeable desynchronises our id
   counter from the checker's.
3. **`#` is not a comment or section marker.** It is the set-level rule and takes an
   integer; `#` followed by prose is a parse error. Only `*` introduces a comment.
4. **Deletion takes an identifier kind**: `del id N`, not `del N`. Same for `delc` and
   `core` (`id` / `range` / `find` / `spec`).

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

Use **levels**, not individual deletions. `# <level>` sets the current level, everything
derived afterwards is tagged with it, and `w <level>` wipes every constraint at or above
that level in a single rule. One proof line per backtrack instead of one `del` per reason
— which matters because the alternative makes the proof grow with the size of the search
rather than with the interesting part of it.

`w` on a level that was never set is an error (*"Tried to wipe level N that was never
set"*), so levels must be opened before they are wiped. That mirrors the solver's own
decision levels exactly, which is the point.

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
