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

| Rule | Meaning | Used for |
|---|---|---|
| `f` | number of model constraints loaded | proof preamble |
| `pol` (`p`) | cutting-planes derivation in reverse Polish | the workhorse: most propagator justifications |
| `rup` (`u`) | reverse unit propagation | prunings whose reason is clausal |
| `red` | redundance-based strengthening | introducing definitions (reified vars, direct-encoding channelling) |
| `del` / `d` | delete constraints by id | retiring reasons on backtrack |
| `delc` | delete a core constraint | rare; objective updates |
| `core` | move constraints to core | after a solution improves the bound |
| `sol` / `soli` / `v` | log a solution | SAT answers, objective improvement |
| `o` | log an improving solution | optimisation |
| `obju` | update objective | optimisation |
| `a` | add a constraint assumed-checked | **forbidden in release builds** — debugging only |
| `*` / `#` | comment / section marker | readability of emitted proofs |
| `conclusion` | final claim | every proof ends with one |
| `end` | end of proof | last line |

`pol` syntax is reverse Polish over constraint ids: `pol 3 4 + 2 d` means "constraint 3
plus constraint 4, divided by 2". Literal axioms are written `~x1` / `x1`.

**Rule**: prefer `pol` over `rup`. A `pol` step states the actual reasoning and is cheap
to check; `rup` makes the checker search. A propagator that can only produce `rup` should
say so in its module header and explain why.

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

Introduced lazily, only for variables that a disequality, `element` or `all_different`
propagator touches:

```
x_eq_v        for l <= v <= u       meaning  x = v
```

channelled to the order encoding by, for each `v`:

```
x_eq_v  <->  x_ge_v  /\  ~x_ge_(v+1)
```

emitted with `red` as a definition. Exactly-one over `x_eq_*` follows from the
channelling and MUST be derived, not assumed.

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
| `int_le` | bounds | `pol` — single model constraint, unit |
| `int_lin_le` | bounds | `pol` — the model constraint plus order-encoding units, one division |
| `int_lin_eq` | bounds | two `int_lin_le` derivations |
| `int_ne` | value | `rup` over direct-encoding literals |
| `bool_clause` | — | `rup` |
| `all_different` | *TBD* | Hall-set reasoning; see M4 and D-0004 |
| `element` | *TBD* | M4 |

## 5. Backtracking and deletion

Reasons logged during search are deleted on backtrack, in reverse order of introduction.
Failing to delete does not make a proof wrong, but makes it grow without bound and makes
checking quadratic. `BAGUETTE_PROOF_AUDIT=1` asserts the live-id set is empty at
`conclusion`.

## 6. Debugging a rejected proof

1. Run with `--proof-comments` — every rule is preceded by a `*` comment naming the
   propagator, the decision level, and the pruning.
2. `veripb --trace` shows the rule that failed.
3. Shrink: `scripts/shrink.sh MODEL` re-runs with propagators disabled one at a time to
   find which one emits the bad step.

Do not "fix" a rejected proof by switching the step to `rup`, or by using `a`. A rejected
step means the propagator pruned something it could not justify — that is a soundness bug
in the propagator until proven otherwise.
