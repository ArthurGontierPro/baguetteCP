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
| `int_le` | bounds | `pol` — single model constraint, unit |
| `int_lin_le` | bounds | **target**: `pol` — the model constraint plus order-encoding units, one division. **M1 emits** `rup` of the stated bound: a literal in a `pol` is the trivial axiom `lit >= 0`, so bound facts need constraint ids the explanation cannot yet carry (D-0009) |
| `int_lin_eq` | bounds | two `int_lin_le` derivations |
| `int_ne` | value | `rup` over direct-encoding literals |
| `bool_clause` | — | `rup` |
| `all_different` | *TBD* | Hall-set reasoning; see M4 and D-0004 |
| `element` | *TBD* | M4 |

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
