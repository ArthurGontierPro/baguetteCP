# Specification

Status: **draft**. This document is normative — the code serves it, not the reverse.
Changes to anything marked *(normative)* require an entry in `docs/DECISIONS.md`.

Keywords MUST / SHOULD / MAY are used in the RFC 2119 sense.

---

## 1. Scope

`baguette` is a constraint programming solver over finite integer and Boolean domains that

1. reads a model in **FlatZinc**,
2. searches for a solution (or proves none exists, or proves optimality),
3. emits a **VeriPB proof** that an independent checker accepts. The format is
   VeriPB **3.0, and only 3.0** (D-0023 chose it, D-0025 made it the default, D-0046
   removed everything else); there is no format switch. The checker is VeriPB **3.0.2**,
   the Rust build, and it is the only one — D-0046 records what losing the second
   implementation costs. `scripts/checker.sh` is the single place that resolves which
   binary runs. A lane asserting a rejection must assert the checker's **wording**, not
   just a non-zero exit: an exit status cannot tell a judgement from a parse error, and
   four lanes were found passing on the latter (M2-T14).

The proof is not a debugging aid. It is a primary output: a run that produces a correct
answer with an unverifiable proof is a **failed run**. *(normative)*

### Out of scope (for now)

Floats, sets of integers, `var set of int`, reified float constraints, search
annotations beyond those listed in §3.4, and multi-objective optimisation.

---

## 2. Input: FlatZinc

### 2.1 Accepted subset *(normative)*

The solver MUST accept FlatZinc 2.x files restricted to:

**Types**: `bool`, `int`, `var bool`, `var int`, `array[int] of ...` of those.
Integer variables MUST have a finite declared domain. A `var int` with no domain is
rejected with a diagnostic; it is not defaulted to a machine-word range.

**Builtins**, by milestone (see `docs/ROADMAP.md`):

| Milestone | Builtins |
|---|---|
| M1 | `int_lin_le`, `int_lin_eq`, `int_lin_ne`, `int_le`, `int_lt`, `int_eq`, `int_ne` |
| M2 | `bool_clause`, `bool2int`, `bool_eq`, `bool_not`, `array_bool_or`, `array_bool_and` |
| M3 | reified forms: `int_lin_le_reif`, `int_eq_reif`, `int_le_reif`, `int_ne_reif` |
| M4 | `all_different_int`, `int_abs`, `int_times`, `int_div`, `array_int_element` |
| M5 | `int_lin_le` with an objective; `minimize` / `maximize` |

Encountering a builtin outside the implemented set MUST produce a clear error naming the
builtin and exit non-zero. It MUST NOT silently ignore the constraint. *(normative)*

**Arithmetic limit** *(normative)*. The solver computes over a fixed-width machine
integer, so there are FlatZinc models it MUST refuse rather than answer. For every posted
linear row, the magnitude

    M = |rhs| + sum_i |a_i| * max(|lo_i|, |hi_i|)   over the declared domains

and every declared bound MUST be checked against an implementation limit, and a model
exceeding it MUST be rejected with a positioned diagnostic naming the limit, exiting
non-zero. It MUST NOT be accepted and answered.

This refuses models the FlatZinc standard allows, which is why it is normative here and
carries a decision record (**D-0029**). The alternative is not "accept more models", it is
"answer some of them wrongly and prove it": the `.opb` row and the propagator are computed
from the *same* arithmetic, so on overflow they wrap identically, the proof is a valid
proof of a model that is not the one on disk, and the checker accepts it. M1-T23
demonstrated exactly that. A wrong answer with a verified proof is the one outcome this
project exists to make impossible, so the limit is normative rather than an
implementation detail.

The limit's *value* is not fixed by this specification — only that one exists, that it
bounds every product and partial sum the propagators and the `.opb` expansion compute, and
that exceeding it is a refusal rather than an answer. This limit is about **overflow**, not
about proof size; the separate question of a *width* cap is open and is not decided here
(see D-0028).

**Integer division, modulo and absolute value** *(normative)*. `int_div(x, y, q)` and
`int_mod(x, y, r)` are **relations**, not functions, and this specification fixes two
things about them that are easy to get wrong in opposite directions.

*Rounding.* `int_div` truncates **toward zero**, and `int_mod`'s remainder takes the sign
of the **dividend**. So `int_div(-7, 2, q)` has the single solution `q = -3`, not `-4`, and
`int_mod(-7, 2, r)` has `r = -1`, not `1`. The identity `x = y * q + r` with `|r| < |y|`
holds for every solution. This matches MiniZinc's `div`/`mod` and is not negotiable by an
implementation, because it decides which assignments are answers.

*Division by zero is relational, not an error.* A model containing `int_div(x, y, q)`
where `y`'s domain includes 0 MUST NOT be rejected, and MUST NOT abort when the search
reaches `y = 0`. The value 0 simply has **no support** in the divisor: no triple
`(x, 0, q)` satisfies the relation, so `y = 0` is pruned like any other unsupported value,
with a justification like any other pruning. A model whose only solutions would require
division by zero is therefore UNSAT, and MUST be reported as UNSAT with a proof — not as
an error. The same holds for `int_mod`.

*A bound is not the relation.* The rounding above says which triples are solutions. It does
**not** say how to round when computing a *bound*. Bounds round **outward** — floor for a
lower bound, ceiling for an upper one — whatever the relation does, because a bound must not
exclude a supported value. These two roundings disagree on negative operands, and an
implementation that uses the relation's rounding to compute a bound prunes values that have
support. See **D-0033**.

`int_abs(x, z)` is total and needs no such rule, but note that `|min_int|` is not
representable; it falls under the arithmetic limit above.

A second, unrelated limit applies to declared **width** rather than magnitude. It is a
different decision with a different justification and a different exit code; see §3.1 and
**D-0041**.

### 2.2 Output format

Solutions are printed on stdout in the standard FlatZinc output format: the variables in
the `output` annotation, one assignment per line, terminated by `----------`; `==========`
after the last solution when the search space is exhausted; `=====UNSATISFIABLE=====`
when the model has no solution.

**How a value is rendered** *(normative)*. Until now this section gave the line shape and
the markers but never said what goes on the right of the `=`, so the rule lived only in
`lib/flatzinc/output.ml` and in `test/expected/bool_out_sat.out`. It is stated here
because it is a requirement on the solver's output, not an implementation detail:

- A value is rendered under the **declared type of its output item**, not under the shape
  of the value. A `bool` MUST print as `false` or `true`; an `int` MUST print as a decimal
  numeral. These are not interchangeable: `1` and `true` are the same assignment printed
  under two different types, and only the declaration says which.
- An array item MUST print as `array<k>d(<range>, ..., [<elements>])`, with `k` the number
  of dimensions, one `l..u` index range per dimension in order, and the elements in
  row-major order as a single flat bracketed list, each rendered by the rule above.
- Each output item occupies exactly one line, `name = value;`, newline-terminated. There
  is no blank line and no trailing space anywhere in a solution block.

This is the FlatZinc standard's rule, not a choice of this project's, which is why it is
recorded without a decision record: nothing was decided here, the specification was
merely silent where the code and the FlatZinc standard already agreed. The consequence
for the implementation is the one M1-T21 had to fix — a `bool` *parameter* folded to a
constant has lost its type by the time it reaches the printer, so the declared type MUST
be carried to the printer rather than inferred there.

---

## 3. Solver semantics

### 3.1 Domains

An integer variable's domain is a finite set of integers. The representation MUST support
lower/upper bound access in O(1) and membership in O(1); hole removal MAY be O(size).
See `docs/ARCHITECTURE.md` §2 for the chosen representation.

**Declared width is a cost the proof pays, and since D-0041 this specification caps it.** A
variable's *declared* domain is what the proof artefacts are sized against, not its current
one: §4.2's encoding gives it one Boolean and one consistency clause per interior value,
and every row it appears in expands to one literal per interior value. Both artefacts are
therefore Θ(declared width) per variable before the search has done anything at all — and
this holds even for a model that is refuted on its declared bounds having pruned nothing.

**A declared width limit** *(normative — D-0065, 2026-09-22, which amends D-0041; D-0041
in turn superseded the "no such limit exists" of D-0028 part 3 and D-0031)*.

The solver **MUST NOT silently answer** a model whose declared width makes its proof
impractical. That requirement is unchanged and is the durable half of D-0041.

**The solver MUST NOT refuse such a model by default.** A declared domain exceeding an
implementation-defined **reporting threshold** MUST produce a diagnostic on stderr naming
the variable, its width, and the clause count it minted. The diagnostic MUST NOT appear on
stdout, and stdout MUST be byte-identical with and without it.

An implementation MUST provide a means of **restoring** the refusal. When a limit is in
force, a model exceeding it MUST be rejected with a positioned diagnostic naming the
variable and the limit, exiting non-zero as a model error rather than an invariant failure.

**Why this amends D-0041 rather than overriding it.** D-0041 forbade a run-time knob on
this ground, and the objection was correct as stated:

> a knob would make the accepted language environment-dependent, so two runs of the same
> binary on the same `.fzn` could disagree about whether it is a legal model, which is the
> one thing a normative statement must not allow.

The amendment answers it rather than ignoring it, because **the default is now unlimited**.
The accepted language is therefore *fixed and maximal*: every legal FlatZinc model is
accepted by a default build, and two default runs always agree. The knob can only
**restrict**, which makes it an operator's self-imposed resource budget rather than part of
the language. D-0041's own arrangement was in fact the weaker one on its own terms — the
accepted language depended on a **compiled-in constant**, so two *builds* could disagree
about legality, with no way for a reader to see which constant was in force.

What D-0041 was really protecting is that a reader must never be unable to tell why a model
was refused. That is preserved: the refusal names the limit and says it was asked for.

**A declared width that is not representable as a native integer is refused
unconditionally, and no option disables it.** This is an arithmetic refusal in the family of
§2.1's overflow cap, not a resource budget: the ladder does not exist to be built. *A limit
that exists because the machine is small is an option; a limit that exists because the
arithmetic does not exist is not.*

This deliberately accepts models whose *artefact* may be unusable. The model is legal and
the answer is correct; what may be unacceptable is the proof, and the diagnostic is how the
user learns that before discovering it at the checker. The limit remains separate from
§2.1's arithmetic limit **in justification, in value, and in the exit code it reports**.
That one refuses models whose arithmetic cannot be *computed* and is a soundness
requirement; this one bounds models whose proof cannot be *stored*. §2.1's limit bounds
width only incidentally, at 5.7 × 10^17.

### 3.2 Propagation

The engine runs propagators to a fixpoint. A propagator MUST be:

- **Sound**: it removes only values that appear in no solution of its own constraint,
  given the current domains.
- **Checking**: when all its variables are fixed, it MUST report failure iff the
  assignment violates its constraint.
- **Idempotent at the interface**: re-running a propagator on unchanged domains MUST
  produce no further change. (The implementation need not be internally idempotent.)

A propagator is *not* required to be domain-consistent. The consistency level of each
propagator MUST be documented in its module header, because it determines what its
explanations may claim.

**`Bounds` means bounds(Z), not bounds(D)** *(normative, added 2026-09-21)*. A propagator
declaring `Bounds` MUST leave each variable's `lo` and `hi` supported when the *other*
variables range over their **intervals** — their bounds read as a contiguous range, holes
ignored. It is **not** required to find support within the actual domains.

Two reasons this is the reading, both checkable rather than stylistic. `docs/GLOSSARY.md`
defines `Bounds` as saying **nothing about interior values**, which forces the interval
reading. And under bounds(D) the harness of M2-T10 would report `Linear`, `Int_le`, `Int_lt`,
`Pb` and `Bool2int` as violations — **none of which is a bug**. The distinction was
unspecified until the per-node consistency oracle made it load-bearing; it is now tested
directly (`test/unit/test_consistency.ml` lane 4 and its control, on a scene where the two
readings genuinely differ).

### 3.3 Explanations *(normative)*

Every domain change and every failure carries an `Explanation`. An explanation is a
*reason* in a form that can be turned into a proof step.

The explanation type is defined in `lib/core/explanation.ml`. It is the single most
important type in the codebase; see `docs/ARCHITECTURE.md` §4.

**Requirement**: for any pruning `p` with explanation `e`, the proof step derived from
`e` MUST be accepted by VeriPB in the proof state at the moment `p` occurs. This is
checked empirically by the test suite, and is the property that all the design pressure
in this project is aimed at.

### 3.4 Search

**Default.** A model with no search annotation is searched by first-fail variable selection
with min-value branching, depth-first, restarts disabled.

**Annotations** *(normative; the honouring requirement predates M7-T2, which brought the
implementation into compliance with it)*. `int_search` and `bool_search` with the variable
choices `input_order`, `first_fail`, `smallest` and `largest`, and the value choices
`indomain_min`, `indomain_max` and `indomain_split`, and `seq_search` over those, MUST be
honoured.

- `input_order` selects the first still-unfixed variable **in the order the annotation's
  array wrote it**, not declaration order.
- `smallest` selects the unfixed variable with the smallest **current domain minimum**;
  `largest` the one with the largest **current domain maximum**. Both read the live domain,
  not the declared one.
- `indomain_min` branches `x = lo` first; `indomain_max` branches `x = hi` first.
- `indomain_split` bisects at the **range midpoint** — `x <= mid` first, then `x > mid` —
  where `mid` is computed from the current bounds. It is defined on the range and not on the
  value count, so on a domain with holes the midpoint may itself be a hole; that is correct
  and is not a degenerate case.
- `seq_search` consults its annotations in order and uses the first whose variables are not
  all fixed. A phase whose array contains only fixed elements contributes no decision and is
  skipped, which is this clause rather than an exception to it.

**A constant in a search array is skipped, not refused** (M7-T7). Flattening produces them
routinely, and a search over an array never branches on a fixed element, so skipping is what
honouring the annotation means here. An array of only constants is a legal empty phase.

**Variables no annotation mentions.** An annotation need not cover every variable. When every
annotation's variables are fixed and a decision is still required, the default above is used.
This is the one respect in which an annotated model's search is not the annotation.

**Anything else MUST be refused**, with a diagnostic naming it — including
`anti_first_fail`, `indomain_median`, `indomain_random`, `float_search`, `set_search` and
`priority_search`. It MUST NOT be silently ignored or replaced: **substituting a strategy
solves a different problem and reports it as this one's answer.** Before M7-T2 an
unrecognised annotation was silently dropped and the model searched by the default, which is
exactly what this forbids.

`indomain_median` is refused for a structural reason and not merely because it is unbuilt,
and its diagnostic says so. A decision here is a **single order literal** — `x <= k` on one
side, `x >= k+1` on the other. `indomain_min` and `indomain_max` are exact under that only
**by accident of sitting at the domain boundary**: `x <= lo` *is* `x = lo`, and `x != lo`
collapses to the single literal `x >= lo+1`. For an interior value `m`, `x = m` needs two
literals and its sibling `x != m` is a **disjunction** (`x <= m-1 OR x >= m+1`) — which is
precisely what the one-trail-entry-per-level and single-resolution-literal invariants exist
to exclude. Honouring it therefore requires a second decision shape and a change to the
nogood-resolution contract (roadmap M7-T12), not a fifth value-choice constructor. **Refusing
is the compliant answer**; a near-equivalent substitution would satisfy this section's letter
and violate the sentence above it.

**The `int_search` exploration argument (`complete`, `bbs`, `lds`) is ignored**, and that is
sound rather than an omission: the search is complete, so ignoring an incompleteness
annotation can only explore *more* of the tree than asked, never less. The answer and the
proof stay honest.

Every branching decision and every backtrack MUST be reflected in the proof.

---

## 4. Output: the proof *(normative)*

### 4.1 Artefacts

A run with `--proof PREFIX` writes two files:

- `PREFIX.opb` — the pseudo-Boolean encoding of the model
- `PREFIX.pbp` — the proof, whose first line is exactly
  `pseudo-Boolean proof version 3.0`. There is no other format and no switch (D-0046);
  `docs/PROOF-FORMAT.md` section 2a is the contract, and its section 2 is the historical
  record of the 2.0 that used to sit beside it.

Both files carry the labels that let the proof cite a model row by name, and they must
agree about that or the checker stops at the grammar without judging anything.
`Encoding.write_opb` is the only way to write the `.opb`, so they cannot disagree.

Both are required; VeriPB is invoked as `veripb PREFIX.opb PREFIX.pbp`.

### 4.2 Encoding

Integer variables are encoded with the **order encoding**: for a variable `x` with
declared domain `[l, u]`, Boolean variables `x_ge_v` for `l < v <= u`, together with the
consistency clauses `x_ge_(v+1) -> x_ge_v` for `l < v < u`.

**The consistency clauses MUST be in the `.opb`, and MUST be there for every declared
variable** *(normative)*. They are not an optimisation and not a convenience for the
solver: no proof step this solver emits ever cites one, and the checker needs them all the
same. A model row is this encoding's own expansion, in which every literal of one variable
carries the same coefficient, so a row constrains only *how many* of `x`'s literals hold.
Nothing but the consistency clauses ties "`x_ge_k` holds" to "at least `k - l` of them
hold", and without that the reverse-unit-propagation checks that carry every pruning in
this project do not close. Measured: strip them from the shipped models' `.opb` files and
7 of 20 proofs are rejected, in each case at the first trace line. Deferring them into the
proof by `red` is possible and is a *pessimisation*; `docs/PROOF-FORMAT.md` §3 records the
witness that works and what it costs, and **D-0031** records the decision.

Direct-encoding literals `x_eq_v` are introduced **only** for the variables that need them
— `element` and `all_different` (M4) — with channelling constraints, lazily, into the
proof rather than the `.opb`. **A disequality does not need them**: `x <> v` is a *clause*
over two ordinary order literals, which is all a `rup` target ever needs (D-0019). This
sentence used to name disequalities among the users of the direct encoding; that was
wrong, it was corrected in `docs/PROOF-FORMAT.md` §3 by M1-T9, and this is the same
correction reaching the normative document at last.

The full encoding contract, including variable naming, is in `docs/PROOF-FORMAT.md`.
Naming is normative: the checker output is read by humans debugging failures, and stable
names are what make that possible.

### 4.3 Conclusion

Order is fixed and all three lines are required:

```
output NONE
conclusion <claim>
end pseudo-Boolean proof
```

`output` is mandatory — omitting it makes the checker reject the proof — and `end` must be
exactly that text.

| Answer | Conclusion |
|---|---|
| SAT | `conclusion SAT` — requires a previously logged solution **and** that deletion checking was never switched off. `conclusion SAT : <assignment>` states the assignment inline instead. |
| UNSAT | `conclusion UNSAT`, optionally `conclusion UNSAT : <cid>` naming the contradiction. Without the id the checker searches its database for one. |
| OPT | `conclusion BOUNDS <lo> [: <cid>] <hi\|INF> [: <assignment>]` |

**`BOUNDS` requires the `.opb` to carry a `min:` objective line**; without one the checker
raises `InvalidProof`. The optional `<cid>` names a constraint implying the lower bound,
saving the checker a search.

---

## 5. Non-goals that are easy to drift into

- Being fast before being verified. Milestone order in `docs/ROADMAP.md` is deliberate.
- Supporting all of FlatZinc. The subset in §2.1 is the target.
- Inventing a proof format. If something cannot be expressed in VeriPB, that is a
  finding worth writing up, not a reason to extend the format locally.

---

## 6. Open questions

Tracked as `OPEN` entries in `docs/DECISIONS.md`. The significant one at the time of
writing is **D-0003: what "higher-order explanation" means for this project** — it has
two live readings and they lead to different code. Resolve it before M3.
