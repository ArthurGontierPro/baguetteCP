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

**A declared width limit** *(normative — D-0041, which supersedes the "no such limit
exists" of D-0028 part 3 and D-0031)*. The solver MUST NOT silently answer a model whose
declared width it cannot encode. Every declared domain MUST be checked against an
implementation limit on `hi - lo`, and a model exceeding it MUST be rejected with a
positioned diagnostic naming the variable and the limit, exiting non-zero. It MUST NOT be
accepted and answered, and **the limit MUST NOT be adjustable at run time** — a knob would
make the accepted language environment-dependent, so two runs of the same binary on the
same `.fzn` could disagree about whether it is a legal model, which is the one thing a
normative statement must not allow.

This refuses models the FlatZinc standard allows, and that is deliberate: the model is
legal and the answer would be correct; what is unacceptable is the artefact. The limit is
separate from §2.1's arithmetic limit **in justification, in value, and in the exit code it
reports**. That one refuses models whose arithmetic cannot be *computed* and is a soundness
requirement; this one refuses models whose proof cannot be *stored*. §2.1's limit bounds
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

Default: first-fail variable selection, min-value branching, depth-first, with restarts
disabled. `seq_search`, `int_search` with `input_order`/`first_fail` and
`indomain_min`/`indomain_max` MUST be honoured when present.

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
