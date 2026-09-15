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
   VeriPB **3.0** (D-0023); 2.0 is still what is emitted by default while the test
   suite is migrated, and `BAGUETTE_PROOF_FORMAT` selects between them.

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

### 2.2 Output format

Solutions are printed on stdout in the standard FlatZinc output format: the variables in
the `output` annotation, one assignment per line, terminated by `----------`; `==========`
after the last solution when the search space is exhausted; `=====UNSATISFIABLE=====`
when the model has no solution.

---

## 3. Solver semantics

### 3.1 Domains

An integer variable's domain is a finite set of integers. The representation MUST support
lower/upper bound access in O(1) and membership in O(1); hole removal MAY be O(size).
See `docs/ARCHITECTURE.md` §2 for the chosen representation.

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
- `PREFIX.pbp` — the proof, beginning with `pseudo-Boolean proof version 3.0`, or
  `2.0` while that remains the default. The two are separate grammars, not options on
  one; `docs/PROOF-FORMAT.md` sections 2 and 2a are the respective contracts.

Both are required; VeriPB is invoked as `veripb PREFIX.opb PREFIX.pbp`.

### 4.2 Encoding

Integer variables are encoded with the **order encoding**: for a variable `x` with domain
`[l, u]`, Boolean variables `x_ge_v` for `l < v <= u`, with the consistency clauses
`x_ge_(v+1) -> x_ge_v`. Direct-encoding literals `x_eq_v` are introduced **only** for
variables that need them (disequality, element, all-different), with channelling
constraints.

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
