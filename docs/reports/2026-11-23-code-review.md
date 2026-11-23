# Code review of baguette, 2026-11-23

The user asked for a complete and critical review of `main` at `c8be4d0`. This file records what the
review found and leaves the work as rows of `docs/ROADMAP.md`, milestone **M22-review**. T1 and T2,
the two bugs, are fixed and merged (section 1). T3 to T13 are proposals for the node session to apply
in the order of section 2. A row marked USER DECISION changes the solver's default behaviour and waits
for the user, as CLAUDE.md requires.

How the review was done. Every module of `lib/` and `bin/` was measured. The core was read (store,
engine, explanation, justify, trace, search, learning, retention), along with the proof side
(encoding, writer), the front end and `bin/main.ml`. A differential fuzz then ran 1,540 small models
through MiniZinc, baguette against Gecode, with VeriPB checking every baguette proof and Gecode
re-checking every baguette solution. The fuzz and a few probes ran on the laptop, which
`scripts/README.md` section 1 forbids. That was the reviewing session's mistake. The harness is now in
`tools/fuzz/`, whose header says to run it on a node.

## 1. The two bugs, fixed

### 1.1 A wrong answer that VeriPB verified (M22-review-T1)

```
var 0..1: x :: output_var;
constraint int_lin_le([2305843009213693952, 1], [4, x], 0);   % 2^61*4 + x <= 0 has no solution
solve satisfy;
```

baguette printed `x = 0;`, the `.opb` row was `+1 ~x_ge_1 >= 1`, and `veripb` answered
`s VERIFIED SATISFIABLE`. `builder.ml`'s `lin_terms` moved the constant operand to the right-hand
side with an unchecked `r - coeff * n`. The product 2^61·4 wraps to 0 in OCaml's 63-bit `int`, so the
term vanished before `compile.ml`'s cap measured the row, and `Model.check_assignment` checked the
same rewritten model. This is the failure `lib/core/checked.ml`'s header and SPEC 2.1 call the worst
outcome, reached through the only fold of the front end that skipped `Checked` (`lin_fact` in the same
file and `compile.ml`'s folds used it). No test put a large coefficient on a constant operand.

The fold now goes through `Checked.sub` and `Checked.mul`, and an overflow refuses the model with a
positioned diagnostic that names the limit (exit 2, the builder's diagnostic path). Every model that
does not overflow is unchanged byte for byte. The unit test is T3, because `test/unit/` is claimed by
M18-coverage-T1.

### 1.2 cumulative missed an overload among fixed tasks (M22-review-T2)

```
predicate baguette_cumulative(array [int] of var int: s,array [int] of int: d,array [int] of int: r,int: b);
var 0..9: x0 :: output_var;
constraint baguette_cumulative([x0,1,0],[1,1,2],[1,1,1],1);
solve satisfy;
```

The tasks at 0 (duration 2) and at 1 (duration 1) both use time 1, so there is no solution. baguette
pushed `x0` past time 1, accepted `x0 = 2` and stopped on `INTERNAL -- a propagator is unsound (I-P1)`
with exit 4. The fuzz found it through `disjunctive`, and it fails the same way with fixed variables
as starts or with negative times. `Cumulative.make` set `ground` only for a row with no movable term.
When fixed tasks alone overloaded a time that a movable task could also cover, the row kept that
task's terms with `avail < 0` and was false, but `pass` only reads times inside each movable task's own
window, so nothing reported it. That broke I-P3 at the declared `Checking` level, and the solution
check I-S1 is what kept it from printing a wrong answer.

`make` now records the first such row and `propagate` reports it on the first run. The derivation is
the row plus each task's free `I_k >= 0` (`drop_summands`), which closes to `0 >= -avail`. The `.opb`
is unchanged, so the `--e2e` pins are too. Two regression models cover both shapes of the
refutation: `cumulative_fixed_overload_unsat` (a `pol` with ladder rungs) and
`cumulative_fixed_overload_edge_unsat` (a row false on its own, closed by unit propagation).

### 1.3 The gate

Run on fataepyc-07 (booked for baguette by the user on 2026-11-23, while fataepyc-06 ran the node
session's benchmarks), with the steps of gate 90 at `-j 16` and `DUNE_JOBS=16`, in
`/scratch/arthur/m22review/` there. The baseline is hub main `6684fd0`, whose solver is `c8be4d0`'s,
built on the same node. Its md5 `83b863f8` is gate 90's binary.

| Step | Result |
|---|---|
| `make check` | rc 0, 34 s, peak RSS 157 MB |
| 209 models against the baseline | 6 artefact differences, all on the two new models (`.out`, `.rc`, `.pbp`; the old binary stopped on exit 4); both new proofs `VERIFIED UNSATISFIABLE` |
| `make diff --tier all` | rc 0, 347 of 347 runs equal the reference (110 s) |
| `make diff --debug --tier all` | rc 0, 333 of 333 runs equal the reference (554 s) |
| `make scaling` | rc 0, every line within its threshold (41 s) |

New binary md5 `c60418f4`.

### 1.4 What the fuzz covered

| Stream | Models | Flags | Result |
|---|---|---|---|
| random constraints, at most 6 variables and 5 constraints | 600 | default | 599 agree, 1 is bug 1.2 |
| the same generator | 300 | `-f --bits-above none` | 300 agree |
| at most 10 variables and 12 constraints | 360 | default and `-f` | 360 agree |
| 3-SAT near the threshold, small integer optimisation | 280 | default, `-f`, `--bits-above none` | 280 agree, 164 with at least 10 conflicts |

The constraints drawn were linear and reified rows, Boolean connectives, `*`, `div`, `mod`, `abs`,
min and max, element over constant and variable arrays, alldifferent, global_cardinality,
cumulative, disjunctive, regular, inverse, member, count, `in`, lex_less and table, over domains
within −4..4. Every proof verified. The first three streams decide most models at the root (34 of a
sample of 40 in the third were UNSAT with at most 2 conflicts), which is why the fourth exists.

## 2. Proposals, in the order to apply them

"Byte-identical" below means the gate's model comparison shows 0 artefact differences and both diff
lanes equal their references. Every row gets a gate before it merges.

### T3. The unit test for T1 (after M18-coverage-T1 releases `test/unit/`)

In `test/unit/test_flatzinc.ml`: the model of 1.1 is refused by `Builder.of_string` with a message that
names the limit; a fold that does not overflow but leaves the right-hand side above `Checked.limit` is
refused by `compile.ml`'s cap; constant products that are large but cancel (`[2^60, -2^60]` on
`[2, 2]`) are accepted, because exact arithmetic got them right.

### T4. Facts in CLAUDE.md and the README

Every session loads `CLAUDE.md`, and its context-budget table is off by a factor of 2.5 to 15.

| File | CLAUDE.md says | Measured on `c8be4d0` |
|---|---|---|
| `docs/` | 340 KB | 2.5 MB |
| `WORKLOG.md` | 68 KB | 634 KB |
| `docs/DECISIONS.md` | 126 KB | 1.9 MB |
| `docs/ROADMAP.md` | 46 KB | 367 KB |
| `docs/PROOF-FORMAT.md` | 30 KB | 74 KB |
| `docs/INVARIANTS.md` ("short on purpose") | 6 KB | 18 KB |
| `docs/SPEC.md` | 14 KB | 34 KB |
| `docs/ARCHITECTURE.md` | 8 KB | 21 KB |

Replace the sizes by the command that prints them (`wc -c`), so the table cannot drift again. Other
stale facts are listed below.
- alldifferent is "BOUNDS consistent" in the module map and the README, but `alldiff.ml:297` declares
  `Domain`.
- The model count is 85 in CLAUDE.md, but 209 after T2.
- CLAUDE.md lists 22 test binaries, but there are 24.
- CLAUDE.md gives `propagator.ml` as 51 lines, but it has 218.
- The section saying `dune runtest` does not build the solver is obsolete, because
  `test/unit/dune` depends on `bin/main.exe`.

### T5. Three latent defects, each with a test

- `Encoding.declare_int_gen` (`encoding.ml:1413`) treats a redeclaration with equal bounds as a no-op
  without comparing the holes or the representation. So `declare_int_with_holes` after `declare_int`
  silently drops the holes. It signals the no-op with `raise Exit`, caught by a wrapper that shadows
  the function (`encoding.ml:1503`, and 1603 for bits). That wrapper would also swallow an `Exit` from
  any callee. Compare the holes and the representation, and return an explicit result instead of
  `Exit`.
- `Domain.of_list` (`domain.ml:286`) and `Domain.change_of` (`domain.ml:216`) have no caller in
  `lib/`. `trace.ml:475-487` records that `of_list` breaks proofs when it has one. Move both to a test
  helper.
- A write error on the proof (`Sys_error`, a full disk) has no handler in `bin/main.ml`, so the run
  ends on an uncaught exception, with exit 2, possibly after the answer was printed. Catch it, name the
  file, say the proof is incomplete as `warn_partial_proof` does, and exit with `exit_resource`.

### T6. Comments that are false, and the rule for module headers

These comments are false today:
- `domain.ml:185` says the engine calls `classify` once per trail entry on its hot path. It does not.
- `bin/main.ml:198`, the `--proof-comments` help, describes M4 as future work.
- `bin/main.ml:2208-2212` says nothing in `builder.ml` mentions `Checked`. It did before T1, in
  `lin_fact`, and does now in `lin_terms`.
- `encoding.ml:537` says the library has no other shared mutable state. It has 56 top-level mutable
  globals (T11).
- `retention.ml:75` keeps an old paragraph under "THAT PREMISE IS SPENT".
- `domain.ml:55-60` keeps `Domain.change` beside `result` because `store.ml` "was not this round's to
  edit". The two-line change it describes can be made now.
- `lexer.ml:3-7` gives "dune-project is owned by another session" as the reason for a hand-written
  lexer. The lexer is measured and fast, so keep it, with its real reasons.

The rule is that a module header states the current rule, its invariants and its cost in a few lines. What
the code used to be, which task changed it and what was measured belong in DECISIONS.md and the git
log. The tree has 19,076 comment-only lines for 23,053 lines of code, with 1,853 `D-0xxx` and 1,677
task-id references. Apply the rule to each file as it is touched, starting with the five with the
most comment: `search.ml` (2,094 comment lines for 1,632 code lines), `encoding.ml`, `compile.ml`,
`engine.ml` and `writer.ml`. Comments only, so the result is byte-identical.

### T7. The differential fuzz as a lane

`tools/fuzz/` holds the review's harness as it ran (`fuzz.py`, `fuzz2.py`). It writes its own `.msc`
for the binary under test (`FUZZ_BIN`). It needs `minizinc`, which is not on `PATH` on the nodes
(`bench/challenge/README.md`). Make it `scripts/fuzz_lane.sh`, with fixed seeds, the four streams of
1.4 at `-j 16` on fataepyc-06, and every disagreement kept. It is not a gate at first: a bug it finds
becomes a regression model in `test/models/`. Things to add to it:
- the table builtin of M18-coverage;
- a check that the solutions printed under `-i` improve monotonically;
- `--time-limit` stops whose proof verifies as `NO CONCLUSION`;
- a stream of models declared wider than 2^20 values (the hole-decline path of `domain.ml:74`).

### T8. Interfaces for the five central modules

There is no `.mli` in the tree. Rules like "only `Justify` writes and reads a node's `line`"
(`explanation.ml:327-333`) or "nothing else may read `Encoding.live`" (`encoding.ml:535`) exist only
as comments, and `trace.ml:300` reads `store.Store.marks` directly. Write `.mli` files for `Store`,
`Explanation`, `Justify`, `Writer` and `Encoding`. Expose what other modules use, add an accessor where
a field is read across modules, and hide the rest. Byte-identical.

### T9. Test machinery out of the production modules

Move each of these to its own module or behind a single value that defaults to off:
- `Writer.Mutation` and the `corrupt_*` functions (`writer.ml:243-318` and `1158-1375`, about 280
  lines) go to `lib/proof/mutation.ml`.
- The six `break_*` fields of `Search.config` and `backjump_on_pb` become one `faults` record that
  defaults to none.
- `Element.break_hole_facts` (`element.ml:990`).
- The brute-force consistency oracle (`engine.ml:1509-1760`) goes to `lib/core/oracle.ml`.
- `BAGUETTE_TEST_VALUE_CHOICE` is read where the CLI builds the order, not inside
  `Search.search_core` (`search.ml:3719`).

This is byte-identical. `lib/proof/e2e.ml` (2,494 lines) is a product feature and stays.

### T10. Split the long functions

`Compile.compile` (`compile.ml:887`) is one function of 1,695 lines. Split it into one function per
constraint family. Make `parse_args` (`main.ml:449`, 473 lines) table-driven. Split
`Builder.build_constraint` (374 lines) per family as well. Byte-identical.

### T11. Process-wide state into explicit values (after T8)

There are 56 top-level mutable globals: 14 in `encoding.ml`, 11 in `explanation.ml` and 10 in
`engine.ml`. Do these first:
- Move `Encoding`'s limits, row sink and e2e request (`encoding.ml:421-790`, `976-1107`) into a
  configuration given to `Encoding.create`.
- Give the hash-consing table (`explanation.ml:596-634`) to a per-solve value held by `Justify.ctx`.
- Move the statistics counters into a stats record.

The goal is that two solves in one process share nothing and tests stop resetting globals by hand.
Byte-identical.

### T12. Performance, measured before anything changes

For each item, profile on the lane, make the change, measure before and after with the diff and
scaling lanes, and write a D-record. Link the work to M20-pernode and M21-memory.

- Learned clauses are one engine instance each. On a satisfiable random 3-SAT (170 variables, ratio
  4.26), the results were:

  | Solver | Result |
  |---|---|
  | Chuffed | solved in 0.012 s, 665 failures |
  | Gecode | solved in 0.5 s, 3,821 failures |
  | baguette | 2,386 conflicts in 3 s (2,942 with `-f`), no solution; 105 learned-clause instances run per node, of which 2.8 pruned |

  A clause store inside the engine with two watched literals, as SAT solvers keep it, is the usual
  answer.
- Each conflict runs three analyses (1UIP, decision closure, PB). It writes the branch trace, the
  conflict line, bridges where a settle needs them, a level-0 clause and a decision nogood. Measure
  each one's share of the time and of the proof's bytes before changing any.
- The learned database is never reduced by default (`retention.ml:607`, `keep_all`). D-0185's Challenge
  series counted 198 proofs over the 16 GB cap and 314 refusals at the heap budget. Measure `lbd` and
  `tiered` with the default search at the Challenge scale. Changing the default is a USER DECISION.
- `alldiff.ml:49` runs the O(n·d²) Hall-interval enumeration, which its header calls an experiment for
  small domains. Replace it with Puget's or López-Ortiz's O(n log n) algorithm.
- Removing an interior value copies the domain's bitset (`domain.ml:250`), so removing every hole of
  one domain along a branch is quadratic in its width. Measure how often it happens on the Challenge
  first.
- The engine has no propagator priorities (`engine.ml:1893`). Dirty instances run in id order, then a
  FIFO. Try running clauses and linear rows before the globals.

### T13. Where a proof goes by default (USER DECISION)

A run without `--proof` writes and keeps `./MODEL.opb/.pbp`, and a MiniZinc run writes
`./baguette-proof.opb/.pbp`, overwriting the previous ones. Two MiniZinc runs in one directory
therefore overwrite each other's proofs. `bin/main.ml:415-438` says so, and says the directory is
still the user's to confirm.

| Option | Consequence |
|---|---|
| Keep it as it is | simplest. Parallel MiniZinc runs in one directory corrupt each other's proofs, and files of several GB land wherever the user runs |
| Direct runs as now, MiniZinc runs to `./baguette-proof-<pid>.opb/.pbp`, path on stderr | no overwriting, "every run keeps its proof" (SPEC 1) still holds, and the files accumulate |
| A unique name under `$TMPDIR` or a cache directory, path on stderr | nothing in the project directory, but files out of the user's sight |

The recommendation is the second option.

## 3. What holds up

- No exception handler in the tree catches every exception.
- The core uses checked arithmetic consistently.
- `Model.check_assignment` handles every constraint constructor explicitly, with no catch-all case. It
  is what kept bug 1.2 from printing a wrong answer.
- Every fuzzed proof verified, under both encodings and both searches.
- `--e2e` against CakeML's encoder is the defence against bug 1.1's kind of failure.
