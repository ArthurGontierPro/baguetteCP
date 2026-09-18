# bench/ — the proof benchmark

Task M3-T5, which absorbs M3-T3, extended by **M2-L8** to the learning counters. This
directory holds a measurement tool. It is **not part of `make check`** and must not
become part of it: it takes minimums over repeated
sequential runs, which is slow by construction, and a timing number has no business
failing a build.

```sh
bench/run_bench.sh                       # every model in test/models/, one configuration
bench/run_bench.sh -r 9 test/models/width_root_unsat.fzn
bench/run_bench.sh -c                    # THE CONTROL (M2-L8, §7) -- asserts, exits non-zero
bench/run_bench.sh -S other/main.exe -b layered     # two solver builds
bench/width_curve.sh                     # the D-0028 shape at w = 9, 99, 999, 9999
bench/run_bench.sh -h                    # all the options

bench/explanation_size.sh                # M2-T17: explanation SIZE, per model (see section 3d)
bench/explanation_size.sh -c             # THE CONTROL for it (bench/control/size/) -- asserts

baguette MODEL.fzn --proof P --time      # the same internal numbers, one model, by hand
```

`--time` writes its report to **stderr**, one `time: <phase> <microseconds> us <what it
is>` line per phase, and is off unless asked. It changes no byte of stdout, of the `.opb`
or of the `.pbp`; the harness verifies that before it measures anything (§1, "the
self-checks"). One row, `emitln`, is a **count** and carries a `lines` unit instead of
`us` — deliberately, so that anything matching on `us` cannot read it as a duration.

There **is** a `make bench` target now (`make bench ARGS="..."`), and it is correctly not
a dependency of `check`. `Makefile` belongs to the orchestrator, not to `bench/`; as of
2026-09-18 its comment above that target still offers `ARGS="-F 2.0"` as the example, and
that flag no longer exists — D-0046 removed the format it selected and M2-L8 removed the
flag. Raised as a cross-session request rather than edited from here.

---

## 1. What it reports, and why they are separate columns

There are now **three tables**, printed one after the other for each configuration. The
first is wall-clock time around whole processes; the second is the solver's own account
of where its time went, read back from `baguette --time` (M1-T35); the third is what
conflict analysis did, read from `baguette --stats` (M2-L8). The first two are printed
side by side rather than one replacing the other, because **the comparison between them
is the measurement** — it is what says how much of a row was `exec`.

### The wall-clock table

| column | what it is |
|---|---|
| `.opb B` | bytes of the problem statement the proof is about |
| `.pbp B` | bytes of the proof |
| `verify ms` | how long the checker of record takes to accept it |
| `slvMB` / `vrfMB` | peak RSS of the solve and of the verify |
| `solve ms` | how long the solver takes, apart from the checker |
| `lvl` | search-tree proxy — see §4, it is **not** a node count |
| `lines` / `longest` / `rup` / `pol` | the proof's shape |

### The internal table (M1-T35)

Microseconds of **CPU time inside the solver process**, from `Sys.time`. Measured on
dedicated runs with `--time`, *outside* the timed repeats — exactly as the peak-RSS pass
is — so the wall-clock table is still produced by the binary invoked the way it was
before `--time` existed, and stays comparable with the baseline below. The repeat with
the smallest total is reported whole, so the phases add up to `inmain` rather than being
per-column minimums of runs that never happened together.

| column | what it is |
|---|---|
| `wall us` | the `solve ms` column above, in microseconds, for reading against |
| `startup` | CPU before `main`'s first statement: `exec`, dynamic link, OCaml runtime, module init |
| `parse` | argument handling + `Builder.of_file` |
| `compile` | `Compile.compile`: store, engine, encoding. No I/O, no proof |
| `opb` | `Encoding.write_opb`: the `.opb` built, written and closed |
| `propag` | `Search.solve` **minus** the proof emission inside it (M1-T47). An **upper bound** on propagation and search |
| `emit` | of the same `Search.solve`, the time inside `Writer`'s own output calls. A **lower bound** on emission |
| `clkovh` | the measuring clock's own cost: one calibrated `Sys.time` read per emitted line, landing **once in `emit` and once in `propag`**. Subtract from both |
| `emitln` | lines the writer wrote during `search` — what `clkovh` is computed from |
| `pbp` | proof channel opened, `Encoding.start_proof`, and the final `.pbp` flush |
| `rest` | printing the solution, plus whatever in `main` is in no phase |
| `inmain` | `startup` excluded; the sum of `parse`…`rest`, exactly — and `propag` + `emit` is exactly the old `search`, so the sum did not change |
| `notslv%` | `(wall − inmain) / wall` — an **upper bound** on the share of `solve ms` that is not the solver's own work |

Three things travel with those numbers and are printed under the table every run, not
just recorded here:

- **CPU time, not wall time.** `bin/dune` links no `unix`, so `Sys.time` is the only
  clock `bin/main.ml` can reach — and it is the better instrument anyway, because it
  excludes the descheduling this file warns about four sessions deep. Measured, not
  assumed: `Sys.time`'s smallest non-zero delta here is **1 µs**, and
  `/proc/self/schedstat`'s — the obvious alternative, which reports nanoseconds — is
  **1.9 ms**, because the scheduler only updates it at its own tick. It cannot see a
  400 µs parse.
- **`notslv%` is a bound, not a figure.** `wall` and `inmain` are different clocks and
  CPU time is never above wall time, so `wall − inmain` over-states the overhead. It is
  labelled an upper bound wherever it appears.
- **`search` is split, and both halves are bounds** (M1-T47, §3b). `emit` is the time
  spent inside `Writer`'s output calls; the time spent *building* each rule's body —
  `Pol.to_string_cited`, `Opb.constr_to_string`, the `Printf.sprintf` at each call site —
  is spent before the writer is entered and lands in `propag`. So `emit` is a **lower**
  bound on emission and `propag` an **upper** bound on propagation, and both are printed
  with those words on them. **"Propagation costs at most X" is now a sentence this
  harness supports. "Propagation costs exactly X" is not, and will not be until the
  rendering is inside the accumulator too.**
- **Subtract `clkovh` before quoting `emit` or `propag`.** It is the instrument, not the
  program: one `Sys.time` read per emitted line, and `Sys.time` is
  `CLOCK_PROCESS_CPUTIME_ID`, a real syscall at ~0.65–0.75 µs here rather than a vDSO
  read. On `width_sat_depth` it is **350 µs of an 805 µs `emit`**. That is why it is a
  column: a reader quoting the raw `emit` as the cost of writing a 545-line proof would
  be wrong by a factor of 1.8, and nothing in the number would say so. It is calibrated
  per run — minimum of nine 256-read bursts, taken in the report *after* every other
  number has been read, so the calibration lands in no phase.

### The learning table (M2-L8)

One row per model, from the solver's own `--stats` counters — **not** read back out of
the `.pbp`. It rides the same dedicated `--stats` pass the tree columns come from, so it
costs no extra run.

| column | what it is |
|---|---|
| `.opb B` / `.pbp B` / `verify ms` | repeated from the first table, deliberately |
| `learn` | 1UIP clauses derived and stated at level 0 (M2-L3) |
| `conv` | …of which `Learned.to_linear_row` accepts. **An opportunity, not a saving** |
| `skip` | siblings a backjump did *not* explore (M2-L3). A `0` here is a real zero |
| `pbtry` / `pblrn` / `pbfall` | PB conflict analysis asked / succeeded / fell back (M2-L6) |
| `fb%` | `pbfall / pbtry`, integer percent. `n/a` when `pbtry` is 0 |
| `pbstrng` | learned PB rows that convert where the same conflict's clause does not |

The three proof columns are **repeated rather than summarised**, and that is the whole
design of this table. M2-L8 exists because learning is the one change in this solver that
can move `.pbp` bytes without moving the search tree *and* move the search tree without
moving `.pbp` bytes. Five quantities on one line is the only arrangement in which a
reader can watch that happen. There is no total column, for the same reason there is none
in the first table.

Under the table, **suite totals** — and only of the *counts*. The bytes and the seconds
are never summed: a sum over models of different sizes is an arbitrary weighting. A model
whose binary reported no learning counters at all is counted in **none** of the sums and
is named separately, because a missing measurement must not be able to read as a zero.

### The self-checks

Before anything is measured, the harness checks three properties of the binary it is
about to measure. Each is a property its own columns rest on, and the first two were
false in this tree until 2026-09-16.

1. **`.opb` bytes do not depend on the path the model was given** (M1-T37). Loud `FAIL`
   and a non-zero exit, but not a refusal: inside one invocation both configurations use
   the same path, so deltas stay sound, and `-S old/main.exe` against a build from before
   the fix has to remain possible. What breaks is comparing the bytes with someone
   else's.
2. **`--time` is invisible to everything else**: the report reaches stderr, stdout is
   byte-identical with and without it, the `.opb` and `.pbp` are byte-identical, and
   nothing appears unless the flag is given. **Fatal**, and nothing is measured: SPEC 2.2
   pins solution output byte for byte and `test/expected/*.out` is ground truth (I-M1),
   so a solver contaminating stdout is not one to take numbers from.
3. **The emission accumulator actually counts** (M1-T47). An accumulator that had come
   disconnected — a gate left shut, a new funnel added to `Writer` that nobody
   instrumented — reports `emit 0` and `propag = search` on every row. That is not a
   visible failure: it is the pre-M1-T47 table with an authoritative-looking column
   bolted on, which is strictly worse than no column. So the harness runs an
   **emission-heavy** model, one whose `.pbp` is written line after line during the
   search (`width_sat_depth`: 545 lines, 29.9 kB, 196 level markers), and requires
   `emitln > 0`, `emit > 0` and `emit <= search`. **Fatal**, and nothing is measured.

   If that model is not among the ones being measured and cannot be found beside them or
   in `test/models/`, the check is **skipped with a notice saying the split went
   unexercised**. A near-zero `emit` on a handful of small models is not evidence in
   either direction, and a column nobody has watched move must not read as a tested one.

Both ways of disconnecting the accumulator were tried — `Writer.emitted_us` returning a
constant 0, and the CLI leaving `Writer.time_emission` shut — and both come out as:

```
  FAIL  the emission accumulator is not counting: emit is 0 us over 543 emitted
        lines -- the accumulator counted nothing.
```

A binary that rejects `--time` as an unknown option is not a failure — it is an older
build, the internal table is skipped with a note, and the wall-clock table is complete.
A binary that takes `--time` but reports no `emit` row predates M1-T47: the emission
columns are **blanked with `-`, not filled with `0`** — a zero in a column called `emit`
says "emission is free", which is a claim an absent measurement must not be able to make
— and the footer keeps the old "*propagation costs X* is not supported" wording for it.

**The first draft of check 2 was itself the failure it exists to catch**, and breaking
the solver on purpose is how that was found. It decided "does this binary support
`--time`?" by looking for a `time: process` line *on stderr*. With the whole report
deliberately redirected to *stdout* — the worst thing this file can be wrong about — it
concluded "no `--time` support", skipped the quietness check as inapplicable, printed a
benign `note`, and exited 0. The detection now turns on the argument parser's own answer
(`unknown option: --time` **and** a non-zero exit, and nothing else counts), and the
check asserts the report is present on stderr before it asserts anything about stdout.

**There is deliberately no total and no score.** The reason is the finding in
`docs/GCS-COMPARISON.md` §4: GCS measured a **5.9× smaller** proof that took **3.5×
longer** to check, *at an identical search tree*. Size and verify time are not two views
of one quantity. A benchmark that adds them, or that reports only size, will approve a
change that made checking three times slower — and this project has a roadmap row
(M1-T25, lazy order-encoding atoms) whose entire purpose is to shrink the `.opb`, so that
mistake is one commit away rather than hypothetical.

Peak RSS is the fourth number because on this machine it is the resource that fails
first. See §5.

## 2. How it avoids reporting noise

This project has retracted a speed claim twice — D-0023's 17–29× that did not move the
suite clock, and D-0025's correction of *that* — and M1-T24 produced a genuine null
result that was correctly reported as one. The harness is built so that the third time is
harder:

- **Minimums, never means.** A mean folds in whatever else the machine was doing. The
  minimum of *n* sequential runs is the closest this gets to the work itself.
- **One at a time.** Nothing here runs in parallel. Four Claude sessions build in this
  checkout at once, so the harness prints the load average and **warns** when it is above
  0.5, because a benchmark run beside a `dune build` is measuring the `dune build`.
- **The spread is printed next to every timing.** `+-%` is `(max − min) / min` over the
  repeats: the measured noise floor for that number, on this machine, today. **A
  difference no larger than the spread is noise.** In comparison mode the harness applies
  that rule itself and prints the word `noise` next to any delta inside the larger of the
  two spreads, per column.
- **A process floor is measured and printed in the header — and, since M1-T35, measured
  a second time from the inside.** Both timings in the first table are wall time around a
  whole process. The solver invoked with no arguments costs **4.0–4.5 ms** here and the
  checker asked for its version **4.6 ms**, so a model reported at 8 ms is mostly `exec`.
  That used to be the end of the sentence, and it is the reason M3-T5 reported a null
  result. It is no longer: `--time` reports `startup` — the CPU consumed before `main`'s
  first statement — from inside the same process, and the two agree in the only way they
  can, with the CPU figure (~2.4–2.9 ms) below the wall floor (4.5 ms), since CPU time
  never exceeds wall time. **The floor is now subtracted rather than merely warned
  about.**
- **Byte counts are checked for reproducibility.** Every repeat's `.opb` and `.pbp` sizes
  are compared; a model whose proof is not byte-identical every time is flagged `!! proof
  bytes NOT reproducible across repeats` rather than quietly reported. (Today every model
  is stable.)
- **A rejected proof gets no timings at all.** If the checker refuses the proof the row
  says `REJECTED` and reports nothing else. Timing an unaccepted proof measures nothing.
- **The checker and the format are read, not assumed.** The checker comes from
  `scripts/checker.sh` (`Checker.find`'s shell twin — no path is hardcoded here) and is
  printed with its version. The proof format is still read back out of **each `.pbp`'s
  own version line** and printed, even though D-0046 left only one format to read: it is
  a check on the artefact, not a knob, and D-0023's lesson is that the artefact is the
  authority. There is no longer any way to *ask* for a format from this harness — `-f`
  and `-F` are gone with the format they selected.

One consequence of the last point, found while writing this: the first draft counted
`rup` and `pol` lines with `grep ' rup '`, and so counted **0** of a proof whose every
derived constraint carries a label (`@c9 rup ...`) — a benchmark reporting a confident
zero for a proof full of the thing it was counting. That is D-0025's vacuously-true
assertion wearing a benchmark's clothes. The counts use `^(@[^ ]+ )?rup `, the shell
transcription of `Writer.strip_label`, and the script says so where it does it. The
optional prefix stays optional: nothing here may assume one spelling.

## 3. Baseline, 2026-09-16 (wall clock, 18 models, before `--time` existed)

VeriPB 3.0.2 (`~/.cargo/bin/veripb`), emitted format 3.0, minimum of 7 runs, one at a
time, WSL2 / 12 cpu / 15.8 GB. Process floor 4.0 ms solver, 4.6 ms checker.

This is the table M3-T5 shipped and the one §3a answers. Its `.opb` column is measured
through the pre-M1-T37 header and so carries the length of the paths that run typed; the
`.opb` figures in §3a are 60–80 bytes smaller for that reason alone and the difference is
not a change in the encoding.

```
model                      .opb B     .pbp B  solve ms    +-% verify ms    +-%   slvMB   vrfMB longest lines   rup   pol  lvl
array_sat                     882        187       7.0    51%       7.1    34%       4      10      88     6     0     0    0
bool_out_sat                  235        136       7.0    21%       7.3    63%       4      10      32     7     0     0    1
chain_sat                    2319        931       7.8    13%       7.4    36%       4      10     215    26    14     0    4
guess_wrong_sat               910        678       7.5     9%       7.4    21%       4      10      74    22    10     0    4
lin_ne_sat                    665        186       7.5    39%       7.3    66%       4      10      68     8     0     0    2
lin_sat                       630        203       7.6    41%       7.6    43%       4      10      84     8     0     0    2
lin_unsat                     627        276       7.1    19%       7.4    12%       4      10      59     9     0     3    0
ne_conflict_sat               496        333       7.1    26%       7.7    20%       4      10      36    16     4     0    4
ne_eq_unsat                   313        369       7.7    37%       7.2    54%       4      10      36    16     7     0    3
ne_prune_sat                  250        128       7.1    37%       7.3    18%       4      10      32     7     0     0    1
ne_sat                        276        118       7.1    13%       7.1     9%       4      10      32     6     0     0    0
ne_self_unsat                 241        120       6.7    17%       7.2    10%       4      10      32     6     1     0    0
offset_unsat                  572       1635       7.6    13%       7.5    38%       4      10      51    52    31     0   11
trivial_sat                   203        129       6.7    43%       7.2    45%       4      10      32     7     0     0    1
trivial_unsat                 205        137       7.2    22%       7.4    37%       4      10      32     6     0     1    0
width_narrow_unsat           1070        303       8.7    33%       8.8    70%       4      10     195     6     0     1    0
width_root_unsat           126010      23891      38.8    16%      13.0    24%       9      18   23779     6     0     1    0
width_sat_depth             16153      29859      17.8    25%      19.2    23%       7      10    1670   545   293     0  196
```

**Read this table as two facts and a warning.**

1. Every pre-existing model is at the process floor in both timing columns, with spreads
   of 9–66%. **Those are not timings of anything.** Nothing about the solver's or the
   checker's speed can be concluded from fifteen of these eighteen rows, and any future
   change that claims a speed effect on them is claiming it about `exec`. *(This was
   stated here as a permanent limitation of the instrument. It is not one any more, and
   §3a says by how much: measured from inside, those rows are 84–96% not-the-solver, and
   the solver's own share of them — 0.37 to 1.6 ms — is now a number you can read.)*
2. The three `width_` models (M1-T30) are the only rows that measure work: 38.8 ms and
   13.0 ms at spreads of 16% and 24%, against floors of 4.0 and 4.6. They exist because
   until today the widest declared domain in the suite was `var 0..9`.
3. `width_root_unsat` and `width_sat_depth` have **almost the same `.pbp` size and
   nothing else in common**: 6 lines against 545, one `pol` against none, 0 `rup` against
   293, no decisions against 196 level markers. This is precisely why the tree proxy and
   the shape columns are here. A benchmark reporting one size number could not tell those
   two apart, and they have opposite fixes.

*(A format-2.0 comparison stood here until D-0046 removed that format from the project.
Its finding is preserved in D-0023 and in the decision record, and is not re-measurable:
the code that emitted 2.0 is gone. The timing half of it was a null result in any case —
every delta came back inside the spread and was labelled `noise`.)*

Width curve (`bench/width_curve.sh`, the D-0028 shape, zero prunings at every width):

```
w         .opb B     .pbp B  solve ms  verify ms  slvMB  vrfMB  longest line
9           1006        303       8.2        8.0      4     10           195
99         11548       2287      10.8        8.0      6     10          2177
999       125950      23891      38.7       13.1      9     18         23779
9999     1359952     257895     363.1       62.0     32     42        257781
```

The `.opb` and `.pbp` are linear in *w* and match D-0028's independently-measured table.
`solve ms` grows faster than either; `verify ms` grows more slowly. Three numbers, three
behaviours, which is the whole argument for three columns.

## 3a. What was inside the floor: the same suite, measured from the inside (M1-T35)

Same machine, same checker, minimum of 7, 29 models (the suite grew from 18). **Load
average was 2.27 — four sessions were building — and it shows in the `wall us` column,
which is 1–2 ms above the 2026-09-16 table for identical work.** That is the point of
this section rather than a caveat to it: the wall column moved because the machine moved,
and the CPU columns did not.

```
model                    wall us   startup    parse   compile       opb    search      pbp    rest    inmain  notslv%
array_sat                   8428      2442      108        78       378        55       79      19       717      91%
bool_and_sat               13727      2595      104        81       179       124      104      23       615      96%
bool_array_sat             12300      3054      161       151       331       124       82      25       874      93%
bool_channel_sat           12674      2996      183       142       637       117      127      30      1236      90%
bool_channel_unsat         17268      3636      127       137       397       237      257      29      1184      93%
bool_clause_sat             8633      3680      244       171       316       208      263      45      1247      86%
bool_eq_sat                 9784      2920       85        74       254       142      121      21       697      93%
bool_not_sat                8366      2510       78        67       171        94       79      19       508      94%
bool_or_sat                 8153      2421       81        80       177       131      100      20       589      93%
bool_out_sat                8734      2585       91        52       152        53       62      30       440      95%
bool_reif_unsat             8695      2453       92       118       219       181       93      19       722      92%
chain_sat                   9743      2519       98       394       564       392       94      21      1563      84%
guess_wrong_sat             9631      2706      112       131       303       248       94      23       911      91%
lin_ne_sat                  8506      2424       80        93       273        70       84      25       625      93%
lin_sat                     9089      2414       80        74       236        84      144      22       640      93%
lin_unsat                   8731      2670       91        74       243        64       60      12       544      94%
ne_conflict_sat             8841      2657       82        85       198       101       59      15       540      94%
ne_eq_unsat                 8062      2543       69        85       170       111       74      14       523      94%
ne_prune_sat                8369      2612       93        77       215        58       95      22       560      93%
ne_sat                      8649      2399       64        65       176        43       75      16       439      95%
ne_self_unsat               8562      2462       67        53       157        25       57      11       370      96%
near_limit_ne_sat           9222      2560      107       141       502       186       97      97      1130      88%
near_limit_unsat            8441      2515       83        81       231       270       69      13       747      91%
offset_unsat                8909      2576       88        73       227       385       88      16       877      90%
trivial_sat                 9757      2813       85        55       205        54      111      21       531      95%
trivial_unsat               9326      2625       66        41       159        47       84      14       411      96%
width_narrow_unsat          9580      2842      109       142       504        81      109      18       963      90%
width_root_unsat           42668      2425       83     13660     18765      5161      513      30     38212      10%
width_sat_depth            21350      2684      120      1340      5451      5051      189      27     12178      43%
```

**The before/after on the rows that sat at the floor.** `trivial_sat` was reported at
6.7 ms. Of that, 2.8 ms is CPU before `main`'s first statement and **0.53 ms is the whole
of the solver's work** — parse, compile, `.opb`, search, proof, print. `ne_self_unsat`:
0.37 ms. `chain_sat`, the largest of the small models: 1.56 ms. Twenty-six of
twenty-nine rows are **84–96% not the solver**, and the residue is not a rounding error
on a 7 ms number, it is three orders of magnitude of dynamic range that the wall-clock
column was hiding. M3-T5's null result was right, and this is the measurement it asked
for.

**Where the work actually is, on the rows that have any.**

- `width_root_unsat`: 38.2 ms of real work, only 10% of its wall time lost to the
  process. **18.8 ms of it is writing the `.opb`** and 13.7 ms is `Compile.compile`.
  `Search.solve` — a model with zero prunings — is 5.2 ms. So nearly half of this model
  is proof *statement*, before a single proof *step* is emitted, which is D-0028's shape
  seen on the clock instead of in bytes.
- `width_sat_depth`: 12.2 ms of work. 5.5 ms `.opb` **plus** 5.1 ms in `search`, where
  the 545-line, 29.9 kB `.pbp` is written. M1-T28's null result described this model's
  trails as "dominated by proof emission"; the part that is certainly emission is 45% of
  `inmain` before `search` is opened at all, and the rest of the question is inside
  `search` and stays there until `Writer` can be asked. **Reported as a bound, not as a
  confirmation.**
- On the small models `opb` is consistently the largest phase — 150–640 µs against 25–390
  µs for `search`. The suite spends more of itself stating problems than solving them.

**What was still not measured, stated as plainly as the rest.** `search` is propagation,
search and `.pbp` emission together. No row above separates them and no arithmetic here
can. The hook is one accumulator around `Writer.line`; `lib/proof/` was not M1-T35's to
change, and the request is recorded rather than the number guessed. *(Done — M1-T47,
§3b. The hook was not one accumulator and `Writer.line` was not the whole funnel; §3b
says what it actually took.)*

Reproducibility of the internal columns, two full runs a minute apart under the same
load: `width_root_unsat` `inmain` 38212 → 37044 µs (3%), `width_sat_depth` 12178 → 12321
(1%), `chain_sat` 1563 → 1416 (9%), `trivial_sat` 531 → 361 (32%). The small models are
noisy at sub-millisecond scale — and even their noise, ±170 µs, is a twentieth of the
8 ms wall column they replace.

## 3b. Splitting `search`: propagation apart from emission (M1-T47)

Same machine, same checker, minimum of 7, 30 models. Load average 1.85 — the warning
fired, and the wall column carries it; the CPU columns are what this section is about.
`propag` + `emit` is exactly the old `search`, so `inmain` is unchanged and these rows
are directly comparable with §3a's.

```
model                    wall us   startup    parse   compile       opb    propag     emit   clkovh  emitln      pbp    rest    inmain  notslv%
array_sat                   7198      2432      117        77       283        54       32        2       4       89      18       670      91%
bool_and_sat                7456      2694       81        88       196       109       40        9      14       93      16       623      92%
bool_array_sat              7937      2389      135       121       258       113       30       10      16       68      21       746      91%
bool_channel_sat            7825      2360       85        97       295        66       13        2       4       81      22       659      92%
bool_channel_unsat          7900      2354       83        61       203        80       25        6      10       78      13       543      93%
bool_clause_sat             7332      2334       80        55       196        75       28        7      11       61      15       510      93%
bool_eq_sat                 7389      2313       75        71       182        88       30        7      12       62      15       523      93%
bool_not_sat                7513      2517       79        71       189        85       33        7      12       62      13       532      93%
bool_or_sat                 7445      2491      105        84       194        91       26        7      12       60      19       579      92%
bool_out_sat                7379      2391       92        49       169        33       16        3       5       59      21       439      94%
bool_reif_unsat             7566      2392       92       120       274       132       43       11      18       89      14       764      90%
chain_sat                   8331      2359      103       241       562       258       40       15      24       93      61      1358      84%
guess_wrong_sat             7706      2296      102       130       302       354       52       13      20       82      19      1041      86%
lin_ne_sat                  7925      2450       76        99       260        53       18        3       6       59      15       580      93%
lin_sat                     7744      2280       76       240       263        58       16        3       6       83      18       754      90%
lin_unsat                   7684      2247       88        73       315        67       16        4       7      115      13       687      91%
ne_conflict_sat             7303      2351       83        89       219       107       32        9      14       79      18       627      91%
ne_eq_unsat                 7590      2384       66        80       192       104       32        9      14       77      13       564      93%
ne_prune_sat                7435      2448       69        61       179        42       17        3       5       72      18       458      94%
ne_sat                      7136      2359      156        90       178        31       11        2       4       59      18       543      92%
ne_self_unsat               7734      2385       61        46       172        44       20        3       4       86      13       442      94%
near_limit_ne_sat           7912      2481       98       145       338       169       46       12      20       68      16       880      89%
near_limit_unsat            8432      2266       81        80       245       357       75       24      38       91      14       943      89%
offset_unsat                8049      2385       83        76       231       385       84       32      50       91      13       963      88%
root_hole_unsat             7721      2414       77        94       217       105       25        8      13       60      11       589      92%
trivial_sat                 7730      2413       61        40       169        36       15        3       5       79      14       414      95%
trivial_unsat               7546      2426       57        42       181        38       13        2       4       72      12       415      95%
width_narrow_unsat          8060      2383       82       123       331        49       11        2       4       63       9       668      92%
width_root_unsat           38766      2455       85     10026     18128      3140       75        2       4      491      20     31965      18%
width_sat_depth            17895      2540       91      1298      3787      5109      805      350     543      166      24     11280      37%
```

**Read `emit` and `propag` with `clkovh` subtracted from each.** On `width_sat_depth`
that is 805 − 350 = **455 µs of emission** and 5109 − 350 = **4759 µs of propagation and
search**, inside a 5914 µs `search`. On the small models the correction is 2–32 µs
against an `emit` of 11–84 µs: it is a third to a half of the raw number everywhere, not
a rounding term.

**What the split says, and only that.**

- **Emission is not what `search` is made of.** Corrected, it is **7.7%** of
  `width_sat_depth`'s search and **2.3%** of `width_root_unsat`'s, and 20–35% on the
  small models where everything is tens of microseconds. The largest emission number in
  the suite, 455 µs, is an eighth of the same model's `opb` phase (3787 µs).
- **So the proof is still the expensive half of this solver — just not in `search`.**
  `width_sat_depth` spends 3787 µs writing the `.opb`, 166 µs in `pbp` and 455 µs
  emitting during the search: **4408 µs of an 11280 µs `inmain`, 39%, is proof**, of
  which barely a tenth is the part that was fused. M1-T28's "dominated by proof
  emission" survives as a statement about the model and does **not** survive as a
  statement about `Search.solve`'s inner loop.
- **`width_root_unsat`'s 3.1 ms of `propag` is now readable as propagation.** It is a
  model with zero prunings and a 6-line proof; four lines are written during its search
  and they cost 75 µs. Whatever that 3.1 ms is, it is not the writer.
- **An upper bound, not a figure.** `propag` still contains every rule body this solver
  renders — `Pol.to_string_cited` and friends — because that happens at the call site,
  before the writer is entered. Nothing here measures how large that is. It is bounded
  below by 0 and above by `propag`, and narrowing it means moving the accumulator up
  into the rule functions, which is a different task.

**The funnel audit, because the premise had to be checked before it could be used.**
"Every rule goes through `Writer.line`" is true of rules and **false of the file**. Four
places write to the `.pbp` channel: `line`, `comment`, `always_comment`, and the `flush`
in `conclusion`. The bypass that matters is `always_comment`, because in format **3.0 —
the default — `set_level` emits its level marker through it**, so every level marker in
every 3.0 proof misses `line` entirely. Measured by building the version that takes the
premise at face value: `emitln` on `width_sat_depth` falls from 543 to **347** (exactly
the 196 level markers the `lvl` column counts) and corrected `emit`, measured
back-to-back against the instrumented build in the same session, from 444 µs to
**239 µs — a 46% under-count, reported without a symptom.**

**The second thing that had to be measured rather than reasoned about.** A timer wrapped
around `line`'s *body* does not work: `Printf.fprintf oc fmt` returns a closure that
consumes the format's remaining arguments, so for a two-argument `line t fmt` the output
happens after `line` has returned. That wrapper does not read zero — it still sees the
format concatenation and the closure build — which is what makes it dangerous: on
`width_sat_depth` it reports 648 µs against the correct 789 µs, an 18% shortfall wearing
a plausible number's clothes. Driven to 200 kB lines, where the write cannot hide, the
same two wrappers report **283 µs and 25 128 µs**. `Printf.kfprintf`'s continuation is
the only place the end of a line can be observed.

**The cost of the instrument, and why it is off by default.** `Sys.time` is
`CLOCK_PROCESS_CPUTIME_ID` — a real syscall, not a vDSO read. Measured here over
2 000 000 reads: **716–771 ns per read**, so the two-read wrapper is **1.47–1.59 µs per
emitted line**. That is far too much to carry in a normal run, so the accumulator is
behind a gate that costs **1.2–1.6 ns** per line and only `--time` opens it. In-process
calibration of the same read, minimum of nine 256-read bursts, lands at ~645 ns. The
reason it is min-of-bursts and not a single one: a single 512-read burst ranged
**836–1871 ns** across five consecutive runs of the same model, which would have swung
the published correction by a factor of two.

**The artefacts did not move.** Every `.opb`, every `.pbp` and every byte of stdout for
all 30 models is MD5-identical before and after M1-T47, checked on a run of the whole
suite in both directions.

## 3c. Learning baseline, 2026-09-18 (38 models, minimum of 3 runs)

```
models that learned a clause   21 of 38
models with a backjump skip     4 of 38
clauses learned                86, of which 13 convertible (15%)
siblings skipped                9
PB tried / learned / fallback  86 / 36 / 50
PB FALLBACK RATE               58% over 86 attempts
PB rows stronger than a clause 36
```

Three things this table says and one it refuses to.

1. **The fallback rate is 58%, and it is a real measurement**: 86 attempts is a
   denominator, not a rounding artefact, and every attempt came from a proof the checker
   accepted. It reproduces M2-L6's own figure (0.581) on a suite that has grown since.
2. **`pbstrng` is 36 of 36 and means nothing yet.** M2-L6's honest negative stands: all
   36 are the degenerate empty-contradiction case. The counter is here so that M2-L11 —
   giving PB analysis the ladder chain `Linear` actually uses — cannot be claimed without
   a non-degenerate number to show. Until then, read this row as `36 degenerate`.
3. **`conv` is 13 of 86 (15%) and is concentrated**, not spread: the `bool_*` models plus
   a handful of others, exactly as M2-L10 measured. Convertibility is model-dependent,
   which is the argument for D-0044's fork (ii).

What it refuses: **any of these counts divided by a time.** 23 of the 38 rows spend ≥90%
of their wall-clock `solve ms` outside the solver's own work (`notslv%`, §3a), and only
`width_sat_depth` and `width_root_unsat` are below 50%. "Learning costs X µs per clause"
is not supportable from this suite and this table does not offer it. The counts are exact;
the seconds beside them, on 36 of 38 rows, are a timing of `exec`.

## 3d. Explanation size baseline, 2026-09-18 (38 models, `bench/explanation_size.sh`)

M2-T17, off `docs/EXPLANATION-REVIEW.md` section 5: **a sound but maximally weak
explanation -- one naming every variable in scope -- passes every test in this repository
today, and VeriPB accepts it.** Nothing before this measured explanation *quality*; the
literature's quality metric is generality, and a shorter, weaker-premised explanation
prunes more later. This is the first tracked number for it, landed deliberately before
M4-T1 (`all_different`), where the choice of Hall set is the whole game.

Two metrics, read straight off the emitted `.pbp` -- no `lib/` change, no new solver
counter -- and reported separately because nothing says they move together:

- **`rup_lits`**: literals per derived `rup` constraint, mean over that model's `rup`
  lines. The direct reading of "how many variables does this explanation name."
- **`pol_prems`**: premises cited per `pol` chain, mean over that model's `pol` lines --
  every operand pushed (a cited constraint id or a literal pushed as its own unit axiom),
  operators (`+ * d s w !`) excluded. The combining side of the same question: how many
  facts did it take to build this derivation.

A model with zero `rup` (or `pol`) lines reports `n/a` for that metric, not 0, for the
same reason `fb%` does in section 4: a zero would read as "explanations here are free."

```
rup_lits  min .. max over the 26 of 38 models that have a `rup` line: 0.0000 .. 2.3636
pol_prems min .. max over the 12 of 38 models that have a `pol` line: 2.0000 .. 1999.0000
```

Three largest by `rup_lits`: `guess_wrong_sat` 2.3636 (n=11), `offset_unsat` 2.1714
(n=35), `backjump_lineq_unsat` / `near_limit_unsat` tied at 2.0833 (n=24 each).
Three smallest: `ne_self_unsat` 0.0000 (n=1 -- the final contradiction line, an empty
`rup >= 1 ;`, which is the correct zero-literal shape for the last step of an UNSAT
derivation, not a bug), `bool_channel_unsat` 0.6667 (n=3), `ne_eq_unsat` 1.3333 (n=9).

Three largest by `pol_prems`: `width_root_unsat` 1999.0000 (n=1) and `width_narrow_unsat`
19.0000 (n=1) -- both are the D-0028 width fixtures, already the deliberate, measured
outliers `CLAUDE.md` and `bench/README.md` section 5 describe them as; `lin_unsat` 5.0000
(n=3) is the largest non-width figure. Three smallest: `bool_channel_unsat` / `near_limit_ne_sat`
/ `width_sat_depth` tied at 2.0000 -- a `pol` chain combining exactly two premises, which is
this proof format's floor (a chain of one premise needs no combination).

**No model outside the two known width fixtures reads as anomalous.** That is itself the
finding worth recording: today's propagators are all linear and their derivations are
forced (section 5's own framing), so a metric built to catch a needlessly wide explanation
currently has nothing non-width to catch. Its job starts at M4-T1.

Verified this baseline is reproducible: two runs of `bench/explanation_size.sh` byte-for-byte
identical, peak RSS 9.6 MB (`/usr/bin/time -v`, both the harness and, separately, the
solver alone on `width_root_unsat.fzn`, the heaviest model in the suite) -- far under the
15 GB / `ulimit -v 4000000` ceiling `CLAUDE.md` sets.

**The control**, `bench/explanation_size.sh -c` (`bench/control/size/`, see
`README-scenes.txt` there): a hand-authored `.pbp` fixture pair, tight vs. the same
derivation deliberately widened, asserting both `rup_lits` and `pol_prems` come out
strictly larger on the widened one. Verified by breaking the measurement code itself and
watching `-c` fail, and once by breaking it in a way this particular fixture cannot catch
(recorded in `README-scenes.txt` rather than hidden) -- exactly the shape M2-L8's control
verification took in section 7.

## 4. What the columns are *not*

- **`lvl` is not a node count, and since M1-T36 it no longer has to pretend to be.**
  `Search.branch` emits one level marker per child it explores *and* one per step back
  down to a parent, so `lvl` is neither the node count nor a multiple of it. The real
  count is the `nodes` column, from the solver's own counter. `lvl` is kept because
  **`nodes` and `lvl` diverging is the informative case**: the same tree, written down
  more densely.
- **`conv` is not a saving.** It counts learned clauses `Learned.to_linear_row` would
  accept — clauses that *could* propagate if they were installed. Nothing in the solver
  installs them (D-0044 fork ii is still open), so the column measures an opportunity,
  not a benefit, and it says so under the table.
- **`fb%` of a model with no PB attempts is `n/a`, not 0%.** A zero denominator means PB
  analysis was never asked about a conflict on that model. Rendering that as `0%` would
  read as "it never fell back", which is the opposite of what it means.
- **`solve ms` is not propagation time, and still is not.** It is one whole process:
  `exec`, runtime start, parse, compile, solve, write the `.opb` and the `.pbp`, and
  `fsync` on exit. The internal table now says how that splits — except for the one join
  it cannot see, below.
- **`propag` is not propagation time exactly — it is an upper bound on it.** The fused
  `search` column is gone (M1-T47, §3b): `propag` + `emit` is what it was, and `emit` is
  the writer's own output calls. What keeps `propag` a bound rather than a figure is that
  a rule's *body* is rendered at its call site — `Pol.to_string_cited`,
  `Opb.constr_to_string`, the `Printf.sprintf` in `rule`'s argument — before the writer
  is entered, so that rendering is counted in `propag`. **A row here supports
  "propagation costs at most X." It does not support "propagation costs X",** and it will
  not until the accumulator moves up into the rule functions.
- **`emit` is not the whole cost of proof emission, in two directions at once.** Downward:
  it excludes that same rendering, so it is a lower bound. Upward: it *includes* one
  `Sys.time` read per line, which is a third to a half of it on this machine. Both are
  reported — the second as the `clkovh` column — and both must be applied before the
  number is quoted.
- **`notslv%` is an upper bound, not a figure.** `wall` is wall time and `inmain` is CPU
  time, and CPU time is never above wall time, so `wall − inmain` over-states the
  overhead by however long the process was descheduled. Two clocks, subtracted on purpose
  and labelled where they meet; do not carry the difference anywhere it will be read as
  exact. (For the same reason the TSV writes the internal numbers to `FILE.internal`
  rather than as extra columns in `FILE`: two clocks in one row get subtracted by the
  next person to read it.)
- **`.opb B` *is* a property of the model alone — since M1-T37, and it is checked every
  run.** It was not: the `.opb` header carried the model's **path**, so the byte count
  included the length of what you typed and the same model measured as
  `test/models/width_root_unsat.fzn` and as `/tmp/x.fzn` differed by ~16 bytes. The
  header now carries `Filename.basename`, which keeps the comment useful to a human
  holding a `.opb` in a temp directory while removing the one part of the path they
  already know. The harness verifies it before every run by solving the same model
  through an 89-character path and a 144-character one and comparing the bytes; if they
  differ it says so loudly and exits non-zero. **The `.opb` figures in §3 are therefore
  60–80 bytes larger than §3a's for this reason and no other.**

## 5. Memory, and the ceiling

**This box has ~15 GB of RAM and several sessions compiling on it at once, and an agent
OOMed it during this round.** A benchmark that watched bytes and seconds only would have
reported a run that was swapping the machine as merely slow.

Measured here, for D-0028's shape (two variables, one row, zero prunings):

| w | `.opb` | solve peak RSS | verify peak RSS |
|---|---|---|---|
| 9 | 982 B | 4 MB | 10 MB |
| 999 | 126 kB | 9 MB | 18 MB |
| 9 999 | 1.36 MB | 32 MB | 44 MB |
| 49 999 | 7.2 MB | 137 MB | 126 MB |

That is about **1.5 kB of peak RSS per unit of declared domain width**, against 63 bytes
of `.opb` per unit — the in-memory cost is more than 20× the file it produces.
Extrapolating, D-0028's bottom row (w = 10⁶, a 156 MB `.opb`) needs roughly **2.8 GB**
just to build, which is why that row belongs in a decision record and not in a test.

So the harness **refuses to start** a model whose declared width is above **10⁵**, or
whose estimated peak is above **2048 MB**, and says what it estimated:

```
huge   REFUSED (widest declared domain 2000000, total 4000000, estimated peak 5722 MB; -Y to force)
```

`-Y` forces it. Do not use `-Y` while other sessions are working on this machine.
Every invocation also runs under `timeout` (`-t`, default 300 s; `width_curve.sh` uses
120 s). The safe ceiling is **10⁵ declared width**, and the reason is memory rather than
patience: at 10⁵ the solve is already ~140 MB of RSS and the curve is linear.

`ulimit -v` is **not** used as a second belt, and the reason was measured rather than
assumed, because the first draft of this file asserted it and was wrong. OCaml 5 reserves
its minor heaps at start-up — one per domain — and the reservation is **independent of the
model**: `trivial_sat.fzn` runs under `ulimit -v 300000` and dies under `ulimit -v 200000`
with

```
Fatal error: Not enough heap memory to reserve minor heaps
```

So a `-v` cap has a floor of roughly 256 MB of *address space* for a model whose resident
set is 4 MB, and `-v` limits virtual, not resident. It can only ever be a coarse ceiling,
never a cap set near a model's real cost, and a mis-set one produces an error that reads
like the benchmark being broken rather than like a model being too big. Refusing *before*
starting, with the estimate printed, is the failure mode you can actually read. (A `-v`
ceiling well above 256 MB would work as a last-resort backstop; it is not added here
because nothing has yet got past the width guard.)

## 6. The D-0026 falsifier: **not runnable today**

D-0026 (reasons are data, justifications are cutting planes) was accepted under a stated
condition — *"the layering must not cost speed"* — and that half is recorded there as **a
prediction, not a measurement**, with M3-T5 named as its falsifier.

**This harness cannot run that falsification today, and nothing in this directory should
be read as having run it.** The reason is simply that the thing to be measured does not
exist yet: the layered reason/justification form is **M2-T8**, which is `TODO`, blocked on
M2-T7, and no code in `lib/` implements it. There is no second binary to point at.

What has been built is the instrument, in the shape that measurement needs:

```sh
dune build --root .                     # in a worktree with M2-T8 applied
bench/run_bench.sh -S /path/to/layered/main.exe -b layered -r 9
```

`-S` runs a second solver binary over the same models and prints a per-column delta table
— `.opb`, `.pbp`, solve, verify, and the tree proxy — with every timing delta inside the
measured spread labelled `noise`. The tree proxy is load-bearing for this particular
comparison: if the layered form changes what the search explores, the `tree(lvl)` column
says `CHANGED` and the harness states that none of the other columns is then a
like-for-like comparison of proof density. D-0026's claim is about cost *at the same
tree*, so that distinction is the difference between falsifying it and misreading it.

Two things whoever runs it should hold on to:

- D-0026's own prediction is that the layered form is **faster**, because it deletes an
  `O(n·|trail|)` scan per pruning. On the models that exist today that scan is invisible:
  fifteen of eighteen rows are at the process floor. **A "no measurable difference" result
  on this suite would not confirm the prediction** — it would mean the suite cannot see
  it, which is a different sentence and this project's signature failure mode. M1-T24 hit
  exactly this and reported it correctly; the models that could see it are a wide *and
  deep* search, and `width_sat_depth.fzn` is the closest thing here.
- If it measures **slower** on a real model, D-0026 says that reopens the record rather
  than being absorbed.

**What M1-T35 changed about the second point above.** M3-T5's roadmap row said that
until a `--time` existed *no timing claim about the solver could be made from the model
suite in either direction*, which made the falsifier unrunnable twice over — no second
binary, and no instrument fine enough to read it if there were one. The second half is
now fixed: the instrument exists, and the scan D-0026 is about lives in `search`, which
this harness reads at microsecond resolution and which is 25 µs to 5.2 ms across the
suite instead of being buried under 8 ms of `exec`.

The first half is unchanged: **M2-T8 does not exist, so the falsification has still not
been run, and nothing here should be read as having run it.**

**What M1-T47 changed about the warning that used to close this section.** It said that a
delta in `search` between two binaries could be a cheaper scan or a cheaper emission, and
that D-0026's claim is about the scan. That is no longer the obstacle: `propag` and `emit`
are separate columns and a delta can be attributed to one of them (§3b). Two things
remain, and they are smaller but not nothing:

- `propag` is an **upper** bound — it carries the rendering of each rule's body — so a
  `propag` delta is a delta in "propagation plus rendering". D-0026's `O(n·|trail|)` scan
  is inside propagation proper, and nothing separates it from the rendering yet.
- **The suite still may not be able to see the scan at all.** §3b puts `propag` at 31–385
  µs on twenty-eight of thirty models. A "no measurable difference" result there would
  mean the suite cannot see it, which is a different sentence from the prediction being
  confirmed — the same trap M1-T24 fell into and reported correctly. `width_sat_depth`,
  at 4.8 ms of corrected `propag`, is still the only row with room for the answer.

---

## 7. The control: can this report tell a proof-only change from a changed tree? (M2-L8)

```sh
bench/run_bench.sh -c        # asserts; exits non-zero if either direction is wrong
```

This is the one part of `bench/` that **passes or fails** rather than reporting. It is
still not a commit gate and must not become one — it takes minimums over repeated runs
like everything else here — but it is an assertion, and it is the assertion the rest of
the directory rests on.

**Why it is needed.** Every comparison this harness prints ends in a verdict: `CHANGED`,
`proof-only`, `same` or `n/a`. If that verdict is wrong, every number on the row is
misread — a moved search tree gets quoted as a proof improvement. The verdict has been
wrong here before. Until M1-T36 it was computed from level markers alone and reported
every proof-only change as `CHANGED`. M1-T36 fixed it with the node count, and **that
fix went stale the moment backjumping landed**: the solver's own identity is

```
nodes = 2 * decisions + 1 - skipped
```

so a tree can gain a decision, skip two more siblings, and arrive back at the node count
it started from. A node-count-only rule calls that `proof-only`.

**The three scenes.** `bench/control/base/NAME.fzn` is measured as configuration A and
`bench/control/variant/NAME.fzn` as configuration B; they share basenames, so the control
exercises the real join and the real classifier rather than a stub of them.

| scene | what differs | required verdict |
|---|---|---|
| `ctl_proof` | a spectator fixed by **root propagation**: every proof column moves, no tree counter does | `proof-only` |
| `ctl_tree` | a spectator that is **branched**: nodes 7→8, decisions 3→4, skipped 0→1 — and the proof columns move too | `CHANGED` |
| `ctl_samenodes` | **nodes 9 = 9**, decisions 5→4, maxdepth 5→4, skipped 2→0 | `CHANGED` |

`ctl_samenodes` is the one that earns its place. It is classified correctly only from
`decisions`, `maxdepth` and `skipped`; under M1-T36's own historical rule it comes out
`proof-only`, which is a report inviting you to compare the bytes and seconds of two
different searches.

**Both directions are required.** A classifier hard-wired to print `proof-only` passes
`ctl_proof`; one hard-wired to print `CHANGED` passes both others. `-c` fails unless a
`proof-only` verdict *and* a `CHANGED` verdict were both actually produced. Verified by
breaking it on purpose, 2026-09-18 — all three exit 1:

| break | what fails |
|---|---|
| verdict from `nodes` alone (M1-T36's rule) | `ctl_samenodes`: expected `CHANGED`, got `proof-only` |
| verdict hard-wired to `proof-only` | `ctl_tree` and `ctl_samenodes` |
| verdict hard-wired to `CHANGED` | `ctl_proof` |

**What the control does not prove.** It shows the *classifier* separates the two cases on
three scenes built to be separable. It does not show that every future change produces one
of those two shapes, and it is not a proof of the underlying counters — the solver's own
`INCONSISTENT` check on `nodes = 2·decisions + 1 − skipped` is what guards those, and this
harness refuses the whole model if it trips.

**Why scenes and not solver configurations.** Until D-0046 the proof-only scene was one
model re-run under proof format 2.0. That knob is gone. `--proof-comments` cannot replace
it — `bin/main.ml`'s own usage text records that it is a no-op on every shipped model —
and every other CLI knob either changes nothing or changes the tree. Two models, one tree,
two proofs is the shape still available without a `lib/` change. It rests on M1-T37's
self-check, which runs before any measurement: `.opb` bytes are a property of the model,
not of the path it was given. The scenes live in different directories, so if that ever
broke, every control row would differ for a reason unrelated to what it tests — and the
self-check says so and exits non-zero first.
