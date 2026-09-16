# bench/ — the proof benchmark

Task M3-T5, which absorbs M3-T3. This directory holds a measurement tool. It is **not
part of `make check`** and must not become part of it: it takes minimums over repeated
sequential runs, which is slow by construction, and a timing number has no business
failing a build.

```sh
bench/run_bench.sh                       # every model in test/models/, one configuration
bench/run_bench.sh -r 9 test/models/width_root_unsat.fzn
bench/run_bench.sh -F 2.0 -b '2.0'       # 3.0 against 2.0, every column separately
bench/run_bench.sh -S other/main.exe -b layered     # two solver builds
bench/width_curve.sh                     # the D-0028 shape at w = 9, 99, 999, 9999
bench/run_bench.sh -h                    # all the options

baguette MODEL.fzn --proof P --time      # the same internal numbers, one model, by hand
```

`--time` writes its report to **stderr**, one `time: <phase> <microseconds> us <what it
is>` line per phase, and is off unless asked. It changes no byte of stdout, of the `.opb`
or of the `.pbp`; the harness verifies that before it measures anything (§1, "the
self-checks").

There is no `make bench` target. `Makefile` belongs to the orchestrator; if a target is
wanted, the body is `./bench/run_bench.sh "$(ARGS)"` and it must not be a dependency of
`check`.

---

## 1. What it reports, and why they are separate columns

There are now **two tables**, printed one after the other for each configuration. The
first is wall-clock time around whole processes; the second is the solver's own account
of where its time went, read back from `baguette --time` (M1-T35). They are printed side
by side rather than one replacing the other, because **the comparison between them is
the measurement** — it is what says how much of a row was `exec`.

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
| `search` | `Search.solve` — propagation and search **and the proof lines emitted during them** |
| `pbp` | proof channel opened, `Encoding.start_proof`, and the final `.pbp` flush |
| `rest` | printing the solution, plus whatever in `main` is in no phase |
| `inmain` | `startup` excluded; the sum of `parse`…`rest`, exactly |
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
- **`search` still contains proof emission.** Every emission point is inside
  `lib/core/justify.ml` and `lib/proof/writer.ml`; `bin/main.ml` can only bracket the
  call. Splitting it wants an accumulator around `Writer.line`, the single funnel every
  rule goes through. **Until that exists, "propagation costs X" is not a sentence this
  harness supports.** The two proof phases that *are* separable — building the `.opb`
  and flushing the `.pbp` — are separated, and on the wide models they are the larger
  half.

### The self-checks

Before anything is measured, the harness checks two properties of the binary it is about
to measure. Both are properties its own columns rest on, and both were false in this tree
until 2026-09-16.

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

A binary that rejects `--time` as an unknown option is not a failure — it is an older
build, the internal table is skipped with a note, and the wall-clock table is complete.

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
  printed with its version. The proof format is read back out of **each `.pbp`'s own
  version line**, not from `BAGUETTE_PROOF_FORMAT`, because D-0023's lesson is that the
  artefact is the authority and the environment variable is only a request.

One consequence of the last point, found while writing this: the first draft counted
`rup` and `pol` lines with `grep ' rup '`, which counts 31 under format 3.0 and **0** for
the same proof under 2.0, because 3.0 prefixes every derived constraint with a label.
That is D-0025's vacuously-true assertion wearing a benchmark's clothes. The counts now
use `^(@[^ ]+ )?rup `, the shell transcription of `Writer.strip_label`, and the script
says so where it does it.

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

Format comparison, same day, `-F 2.0`: 2.0 is 5–9% smaller `.opb` and 16–18% smaller
`.pbp` on the small models, agreeing in direction with D-0023's "3.0 is about 19% larger".
Every **timing** delta between the two formats came back inside the spread and the harness
labelled all of them `noise`. That is the correct answer, not a disappointing one: the
formats differ in bytes written, and at this problem size bytes written are not the cost.

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

**What is still not measured, stated as plainly as the rest.** `search` is propagation,
search and `.pbp` emission together. No row above separates them and no arithmetic here
can. The hook is one accumulator around `Writer.line`; `lib/proof/` was not M1-T35's to
change, and the request is recorded rather than the number guessed.

Reproducibility of the internal columns, two full runs a minute apart under the same
load: `width_root_unsat` `inmain` 38212 → 37044 µs (3%), `width_sat_depth` 12178 → 12321
(1%), `chain_sat` 1563 → 1416 (9%), `trivial_sat` 531 → 361 (32%). The small models are
noisy at sub-millisecond scale — and even their noise, ±170 µs, is a twentieth of the
8 ms wall column they replace.

## 4. What the columns are *not*

- **`lvl` is not a node count.** The solver does not count nodes, and this harness cannot
  add one without touching `lib/` (owned elsewhere). `Search.branch` emits one level
  marker per child it explores, in both formats, so `lvl` moves when the search tree moves
  — which is the question it is here to answer. It is labelled a proxy everywhere it is
  printed. If a node counter ever lands, this column should become it.
- **`solve ms` is not propagation time, and still is not.** It is one whole process:
  `exec`, runtime start, parse, compile, solve, write the `.opb` and the `.pbp`, and
  `fsync` on exit. The internal table now says how that splits — except for the one join
  it cannot see, below.
- **`search` is not propagation time either.** It is propagation, search, *and* the proof
  lines emitted while they run. This is the honest residue of M1-T35: `bin/main.ml` can
  only bracket `Search.solve`, and every emission point is inside `lib/core/justify.ml`
  and `lib/proof/writer.ml`. The fix is an accumulator around `Writer.line` — the single
  funnel every rule goes through — exposed as something like `Writer.emitted_us`. **Until
  that exists, no row here supports a sentence of the form "propagation costs X."**
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
been run, and nothing here should be read as having run it.** And the warning above
survives intact in a sharper form — `search` is still fused with proof emission, so a
delta in that column between two binaries could be a cheaper scan or a cheaper emission,
and D-0026's claim is about the scan. Splitting them (the `Writer.line` accumulator) is a
precondition for reading a `search` delta as a statement about propagation, not merely a
nicety.
