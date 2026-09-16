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
```

There is no `make bench` target. `Makefile` belongs to the orchestrator; if a target is
wanted, the body is `./bench/run_bench.sh "$(ARGS)"` and it must not be a dependency of
`check`.

---

## 1. What it reports, and why they are separate columns

| column | what it is |
|---|---|
| `.opb B` | bytes of the problem statement the proof is about |
| `.pbp B` | bytes of the proof |
| `verify ms` | how long the checker of record takes to accept it |
| `slvMB` / `vrfMB` | peak RSS of the solve and of the verify |
| `solve ms` | how long the solver takes, apart from the checker |
| `lvl` | search-tree proxy — see §4, it is **not** a node count |
| `lines` / `longest` / `rup` / `pol` | the proof's shape |

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
- **A process floor is measured and printed in the header.** Both timings are wall time
  around a whole process. The solver invoked with no arguments costs **4.0 ms** here and
  the checker asked for its version **4.6 ms**, so a model reported at 7 ms is roughly 4 ms
  of `exec` and 3 ms of solving. On the fifteen pre-existing models *almost the entire
  solve column is the floor*. That is a fact about the instrument and it is printed at the
  top of its own output rather than buried here.
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

## 3. Baseline, 2026-09-16

VeriPB 3.0.2 (`~/.cargo/bin/veripb`), emitted format 3.0, minimum of 7 runs, one at a
time, WSL2 / 12 cpu / 15.8 GB. Process floor 4.0 ms solver, 4.6 ms checker.

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
   change that claims a speed effect on them is claiming it about `exec`.
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

## 4. What the columns are *not*

- **`lvl` is not a node count.** The solver does not count nodes, and this harness cannot
  add one without touching `lib/` (owned elsewhere). `Search.branch` emits one level
  marker per child it explores, in both formats, so `lvl` moves when the search tree moves
  — which is the question it is here to answer. It is labelled a proxy everywhere it is
  printed. If a node counter ever lands, this column should become it.
- **`solve ms` is not propagation time.** It is one whole process: `exec`, runtime start,
  parse, compile, solve, write the `.opb` and the `.pbp`, and `fsync` on exit. Subtract
  the printed floor before believing any of it.
- **`.opb B` is not a property of the model alone.** The `.opb` header carries a comment
  naming the model **path**, so the byte count includes the length of the path you typed:
  the same model measured as `test/models/width_root_unsat.fzn` and as `/tmp/x.fzn` differs
  by 16 bytes. Harmless for a comparison, which always uses the same path on both sides,
  and noted here because a 16-byte discrepancy between two people's numbers otherwise
  looks like a real difference. Found, not fixed — `lib/proof/` is not this task's.

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
