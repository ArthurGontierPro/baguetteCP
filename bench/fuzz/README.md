# bench/fuzz -- random small-model proof sweep (M7-T21, D-0084)

Generates small random FlatZinc models, solves each with `--proof`, runs veripb over
the proof, and keeps ONLY the models that fail. About 20 000 models through it on
2026-10-02 found the gcc rule C shape of D-0080's corpus rejections and four
root-conflict defects that no lane and no corpus run had seen.

**Not part of `make check`, and must not become part of it**: it is a search for
defects, not a regression gate. A failure it finds is reduced into `test/models/`
and recorded.

## Running it

```sh
dune build --root . bin/                       # run.py does NOT build; a stale binary
                                               # is a measurement of the stale binary
(ulimit -v 4000000; python3 bench/fuzz/run.py gcc 1 500 /tmp/fuzz-gcc)
```

`run.py MODE FIRST_SEED COUNT OUTDIR` prints one line per non-ok seed and a summary,
exiting 1 if anything was kept. Classes: `ok` and `refused` (outside SPEC 2.1) are
deleted; `rejected` (veripb refused: line number, the line, the checker's last
message), `crash` (solver exit != 0) and `timeout` (solver 20 s, veripb 60 s) are
kept as `OUTDIR/m<seed>.{fzn,opb,pbp,log}`. `BAGUETTE=<binary>` and `VERIPB=<binary>`
override the defaults (`_build/default/bin/main.exe`, `~/.cargo/bin/veripb`). Point
`BAGUETTE` at an older build to tell a pre-existing defect from a new one.

**The seed is the reproducer.** `python3 bench/fuzz/gen.py MODE SEED` prints the same
model for the same pair, always. Do not reorder the random calls in `gen.py`: every
seed below depends on that exact sequence.

## The model space

- 4..7 variables `x_k` over `1..D`, D in 3..5; gcc counts over `0..1`..`0..3`.
  **Single-digit widths, by construction** (D-0028: the order encoding is
  width-proportional). Do not widen them here; a property that only shows at width
  has `test/models/width_root_unsat.fzn`.
- Builtins, by MODE:
  - `gcc`: 1-2 `fzn_global_cardinality` (cover of 1-3 values, counts constant or
    variable; a count variable may join a later gcc's scope)
  - `elem`: 1-3 `array_int_element` over constant arrays (index and result drawn
    from the same variables, so shared and crossed index/result occur)
  - `mix`: both of the above
  - `ad`: 1-2 `all_different_int` plus the `elem` constraints
  - every mode adds 1-4 `int_ne` and 0-2 `int_lin_le` (coefficients 1, -1, 2)
- `int_search` over all variables, shuffled, with a random variable choice
  (`input_order`, `first_fail`, `smallest`, `largest`) and value choice
  (`indomain_min`, `indomain_max`, `indomain_median`, `indomain_split`), `complete`.

Most models are UNSAT, and a `rup` over a contradictory database can be accepted
while wrong (D-0066/D-0073). So an `ok` on an UNSAT model is weaker evidence than one
on a SAT model, and a sweep's clean run is not proof of absence.

## What it found (2026-10-02, D-0084)

| Mode, seed | Shape | Status |
|---|---|---|
| `gcc 146` (and 11 more in seeds 1-300) | SAT, `rup +1 <n>_ge_k +1 ~<x>_ge_v +1 <x>_ge_(v+1) ...` refused: gcc rule C LOWER push not single-row RUP | fixed; `gcc_count_lower_rup_sat.fzn` |
| `elem 667`, `mix 166` | UNSAT, `conclusion` "not contradicting": element result-hole derivation embedded with uncancelled root residue | fixed; `element_shared_result_root_unsat.fzn` |
| `elem 9044` | UNSAT, `conclusion` "not contradicting": crossed index/result, index removal stated in the direct currency | fixed; `element_crossed_root_unsat.fzn` |
| `gcc 419`, `mix 1619`, `mix 1948` | UNSAT, `conclusion` "not contradicting": gcc rule C emptying push against a root count bound | fixed; `gcc_count_empty_root_unsat.fzn` |
| `gcc 565`, `mix 11984`, `mix 12008`, `mix 12062`, `ad 25920` | UNSAT, root `rup +1 <lit> >= 1 ;` refused: a nested `Defining` minted with no root trace on the page | OPEN, `search.ml` request (D-0084 item 4a) |
| `ad 24319`, `ad 25012` | UNSAT, `conclusion` "not contradicting": all_different Regin removal in the direct currency | OPEN, `alldiff.ml` request (item 4b) |
| `ad 25203`, `ad 25705` (+1) | CRASH exit 2, `Alldiff: ladder rung has no constraint id` | OPEN, `alldiff.ml` request (item 4c) |

The element foreign-index-hole shape (23 of the 26 corpus rejections) was NOT found by
this sweep; it was built by hand (`element_foreign_hole_rup_sat.fzn`), which needs an
interior `indomain_median` guess and a second element sharing the result.
