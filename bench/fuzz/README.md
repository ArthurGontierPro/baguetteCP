# bench/fuzz -- random small-model proof sweep (M7-T21, D-0084)

Generates small random FlatZinc models, solves each with `--proof`, runs veripb over
the proof, and keeps ONLY the models that fail. About 20 000 models through it on
2026-10-02 found the gcc rule C shape of D-0080's corpus rejections and four
root-conflict defects that no lane and no corpus run had seen.

**Not part of `make check`, and must not become part of it**: it is a search for
defects, not a regression gate. A failure it finds is reduced into `test/models/`
and recorded.

## The differential fuzz lane: `scripts/fuzz_lane.sh` (M22-review-T7, D-0258)

The lane is the successor of `run.py` below: it compares baguette with Gecode instead of only
checking proofs, so it also catches a wrong answer whose proof VeriPB accepts (a wrong `.opb`, or a
`rup` over a contradictory database, D-0066). It is not a gate either. Run it on a node:

```sh
dune build --root . bin/
scripts/fuzz_lane.sh -j 16 -n 100 /scratch/arthur/fuzz-<date>          # all twelve streams
scripts/fuzz_lane.sh -j 16 -n 2000 --streams globals,configs --seed 2 OUT
scripts/fuzz_lane.sh --streams globals --mznlib /path/to/old/mznlib OUT  # another mznlib/
```

Exit status: 0 when every model agreed; 1 when a disagreement was kept in `OUT/<stream>-<k>/bad/`;
2 on a usage or setup error. Timeouts (baguette's 30 to 60 s, VeriPB's 120 s) are kept in `slow/`
and do not make the status 1. `OUT/summary.txt` has one tally line per chunk. The seed of chunk
`k` of the `i`-th stream is `SEED*1000 + i*100 + k`; a stream is a function of that seed, the
binary and mznlib.

| Stream | Script | What it runs | Acceptance test |
|---|---|---|---|
| `default` | `tools/fuzz/fuzz.py` | the review's 26 constraint kinds, domains within -4..4, default flags | found M22-review-T2 (2026-11-23) |
| `free-order` | fuzz.py | `-f --bits-above none` | |
| `larger` | fuzz.py | up to 10 variables and 12 constraints | |
| `search`, `search-free`, `search-order` | `tools/fuzz/fuzz2.py` | 3-SAT near the threshold, small integer optimisation; default, `-f`, `--bits-above none` | |
| `globals` | `tools/fuzz/streams.py` | `global_cardinality` in its five forms (fixed and variable counts, closed, `low_up`, `low_up_closed`) with covers that REPEAT a value (40 %) or miss one, `all_different`, `alldifferent_except_0`, `nvalue`, `table`, `regular`, `element`, `inverse` (also `inverse(f, f)`), `circuit`, `cumulative`, `disjunctive(_strict)`, `bin_packing`, `_capa`, `_load`, `lex_less(eq)` over int and bool, `value_precede`, `count_eq`, `member`, `maximum`/`minimum`; repeated variables, constants in arrays, empty and one-element arrays; 40 % optimisation | with the mznlib of `99d0e39~1` it finds D-0255's wrong UNSAT: 11 of 2000 models, the first at model 54 of seed 1703 (`--seed 1`) |
| `configs` | streams.py | one model (globals, fuzz.py, fuzz2) under 18 configurations: default, `--cdcl`, `--cdcl --chrono 5`, `-f`, and under both the default search and `--cdcl`: `BAGUETTE_MINIMISE=rec`, `BAGUETTE_PRIORITY=classes`, `BAGUETTE_PROBE=root`, `BAGUETTE_RETENTION=keep_all`, `fifo:1`, `lbd:1` and `tiered:core=0,mid=0,first=1,inc=0,mid_every=1` (an eviction at every learned constraint, D-0257's knob). Each agrees with Gecode and with the default run | on main before D-0257 it finds the REJECTED proof under `--cdcl`: model 0 of seed 1 (`streams.py configs OUT 1 1`), under `cdcl-ret-evict`, `-fifo1` and `-lbd1`; VERIFIED on `wave103-retbug` |
| `incr` | streams.py | optimisation models, `-i` and plain: the printed objectives strictly improve, every printed solution holds, the last equals the plain run's optimum | |
| `limit` | streams.py | `BAGUETTE_NODE_LIMIT` in 1..50 (30 % under `--cdcl`) and `-t` 1..20 ms: a stopped run (stderr `limit:`) claims neither `==========` nor UNSAT, its solutions hold and are no better than Gecode's optimum, and VeriPB says NO CONCLUSION or BOUNDS containing the optimum | |
| `e2e` | streams.py | models over what `tools/e2e/fzn2scp.py` covers, through `tools/e2e/chain.sh` bridged and `E2E_SOLVER=1`: VERIFIED agrees with Gecode, SKIPPED is counted, FAIL is kept | |
| `wide` | streams.py | FRONT END ONLY: domains of width 2^21 to 2^62, linear, times, div, abs, max, element, alldifferent; `--time-limit 10`. It answers (agreeing with Gecode when Gecode answers) or refuses (exit 3, 5), never crashes or meets the 4 GB cap. Proofs are not checked | |

Every streams.py run is judged by `check_run`: exit status (3 refused, 5 resource, 4 INTERNAL, an
`Out_of_memory` MEMCAP, anything else CRASH), status and objective against Gecode, VeriPB on the
proof AND its `s VERIFIED` conclusion against what was printed (PROOF-CONCLUSION when they differ),
and Gecode on the model with the printed solution fixed (BAD-SOLUTION). streams.py flattens each
model once with `minizinc -c` (baguette's mznlib, or `--mznlib`) and runs the binary on the `.fzn`,
translating its output through the `.ozn` (a variable MiniZinc fixed is not in the `.fzn`). On a
STATUS- or OBJ-MISMATCH the note also records Chuffed's and CP-SAT's answers, for the triage only:
they never outvote Gecode, because Chuffed shares std's repeated-cover row and answers the same wrong
UNSAT as D-0255's mznlib.

Two shapes are kept out of the generator because Gecode is the outlier there (D-0258): `circuit` over
one node (std and Chuffed: false, Gecode: true; baguette follows std), and a `cumulative` task of
duration 0 whose resource exceeds the capacity (Gecode 6.4.0: UNSAT; Chuffed, CP-SAT, HiGHS: SAT).

**Triage.** `tools/fuzz/triage.py CASE...` re-judges kept cases under `FUZZ_BIN`/`FUZZ_MZNLIB` (a
fix's build tells a known defect from a new one); `tools/fuzz/shrink_mzn.py IN OUT VERDICT [FLAGS]`
deletes constraints while the verdict holds. A new defect is kept as `bench/fuzz/found/<name>.fzn`
with a one-line header, never in `test/models/` until it is fixed, and filed as a cross-session
request.

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
| `gcc 565`, `mix 11984`, `mix 12008`, `mix 12062`, `ad 25920` | UNSAT, root `rup +1 <lit> >= 1 ;` refused: a nested `Defining` minted with no root trace on the page | fixed (M7-T22, D-0086 (a)); `root_nested_defining_{gcc,alldiff}_unsat.fzn` |
| `ad 24319`, `ad 25012` | UNSAT, `conclusion` "not contradicting": all_different Regin removal in the direct currency | fixed (M7-T22, D-0086 (b)); `alldiff_regin_hole_element_unsat.fzn` |
| `ad 25203`, `ad 25705` (+1) | CRASH exit 2, `Alldiff: ladder rung has no constraint id` | fixed (M7-T22, D-0086 (c)); `alldiff_overshoot_decl_top_unsat.fzn`, and its sibling `alldiff_pigeonhole_narrow_{unsat,sat}.fzn` |

The element foreign-index-hole shape (23 of the 26 corpus rejections) was NOT found by
this sweep; it was built by hand (`element_foreign_hole_rup_sat.fzn`), which needs an
interior `indomain_median` guess and a second element sharing the result.

## Acceptance run (M7-T22, D-0086, 2026-10-02)

Seeds 1..30000 of every mode, before and after M7-T22's three fixes:

| Mode | Models | Before: rejected / crash | After: rejected / crash |
|---|---|---|---|
| `gcc`  | 30 000 | 5 / 0  | 0 / 0 |
| `elem` | 30 000 | 0 / 0  | 0 / 0 |
| `mix`  | 30 000 | 4 / 0  | 0 / 0 |
| `ad`   | 30 000 | 25 / 27 | 0 / 0 |

Before = the wave-32 tip `43b68bb`, binary sha256 `a57f296130906c3e7d9744f83f07928235828280bcc40b5661ccceb94f686ab4`; after = `wave33-root`
at the M7-T22 (b) commit, sha256 `7443a8a24907e9050c3df2dcd8de1f19048957d653d23931b997c089ae97be4b` (the later commits touch no source).
Every seed in the table above passes. Reproduce exactly, from the worktree root, with the
binary built by `dune build --root . bin/` (check its hash first):

```sh
(ulimit -v 4000000; for m in gcc elem mix ad; do nice python3 bench/fuzz/run.py $m 1 30000 /tmp/fuzz-acc-$m || echo "$m: NOT CLEAN"; done)
```

Each mode prints `summary: ok=30000` and nothing else. Peak RSS of a mode's run: 51 MB
(`gcc`). The caution above stands: most of these are UNSAT, so a clean run is evidence
against refusals and crashes, not proof that every accepted `rup` is load-bearing.
