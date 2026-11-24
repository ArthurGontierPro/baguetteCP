# bench/challenge — the MiniZinc Challenge editions

`<YEAR>.lst` (2011 to 2026) is each edition's official instance set; `bench/README.md` §9 says how
the lists are built and how an edition is run and ranked. This file says where the solvers and the
recorded runs are, so that a session reads a table instead of relaunching a series.

## 1. The solvers

| Tool | Where |
|---|---|
| MiniZinc 2.10.1 bundle, with Chuffed | node: `/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc` (not on `PATH`); laptop: `~/opt/MiniZincIDE-2.10.1-x86_64-linux-gnu`, linked as `~/.local/bin/minizinc` |
| Chuffed | `--solver chuffed` from the bundle |
| GCS (Glasgow Constraint Solver) | node: `--solver /scratch/arthur/gcs/build/glasgow.msc` |
| baguette | flatten with `minizinc -c --solver <checkout>/tools/baguette.msc model.mzn data.dzn -o x.fzn`, which uses `mznlib/`, then run the release binary `_build_release/default/bin/main.exe` (`make release`, D-0171; the harnesses take it as `BAGUETTE=...`); or `MZN_SOLVER_PATH=<checkout>/tools minizinc --solver baguette ...` |
| Kissat 4.0.2, pysat | installed 2026-11-16 under `/scratch/arthur/tools/`, which is not on `fataepyc-06` (checked 2026-11-19); look on `fataepyc-07` before reinstalling |

Flattening is fine on the laptop; solving goes to the node (`scripts/README.md` §1).

## 2. The recorded runs

Every path below on `/scratch` can be wiped by a node reset. The tables (`*.tsv`) of M7-T26 and
wave43, and the archive, are copied to `/cluster/arthur/baguette-results/` (2026-11-19), which is
persistent; read those copies if `/scratch` is gone.

| Run | What | Where |
|---|---|---|
| M7-T26, 2026-10-30/31 | All sixteen editions, 1 200 s, 16 GiB, PAR 30; baguette and Chuffed, GCS on 2025 and 2026 only; fixed category only | tables `/scratch/arthur/m7t26/<YEAR>/{results,flatten}.tsv`; corpus `/scratch/arthur/mznc/<YEAR>/`; archive `/scratch/arthur/mznc-archive/` (also `~/mznc-archive` on the laptop); records D-0105 (2026) to D-0120 (2011), synthesis D-0121 |
| wave43, 2026-11-13 | The editions again after M7-T27 | `/scratch/arthur/wave43run/`, D-0133 |
| M8-T4, 2026-11-20/21 | Two arms, one binary (`492638b9`, `ec53df4`): `W = none` and `--bits-above 0`, baguette only, D-0133's rules, 20 + 20 runs; peak RSS per run in `log/*.rss` | `/scratch/arthur/m8t4/{none,w0}/<YEAR>/`, tables in `/cluster/arthur/baguette-results/m8t4/`, D-0175 |
| M10-T5 / M9-T3 / M7-T30, 2026-11-20/22 | All sixteen editions in three arms of one release binary (`7c880bce`, main `10b3507`, order default, before D-0201): A default with proof (fixed category), B `-f` with proof (free category), C default `--no-proof` (unverified); D-0133's settings, flattened once with `10b3507`'s mznlib | runs `/scratch/arthur/m10t5/{A,B,C}/<YEAR>/`; tables, per-instance pairs and drivers `/cluster/arthur/baguette-results/m10t5/`; record D-0185 |
| M17-T1/T2, 2026-11-23/24 | All sixteen editions in three arms of one release binary (`f244c35a`, bits default D-0201, no proof cap, PAR 29 per arm): A default with proof, B `-f` with proof, C default `--no-proof`; veripb in its own 64 GB cgroup, 3 600 s | runs `/scratch/arthur/series-20261123/{A,B,C}/<YEAR>/`; tables and drivers `/cluster/arthur/baguette-results/series-20261123/`; driver `bench/series/run_series.sh`; record D-0203 |
| Later rows | Per-feature Challenge runs (`regular`, `inverse`, `member`, alldiff conflicts) | each record's own section names its run directory |

Re-read an edition without re-running it:

```sh
python3 -I tools/compare/challenge_rank.py <archive>/results/<YEAR>.json bench/challenge/<YEAR>.lst \
  /scratch/arthur/m7t26/<YEAR> [--no-chuffed] [--category=free]
```

M7-T26's headline, stale since the November work: baguette-fd last in 13 editions and next to last
in 3; 169 complete answers, all VERIFIED; 543 refusals (388 width wall, 145 heap budget, 9 gcc with
a repeated variable, 1 unbounded `var int`). The M8, M9, M10 and M11 milestones changed most of
those numbers. D-0185 (M9-T3, M10-T5) re-measured all sixteen on `10b3507`: 323 verified complete answers,
0 REJECTED, no width-wall refusal left, 311 heap-budget refusals, fixed-category score sum 2 789.

## 3. Rules for a new series

- Read the recorded tables first. A series costs the node for a day or more.
- Every baguette answer is checked: the harnesses pass `--proof` and run `veripb`. An OPT or UNSAT
  whose proof is not VERIFIED is demoted by `challenge_rank.py`.
- Ask the user before a new series whether to run Chuffed again. M7-T26 reran it as a scale factor
  against the official `chuffed-fd` results, and the user asked why; the question was left open.
- The free category (`-f`, D-0154) was first run in D-0185 (arm B), on a binary before D-0201's default.
- Run a series on the release binary (`make release`, `BAGUETTE=<checkout>/_build_release/default/bin/main.exe`;
  `scripts/README.md` §8). It writes the same bytes as dev at ~17 % fewer instructions per node
  (D-0171). The harnesses' default is still the dev binary, so set the variable.
- Hash the binary of every series and write the md5 in its record, with whether it is release or dev.
