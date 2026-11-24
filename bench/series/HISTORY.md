# Challenge series, one row each, newest first

A series is the sixteen MiniZinc Challenge editions (2011 to 2026, 1 600 instances) run on one
solver binary in arms. A row is produced by `bench/series/run_series.sh` (the clone, the release
build and its md5, the arms, `read_series.sh` for the tables), then
`tools/compare/readme_table.py SERIES_DIR` writes the README's performance section from the same
tables. Add the row here in the same commit as the regenerated README section.

**A number is copied from the series' decision record (or its published tables), never recomputed
by hand.** An empty cell means the record does not give that number in that form. Do not fill it
from memory.

Cell format of an arm: `OPT+UNSAT verified / SAT verified / REFUSED / summed score / rank range`.
The rank range is the best and worst rank over the sixteen editions in the FIXED category, scored
against that year's official entrants by `tools/compare/challenge_rank.py` (a `-f` arm is scored in
that category too, so the rows compare). The entrants number 6 to 13 per edition. An arm without
proof (`--no-proof`) is UNVERIFIED, and its counts are what the harness printed, not checked ones.
Arms: A default with proof, B `-f` with proof, C default `--no-proof`.

| Date | Record | Commit | Binary | Differing settings | A (default, proof) | B (`-f`, proof) | C (default, `--no-proof`) |
|---|---|---|---|---|---|---|---|
| 2026-11-23 to 24 | D-0210, observation, 64 GiB, fataepyc-07 | `e1971f6` (harness), same source as D-0203 | `f244c35a` | bits default, no proof cap, 64 GiB address space, `--max-heap-mb 32768`; arms A and C only, PAR 40 | 304 verified / empty / 60 / 4 323 / 4 to 11 (3 more OPT complete but TIMEOUT-CHECK) | not run | 344 unverified / empty / 48 / 4 782 / 2 to 11 |
| 2026-11-23 to 24 | D-0203, series-20261123 | `f827518` (main `f6c62db` plus the series tooling, no change under `lib/` or `bin/`) | `f244c35a` | bits default (D-0201), no proof cap, 16 GiB address space, heap budget 8 GiB, veripb 64 GB cgroup | 302 / 74 / 164 / 4 043 / 5 to 12 | 346 / 95 / 138 / 5 799 / 2 to 9 | 340 / 86 / 157 / 4 428 / 4 to 11 (unverified) |
| 2026-11-20 to 22 | D-0185, m10t5 | `10b3507` | `7c880bce` | order encoding by default, 16 GB proof cap, 16 GiB address space (also covers veripb), heap budget 8 GiB | 251 / 72 / 314 / 2 789.4 / 6 to 12 | 265 / 97 / 336 / 3 580.6 / 4 to 12 | 296 / 84 / 398 / 3 237.1 / 6 to 12 (unverified) |
| 2026-11-20 to 21 | D-0175, m8t4, arm `none` (order) | `ec53df4` | `492638b9` | order encoding, 16 GB proof cap, 16 GiB, heap budget 8 GiB; proof arms only, PAR 20 per arm | 245 / 70 / 320 / 2 712.4 / 6 to 12 | not run | not run |
| 2026-11-20 to 21 | D-0175, m8t4, arm `w0` (`--bits-above 0`) | `ec53df4` | `492638b9` | the same binary, bits encoding on every variable | 287 / 71 / 277 / 3 441.3 / 5 to 12 | not run | not run |
| 2026-11-13 to 14 | D-0133 (baseline of M8-bits-encoding-T4) | `f158c9f` | `a6327dc6` | order encoding, 16 GB proof cap, 16 GiB, 30 in parallel | 184 complete (224 verified in all) / 48 printed / 205 / 2 316.7 / 6 to 12 | not run | not run |
| 2026-11-02 | D-0121 (M7-T26, sixteen editions side by side), score from D-0185's table | empty | empty | order encoding, width wall, 8 GiB heap budget, 16 GB proof cap | 169 complete, all verified / empty / 543 / 1 885.0 / 6 to 12 | not run | not run |

Notes on the rows.

- D-0185 gives its B rank in the free category too (8 to 23 of 14 to 27 entrants). The cell above
  is the fixed-category reading its last column gives, which is the one the later rows use.
- D-0133 says 184 complete answers and 224 verified in all, and does not split the 224 into
  OPT+UNSAT and SAT, so the two numbers are given as the record words them.
- D-0210's ranks come from the `rank_A_*.txt` and `rank_C_*.txt` of
  `/cluster/arthur/baguette-results/node07-64g/`, the verified count and scores from the record. It
  is on branch `wave60-node07`, not yet on main when this row was written, and its SAT count is not
  in the record.
- D-0121 and D-0133 predate the series driver. Their rows come from the record's tables, and the
  binary of D-0121 is not recorded there.
- Scores and ranks are only comparable between rows with the same entrants and the same scoring
  script, and the counts only between rows that share a proof cap (see Differing settings).
