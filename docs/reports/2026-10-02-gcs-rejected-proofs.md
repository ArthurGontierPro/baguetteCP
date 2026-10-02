# Glasgow Constraint Solver: 16 proofs VeriPB 3.0.2 does not accept, on MiniZinc Challenge instances

*Prepared 2026-10-02 by the baguette project (University of Glasgow) for the GCS authors.
Everything here is reproducible from the commands in §4; the artefacts are kept on
`fataepyc-07` under `/scratch/arthur/compare-out-w31/log/<instance>.gcs.{opb,pbp,vp,out,err,scp,varmap}`.*

> **Update, 2026-10-02 evening.** The GCS authors pointed out that our VeriPB build (Rust,
> source `78db9573`, 2026-06-18) predates `4c4b92c7` (2026-06-22, "never reset trailhead to
> higher position than current"), before which `move to core` could drop watches and make a
> valid `rup` step fail. Both machines now run source `d5644ca4` (2026-09-04); the 16 proofs
> below are being re-checked with it and this report will be revised with the new verdicts
> (D-0100). Until then the table is a report on the June checker as much as on GCS.

## 1. Summary

While comparing three solvers on the MiniZinc Challenge corpus (436 models, 2008–2026, one
data file each) we ran GCS with proof logging on and checked every proof with VeriPB 3.0.2
(the Rust checker). GCS solved 94 instances within 300 s under a 16 GB proof-file cap. Of
those 94 proofs:

| checker verdict | count |
|---|---|
| VERIFIED | 46 |
| **REJECTED** — "not implied by reverse unit propagation" | **12** |
| **REJECTED** — "the propagated assignment does not satisfy the constraint with ID …" | **3** |
| checker **panic** (`veripb-propagator/src/general_pb_watcher.rs:240:18`, exit 134) | **1** |
| check exceeded 900 s | 32 |

**Every one of the 16 is an optimisation instance whose optimum Chuffed 0.14.0 confirms**
(and baguette too, on the three it finished), so the answers look right and the defect is in
the proof written, or, for the panic, in the checker. No proof was rejected on a
satisfiability instance. The rest of the corpus: 273 instances hit the 16 GB cap, 40 timed
out, 4 errored (integer overflow), 25 never reached a solver (corpus/data issues).

## 2. The 16 instances

Sorted by proof size; the first two are the natural starting points. "Line" is the `.pbp`
line VeriPB names in `Verification error at …pbp:<line>`.

| # | instance (year / model) | data file | GCS answer (time) | Chuffed | `.pbp` lines / bytes | line | message |
|---|---|---|---|---|---|---|---|
| 1 | 2025 `is` | `avdoaYnfXq.dzn` | min 73728 (0.1 s) | 73728 | 18 553 / 1.5 MB | 12632 | propagated assignment does not satisfy constraint 14034 |
| 2 | 2025 `mondoku` (`mondoku-gcc-model-balance`) | `8-8-4.dzn` | min 0 (0.2 s) | 0 | 93 219 / 6.4 MB | 38256 | not implied by RUP |
| 3 | 2013 `fjsp` | `easy01.dzn` | min 253 (0.7 s) | 253 | 351 570 / 55 MB | — | **checker panic**, `general_pb_watcher.rs:240:18`, after 14 s |
| 4 | 2019 `stochastic-vrp` (`svrp-v2-c3_det`) | bare model | min 117 (0.7 s) | 117 (baguette 117) | 370 047 / 38 MB | 262034 | propagated assignment does not satisfy constraint 9457 |
| 5 | 2013 `mario` | `mario_easy_2.dzn` | max 628 (0.5 s) | 628 | 415 758 / 50 MB | 316259 | not implied by RUP |
| 6 | 2014 `mario` | `mario_easy_5.dzn` | max 445 (0.9 s) | 445 | 765 277 / 93 MB | 177148 | not implied by RUP |
| 7 | 2014 `ship-schedule` (`.cp`) | `3Ships.dzn` | max 265650 (1.9 s) | 265650 | 938 291 / 153 MB | 425765 | not implied by RUP |
| 8 | 2011 `ship-schedule` (`.cp`) | `4Ships.dzn` | max 371850 (3.3 s) | 371850 | 1 475 389 / 240 MB | 168174 | not implied by RUP |
| 9 | 2012 `ship-schedule` (`.cp`) | `5Ships.dzn` | max 483650 (5.0 s) | 483650 | 2 406 705 / 399 MB | 207186 | not implied by RUP |
| 10 | 2023 `table-layout` | `p1000_m3_r100_c10.dzn` | min 8137 (76 s) | 8137 | 5 073 200 / 7.6 GB | 202979 | not implied by RUP |
| 11 | 2025 `atsp` | `instance1_0p05.dzn` | min 657504 (17 s) | 657504 | 9 065 586 / 1.2 GB | 18978 | not implied by RUP |
| 12 | 2013 `proteindesign12` (`wcsp`) | `2TRX.11p.8aa.usingEref_self.dzn` | min 1747 (73 s) | 1747 | 9 507 568 / 6.2 GB | 35490 | not implied by RUP |
| 13 | 2015 `is` | `jZ9pQqRxJ2.dzn` | min 210944 (47 s) | 210944 | 29 376 615 / 5.2 GB | 26290 | propagated assignment does not satisfy constraint 23397 |
| 14 | 2011 `prize-collecting` (`pc`) | `25-5-5-9.dzn` | max 65 (55 s) | 65 | 31 352 547 / 3.1 GB | 84331 | not implied by RUP |
| 15 | 2014 `smelt` | `smelt_2.dzn` | min 69 (53 s) | 69 | 37 005 666 / 5.9 GB | 31798 | not implied by RUP |
| 16 | 2014 `stochastic-fjsp` (`fjsp-a1-s4_…det`) | bare model | min 242 (187 s) | 242 (baguette 242) | 192 365 107 / 13.9 GB | 17336 | not implied by RUP |

Observations we can offer without having minimised anything:

- The failing line is early in the file for several large proofs (#11 at 18 978 of 9 M lines,
  #12 at 35 490 of 9.5 M, #15 at 31 798 of 37 M, #16 at 17 336 of 192 M), so the first
  rejected step is within the first seconds of search; the small `is` instance (#1) fails
  at line 12 632 of 18 553. `--trace-failed` on #1 and #2 should be cheap.
- The three "propagated assignment does not satisfy the constraint" rejections (#1, #4, #13)
  are a different failure class from the twelve RUP failures: the checker found a
  propagation step whose asserted assignment violates a constraint of the database.
- Two models appear twice across years with the same defect (`mario` 2013/2014,
  `ship-schedule` 2011/2012/2014; `is` 2015/2025), which suggests one propagator or one
  encoding per family rather than sixteen unrelated faults.
- The panic (#3) is the checker's, not the proof's: a proof can be wrong, a checker should
  say so rather than abort. It reproduces on the kept `.opb`/`.pbp` pair and may be worth a
  VeriPB issue alongside.

## 3. Setup, exactly

| component | value |
|---|---|
| GCS | `https://github.com/ciaranm/glasgow-constraint-solver`, commit `5882c2943480db38fd66760858e3b6196ad7b7cc` (`CP2026-1817-g5882c294`, merge of PR #1135, 2026-10-01); `cmake --preset release`, Release, g++ 15.2.0 (Ubuntu); binary `build/fzn-glasgow`, md5 `ebffdc089f351bbedbd02c12bca6e00d` |
| MiniZinc | 2.10.1 (build 33348285743), the MiniZincIDE bundle; GCS's own `minizinc/mznlib` through `build/glasgow.msc` (JSON FlatZinc) |
| checker | VeriPB 3.0.2, the Rust implementation (`veripb 3.0.2`) |
| limits | 300 s wall (`timeout -k 30`), `ulimit -v 32000000` (32 GB), `ulimit -f 16000000` (16 GB per file), check timeout 900 s |
| machine | `fataepyc-07`, 192 cores, 2 TB RAM, 16 solver jobs in parallel for GCS (48 across the three solvers) |
| corpus | MiniZinc Challenge 2008–2026 archive; the data file is the smallest `.dzn`/`.json` of the family that flattens, pinned in `bench/corpus/answers.tsv` of the baguette repository |

One caveat on the flatten: for every Chuffed and GCS flatten we passed a second model file,
`mznlib/compat_mzn1.mzn` from the baguette repository, which only supplies MiniZinc 1.x
syntax the 2008–2010 models use (`is_output`, string search annotations, the two-argument
`global_cardinality`). It defines nothing a 2.x model calls, but a clean reproduction should
try without it first (§4 gives both).

## 4. Reproducing one instance

```sh
# flatten with GCS's library (MZN_SOLVER_PATH must contain the directory of glasgow.msc)
MZN_SOLVER_PATH=/scratch/arthur/gcs/build \
minizinc -c --no-output-ozn --solver com.github.ciaranm.glasgow-constraint-solver \
  mzn-challenge/2025/is/model.mzn mzn-challenge/2025/is/avdoaYnfXq.dzn -o is.fzn
#   (the run that produced the table added  mzn-challenge/.../compat_mzn1.mzn  as a second model)

# solve with proof logging; -i only on optimisation models (intermediate solutions)
fzn-glasgow -i --prove --proof-files-basename is is.fzn      # writes is.opb / is.pbp

# check
veripb is.opb is.pbp
#   Error: Verification error at is.pbp:12632
#   Caused by: The propagated assignment does not satisfy the constraint with ID 14034.
#   (add --trace-failed for the propagation trace)
```

The kept artefacts for all 16 (`.opb`, `.pbp`, the checker's output `.vp`, GCS's stdout/stderr,
`.scp`, `.varmap`) are at `fataepyc-07:/scratch/arthur/compare-out-w31/log/`; sizes are in the
table above. We are happy to copy any of them, or to re-run with a newer GCS commit.

## 5. Context, for what it is worth

The same harness checked 353 baguette proofs that day (all accepted) and found no
disagreement between the three solvers over 127 instances. On the 51 instances all three
solved, the 1-shifted geometric mean of wall time was 2.28 s for GCS, 7.26 s for baguette
and 0.20 s for Chuffed; GCS's proofs were 35.7 MB and checked in 6.6 s (geometric means over the
42 that verified), baguette's 8.5 MB and 2.3 s.5 MB and 2.3 s. GCS without
proof logging solves 149 of the 436 within 300 s; with it, the 16 GB cap stops 273.

One data point on proof size, from re-running instance #16 with `-s`: GCS visits 3 007 079
nodes (3 006 955 failures, no restarts, 308.6 M propagations of which 67.6 M effectful) and
writes 192 365 107 proof lines, i.e. 4.6 KB and 64 lines per node, about 2.85 lines per
effectful propagation; proof logging takes the run from 72.7 s to 193.7 s. baguette closes
the same instance in 178 nodes with clause learning, so its 1.5 MB proof is a tree-size
effect, not a per-node one: per node its proof is larger (8.6 KB).
