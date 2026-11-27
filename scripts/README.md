# scripts/ — running, gating and measuring

What a session needs to know to run anything here. The rules come from incidents, and each one
names the incident. `bench/README.md` §10 describes what the two M11 lanes measure; this file says
how to run them, gate a merge with them and re-record them.

## 1. Where things run

| Machine | What runs there |
|---|---|
| The laptop (WSL2, 15 GB shared by every session) | Building and typechecking only: `dune build --build-dir=<scratch> lib/ bin/ test/ @fmt`. Flattening a model with MiniZinc is fine. The user forbids running tests, models, benchmarks or the solver there (2026-10-23: "trop nul et imprévisible", and CLAUDE.md's 14.9 GB RSS incident). |
| `fataepyc-06` (192 cores, 2 TB, shared) | Every run: suites, lanes, gates, measurements, Challenge series. |
| `fataepyc-07` | The user's other experiments (codes-cp, graph solvers, re-verifications), which are untouchable. Baguette campaigns may run there only while it is idle, launched over `ssh` from `fataepyc-06` after checking `uptime` and `ps -u arthur` (the user, 2026-11-23); stop launching as soon as another experiment starts. `/scratch` is local to each node. |

On `fataepyc-06`:

| Path | What it is |
|---|---|
| `/cluster/arthur/baguette.git` | The bare hub, on the persistent cluster disk. From the laptop it is the remote `node06`. |
| `/cluster/arthur/baguette` | The working clone a session launched ON the node works in (since 2026-11-19). Its `origin` is the hub; `github` is `git@github.com:ArthurGontierPro/baguetteCP.git`, reachable from the node. Push to both. |
| `/cluster/arthur/baguette-results/` | Copies of the results a decision record cites: the Challenge tables (`m7t26/`, `wave43run/`) and `mznc-archive/`. |
| `/scratch/arthur/<branch>` and `/scratch/arthur/<branch>-runs` | An agent's clone of its branch, and its run outputs. |
| `/scratch/arthur/baguette-gate-<date><letter>` | The fresh clone of one gate; its `_build/default/bin/main.exe` is the binary the next gate compares against. |
| `/scratch/arthur/gateNN.sh`, `gateNN.status` | The gate scripts and their verdicts. |

**`/scratch` can be wiped** by a reset or a crash of the node (the user, 2026-11-19). It is for
proofs, run outputs and disposable clones only. Code, clones you work in, memories and any result
worth keeping go to `/cluster/arthur/` (persistent, shared by the cluster's nodes): copy a run's
tables and logs there, under `baguette-results/<run>/`, before citing them in a decision record.
The hub used to be `/scratch/arthur/baguette.git`; it was removed on 2026-11-19, after the move.
The home directory `/users/grad/arthur` is NFS too, shared by the cluster but not with the laptop.

## 2. The shell

A non-interactive shell (ssh, cron, a detached script) has neither the opam switch nor the checker
on its `PATH`:

```sh
export PATH=$HOME/.cargo/bin:$HOME/.local/bin:$PATH
eval "$(opam env --switch=baguette)"
```

The checker is `$HOME/.cargo/bin/veripb` (3.0.2, source `d5644ca4`). `~/.local/bin/veripb` is a
stale Python wrapper, and a script that finds it first fails: a weekend run in October 2026 died
on it. `scripts/checker.sh` resolves the binary for the suites; a harness of your own should
name `$HOME/.cargo/bin/veripb` explicitly.

From the laptop, `ssh fataepyc-06` jumps through `fataepyc-head` and the gateway `ssh1`. When the
gateway refuses the keys (2026-11-19), the head is reachable directly from campus or VPN:
`ssh -o ProxyCommand="ssh -o ProxyJump=none -W %h:%p fataepyc-head" fataepyc-06`.

## 3. Sharing the node

CLAUDE.md, "The nodes are shared", is the rule: never `pkill`, `killall` or `kill` by pattern
(2026-10-28 killed hours of someone else's `veripb`); kill only PIDs from your own pidfiles; `ps`
before you kill. In practice:

- **Detached runs**: `(nohup setsid bash run.sh > run.log 2>&1 < /dev/null & echo $! > run.pid)`,
  then poll from fresh shells. `timeout`'s children survive a group kill, so a script that may
  need killing writes its own `$$` to a pidfile.
- **The user's own node rules come first.** They live in the global `~/.claude/CLAUDE.md` on the
  cluster's home ("Sur les nœuds de calcul"): at most 92 runs in parallel in all, each under a real
  memory limit (`systemd-run --user --scope -p MemoryMax=32G ...`); no `make -j` above 16; look at
  the free space on `/scratch` before writing large proofs, and tell the user
  when a run writes more than a few tens of GB; never delete or rewrite a file you did not create
  outside this repository; text with quotes or backquotes does not survive `ssh '...'`, so write it
  to a file and `scp` it.
- **Budget.** `make -j` stays at 16 or below. Lane and campaign runs count toward the 92 runs of
  the whole node, every experiment included; each lane run is capped by its own `ulimit -v` (4 GB,
  `BAGUETTE_MEM_CAP_KB`), so 92 of them hold at most 368 GB of the node's 2 TB. An agent uses
  `-j 16`, so that several can gate at once. The orchestrator's gate may use `-j N` with N = 92
  minus the runs already going (`ps -u arthur`, read the list). Look at `uptime` before a large
  series; an experiment that is not yours has priority.
- **Memory**: suites run under `ulimit -v 4000000` (make applies it); lanes and Challenge runs
  under 16 GB. A run that dies on a cap is a finding. Raise a cap only for an explained exception,
  written in WORKLOG (`BAGUETTE_MEM_CAP_KB=33554432` for openshop's checker, below).

## 4. The gate: what makes a merge count

The orchestrator gates every merge into `main` on a fresh clone, never on a working tree. Copy the
last `/scratch/arthur/gateNN.sh` and change its number, its clone directory and the previous gate's
binary. It does, in order:

1. `git clone /cluster/arthur/baguette.git` into a new `/scratch/arthur/baguette-gate-<date><letter>`.
2. `make check` under `ulimit -v 4000000` with `/usr/bin/time` (rc, unit checks, models, peak RSS).
3. For every `test/models/*.fzn`, stdout, exit code, `.opb` and `.pbp` of the new binary against
   the previous gate's binary, both hashed. A change meant to be byte-identical must show 0
   differences. A comparison whose two sides used the same binary is no evidence (CLAUDE.md).
4. `make diff ARGS="--tier all -j N"` and `make diff ARGS="--debug --tier all -j N"`, N as in §3 (16 for
   an agent, up to 92 minus the node's other runs for the orchestrator).
5. `make scaling ARGS="-j 16"`, a blocking gate since D-0160: its rc is the verdict.
6. A `DONE` line in `gateNN.status`. The gate is then recorded in a WORKLOG handoff note
   ("gate NN recorded").

Launch it detached (section 3) and poll `gateNN.status`.

## 5. Re-recording a reference

- **The diff lane** (`bench/diff/reference*`, D-0141): only after a gated merge that changes the
  search on purpose, in a commit of its own that names the cause:
  `BAGUETTE_MEM_CAP_KB=33554432 scripts/diff_lane.sh --update --config NAME`. `--update` verifies
  every proof it records; openshop's checker dies under the default 4 GB cap, hence the 32 GB.
  A new configuration in `bench/diff/configs.tsv` gets its references in the same merge. Run the
  update in the gate clone, copy `bench/diff/` back and commit it.
- **The scaling baseline** (`bench/scaling/baseline.tsv`, D-0160): `scripts/scaling_lane.sh
  --update -j 16`, a per-line ratchet that keeps a line's row unless its growth fell. `--raise`
  writes every line as measured, and only with a decision record.

## 6. Merge traps met in November 2026

- `WORKLOG.md` and `docs/DECISIONS.md` conflicts are two appends: keep both sides. In WORKLOG put
  the newest handoff note first and drop claim rows the merge resurrects (a branch based on an
  older `main` brings released claims back).
- A `docs/ROADMAP.md` conflict where each side updated a different row: take each row from the side
  that updated it.
- Resolving a code conflict can break formatting (gate 54 failed on a dropped blank line): run
  `dune build --build-dir=<scratch> lib/ bin/ test/ @fmt` before committing the merge.
- A hook rejects any shell command whose text contains a space followed by the dash-a flag, commit
  messages included. Never `git add -A`, `git add .` or commit-all (CLAUDE.md, "Git").
- A paused agent leaves a WIP commit and a `PAUSED` note at the top of `## Handoff notes` on its
  branch: resume from the note, not from memory.

## 7. The scripts

| Script | What it does |
|---|---|
| `checker.sh` | Resolves which `veripb` runs; a missing checker is a failure |
| `verify_proof.sh` | Solves one model and checks its proof |
| `run_model_tests.sh` | The model suite, with the proof and the `--no-proof` stdout lane |
| `mutate_proof.sh` | The mutation lanes: a broken proof must be refused at the checker's wording |
| `diff_lane.sh`, `scaling_lane.sh` | The M11 lanes (`make diff`, `make scaling`), sections 4 and 5 |
| `compare_run.sh`, `corpus_run.sh` | baguette against Chuffed and GCS, and corpus walks; both pass `--proof` (`bench/challenge/README.md`) |
| `check_fmt.sh`, `check_test_widths.py`, `check_determinism.sh`, `check_unlimited.sh` | The static checks of `make check` |
| `compare_selftest.sh`, `corpus_selftest.sh` | Self-tests of the two harnesses |
| `shrink.sh` | Shrinks a failing model |
| `run_scp_tests.sh` | The `.scp` models of `test/scp/` against `test/scp/expected/`, every proof checked (`make scp`, part of `make test`) |
| `e2e_lane.sh`, `sym_lane.sh` | The end-to-end and symmetry lanes, sections 9 and 10. Node only, not in `make check` |
| `fuzz_lane.sh` | The differential fuzz (M22-review-T7): random small models, baguette against Gecode through MiniZinc, every proof checked and every solution re-checked. Not a gate: a disagreement becomes a model in `test/models/`. `scripts/fuzz_lane.sh -j 16 -n 100 /scratch/arthur/<run>` on a node |
| `bootstrap.sh` | Installs the toolchain on a fresh machine; safe to re-run |

## 8. The release binary (M11-complexity-T16, D-0171)

`make release` builds the solver alone with dune's release profile into its own build directory:

```sh
make release        # dune build --root . --profile release --build-dir _build_release bin/main.exe
                    # -> _build_release/default/bin/main.exe, and prints its md5
```

dune's dev profile compiles every library module with `-opaque`, so no cross-module call is ever
inlined. The release binary runs about 17 % fewer instructions per node on QR48 and writes the same
bytes as the dev binary of the same commit (D-0171 has the measurement). `_build_release/` has its
own lock, so it does not fight the dev `_build/`, and `dune build`, `make check` and a worktree's
`--root .` are unchanged.

- **Measurements and Challenge series use it.** Point the harness at it by variable:
  `BAGUETTE=_build_release/default/bin/main.exe` for `compare_run.sh`, `corpus_run.sh`,
  `bench/run_bench.sh` and the suite scripts, `BIN=...` (or `--bin`) for `diff_lane.sh` and
  `scaling_lane.sh`. The defaults stay the dev binary.
- **Gates and sessions keep dev.** Release does not turn warnings into errors, so it is never the
  gate. The scaling lane's baseline was measured on dev: compare a release run only with a release
  run.
- **Every series records the binary's md5** (`make release` prints it), and says it is release.

## 9. The end-to-end lane (M14-e2e-verification-T2, D-0176)

`make e2e ARGS="-j 8 /scratch/arthur/<run>"`, or `scripts/e2e_lane.sh -j 8 OUTDIR`. Node only, not
in `check`. It needs three things outside the repository, and a missing one is a failure, never a
skip:

| What | Default | Override |
|---|---|---|
| `cake_pb_cp`, CakeML's verified CP encoder and checker (D-0174) | `/cluster/arthur/baguette-results/wave55-e2e/cake_pb_cp-438b8f83` (sha256 `ca92491e`) | `CAKE_PB_CP=` |
| the solver | `_build/default/bin/main.exe`, NOT built by the script: `dune build --root . bin/` first | `BAGUETTE=` |
| Gecode and CP-SAT, the translator's references | the MiniZinc 2.10.1 bundle under `/scratch/arthur/mzn/` | `MZN_BIN=` |

Three passes, one line per item, a summary each, `e2e_lane: PASS` or `FAIL` at the end:

1. **chain**: every `test/models/*.fzn` through `tools/e2e/chain.sh`. `VERIFIED` means
   `cake_pb_cp`'s own `s VERIFIED SATISFIABLE|UNSATISFIABLE` line, agreeing with baguette, or for
   an objective (D-0182) `s VERIFIED BOUNDS v <= OBJ <= v` with v baguette's optimum (`OPT=v`). It exits
   0 when it refuses, so never read its status. `SKIPPED` names the first uncovered builtin (or the
   objective, or `var int` with no domain). Anything else is `FAIL`.
2. **controls**: forty-one corruptions the bridged chain must refuse (forty-two on the solver-written `--e2e` path, D-0195, D-0196), each asserted at the refused line and
   in the checker's sentence (`chain.sh`'s header lists them). One runs on a model of its own,
   `tools/e2e/models/gcc_repeat_free_sat.fzn` (D-0180 §4). Eight claim a wrong optimum (D-0182):
   four refused by `veripb` at baguette's `conclusion BOUNDS`, four by `cake_pb_cp` itself at the
   elaborated core's.
3. **validation**: the translator against the reference solvers, solution set for solution set. A
   model calling baguette's mznlib predicates is re-flattened as MiniZinc against the reference's own
   library (`tools/e2e/fzn_solutions.py`, D-0180 §5).

Each run is under `systemd-run --user --scope -p MemoryMax=32G` with a timeout, at most 8 at a
time, and writes `OUTDIR/<dir>/<model>.pid` while it runs; the lane's own PID is `OUTDIR/lane.pid`.
Clean up with `kill $(cat OUTDIR/lane.pid)` and the per-model pidfiles, never by name. `make e2e` is the one
running target without `ulimit -v`: `cake_pb_cp` reserves its whole heap as virtual memory and
refuses every model under the 4 GB cap. baguette keeps the cap inside `chain.sh`. The chain and
the controls take about ten seconds at `-j 8`; the validation takes about four and a half minutes,
most of it the two references timing out (120 s each) on `rup_level0_nogood_sat`, which stays
UNCHECKED (measured 2026-11-20, D-0180).

The translator, `tools/e2e/fzn2scp.py`, is the one TRUSTED new link: a wrong translation verifies.
It shares no code with `lib/flatzinc/` on purpose (D-0174 §5). Widen it only together with
`tools/e2e/scpsem.py` (the .scp semantics transcribed from CakeML's `cpScript.sml`) and the
validation pass, and run the lane.

`make e2e ARGS="--bits W"` runs the solver's passes at `--bits-above W` (the bits arm, D-0196: baguette's unsigned offset bits rebuilt from cake's two's-complement bits by a ripple-carry adder in the prefix); the lane is VERIFIED at W = 0 and W = 4 with the same counts as the order arm.

## 10. The symmetry lane (M15-symmetry-T2, D-0179)

`make sym ARGS="-j 8 /scratch/arthur/<run>"`, or `scripts/sym_lane.sh [-j N] [--big] OUTDIR
[NAME...]`. Node only, not in `check`. dejavu is NOT inside baguette (the user's rule): it runs
beside it, as distributed, in a pipeline of three scripts under `tools/symmetry/`.

```sh
main.exe M.fzn --proof ORIG --time-limit 0                 # ORIG.opb, the model, no search
tools/symmetry/symchain.py M.fzn ORIG.opb S --depth 3      # dejavu per level -> S.chain.json, S.fzn
main.exe S.fzn --proof S                                   # baguette on the broken model
tools/symmetry/symmerge.py S.chain.json ORIG.opb S.opb S.pbp MERGED.pbp
veripb ORIG.opb MERGED.pbp                                 # the ORIGINAL model, unchanged
```

| What | Default | Override |
|---|---|---|
| dejavu, upstream `main` `f984485` (v2.1), unchanged | `/cluster/arthur/tools/dejavu-f984485/build/dejavu` (sha256 `bb1759d0`, `PROVENANCE` beside it) | `DEJAVU=` |
| the solver | `_build/default/bin/main.exe`, NOT built by the script: `dune build --root . bin/` first | `BAGUETTE=` |
| MiniZinc, to flatten the codes | the 2.10.1 bundle under `/scratch/arthur/mzn/` | `MZN=` |
| codes-cp, for QR48's `.dzn` (`--big`) | `/cluster/arthur/codes-cp` | `CODES_CP=` |

The instances are `bench/symmetry/instances.tsv`. One line per instance, a row of
`OUTDIR/results.tsv` (group order, chain, cuts, nodes and seconds without and with the cuts, the
check), and `sym_lane: PASS` or `FAIL`. VERIFIED means veripb's `s VERIFIED` line on the original
`.opb`, agreeing with the expected answer and with both baguette runs. On the satisfiable models
marked `yes`, four controls (a wrong witness and a wrong cut, under `red` and under `dom`) must be
refused at the mutated line, in the checker's words. Each step is under `systemd-run --user
--scope -p MemoryMax=32G` and a timeout (`SYM_TL`, 1800 s), with `OUTDIR/<name>/<step>.pid`
while it runs and `OUTDIR/lane.pid`. Clean up by those PIDs, never by name. The small tier takes
seconds; QR48 (`--big`) about five minutes, most of it the run without breaking (253 s).

Nothing in `tools/symmetry/` is trusted: a wrong generator, orbit or witness is a line veripb
refuses. Only 0/1 variables are broken on (the cut has to be a FlatZinc constraint without new
variables), and optimisation models are refused (M15-symmetry-T4).
