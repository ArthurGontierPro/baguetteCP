# scripts/ — running, gating and measuring

What a session needs to know to run anything here. The rules come from incidents, and each one
names the incident. `bench/README.md` §10 describes what the two M11 lanes measure; this file says
how to run them, gate a merge with them and re-record them.

## 1. Where things run

| Machine | What runs there |
|---|---|
| The laptop (WSL2, 15 GB shared by every session) | Building and typechecking only: `dune build --build-dir=<scratch> lib/ bin/ test/ @fmt`. Flattening a model with MiniZinc is fine. The user forbids running tests, models, benchmarks or the solver there (2026-10-23: "trop nul et imprévisible", and CLAUDE.md's 14.9 GB RSS incident). |
| `fataepyc-06` (192 cores, 2 TB, shared) | Every run: suites, lanes, gates, measurements, Challenge series. |
| `fataepyc-07` | The user's other experiments (codes-cp, graph solvers, re-verifications). **Never run baguette there.** Reading its files is fine when the user asks. |

On `fataepyc-06`:

| Path | What it is |
|---|---|
| `/scratch/arthur/baguette.git` | The bare hub. From the laptop it is the remote `node06`. |
| `/scratch/arthur/baguette` | The working clone a session launched ON the node works in (since 2026-11-19). Its `origin` is the hub; `github` is `git@github.com:ArthurGontierPro/baguetteCP.git`, reachable from the node. Push to both. |
| `/scratch/arthur/<branch>` and `/scratch/arthur/<branch>-runs` | An agent's clone of its branch, and its run outputs. |
| `/scratch/arthur/baguette-gate-<date><letter>` | The fresh clone of one gate; its `_build/default/bin/main.exe` is the binary the next gate compares against. |
| `/scratch/arthur/gateNN.sh`, `gateNN.status` | The gate scripts and their verdicts. |

`/scratch` is local to each node; the home directory `/users/grad/arthur` is NFS, shared by the
cluster but not with the laptop.

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
  memory limit (`systemd-run --user --scope -p MemoryMax=32G ...`); no `-j` above 16 (the lanes run
  at `-j 16`); look at the free space on `/scratch` before writing large proofs, and tell the user
  when a run writes more than a few tens of GB; never delete or rewrite a file you did not create
  outside this repository; text with quotes or backquotes does not survive `ssh '...'`, so write it
  to a file and `scp` it.
- **Budget**: at most 16 parallel jobs per agent. Look at `uptime` and `ps -u arthur` before a
  large series; an experiment that is not yours has priority.
- **Memory**: suites run under `ulimit -v 4000000` (make applies it); lanes and Challenge runs
  under 16 GB. A run that dies on a cap is a finding. Raise a cap only for an explained exception,
  written in WORKLOG (`BAGUETTE_MEM_CAP_KB=33554432` for openshop's checker, below).

## 4. The gate: what makes a merge count

The orchestrator gates every merge into `main` on a fresh clone, never on a working tree. Copy the
last `/scratch/arthur/gateNN.sh` and change its number, its clone directory and the previous gate's
binary. It does, in order:

1. `git clone /scratch/arthur/baguette.git` into a new `baguette-gate-<date><letter>`.
2. `make check` under `ulimit -v 4000000` with `/usr/bin/time` (rc, unit checks, models, peak RSS).
3. For every `test/models/*.fzn`, stdout, exit code, `.opb` and `.pbp` of the new binary against
   the previous gate's binary, both hashed. A change meant to be byte-identical must show 0
   differences. A comparison whose two sides used the same binary is no evidence (CLAUDE.md).
4. `make diff ARGS="--tier all -j 16"` and `make diff ARGS="--debug --tier all -j 16"`.
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
| `bootstrap.sh` | Installs the toolchain on a fresh machine; safe to re-run |
