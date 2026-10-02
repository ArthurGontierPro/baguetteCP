#!/usr/bin/env python3
"""Solve + check a range of generated models, keep only the failures (M7-T21, D-0084).

    (ulimit -v 4000000; python3 bench/fuzz/run.py MODE FIRST_SEED COUNT OUTDIR)

For each seed: write the model, run the solver with --proof, run veripb, classify:

    ok            solver exit 0 and veripb accepted          (files deleted)
    refused       the solver refused the model (outside SPEC 2.1) (files deleted)
    crash         solver exit != 0 otherwise                 (kept)
    timeout       solver or checker hit its timeout          (kept)
    rejected      veripb refused; prints the line number, the line, and the
                  checker's last message                     (kept)

One line per non-ok seed on stdout, a summary at the end. Kept files are
OUTDIR/m<seed>.{fzn,opb,pbp,log}. Exit status 1 if anything was kept.

Environment: BAGUETTE (solver, default _build/default/bin/main.exe under the
checkout this file lives in), VERIPB (default: scripts/checker.sh's choice is not
sourced here; ~/.cargo/bin/veripb, then `veripb` on PATH). Build the solver first
(`dune build --root . bin/`) -- this script does not, and a stale binary is a
measurement of the stale binary (CLAUDE.md).

NOT part of `make check`, and must not become part of it: it is a search for
defects, its runtime is unbounded in COUNT, and a found defect is a finding to
reduce and record, not a red gate.
"""
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from gen import MODES, gen  # noqa: E402

SOLVER = os.environ.get("BAGUETTE", os.path.join(ROOT, "_build/default/bin/main.exe"))
VERIPB = os.environ.get("VERIPB") or (
    os.path.expanduser("~/.cargo/bin/veripb")
    if os.path.exists(os.path.expanduser("~/.cargo/bin/veripb"))
    else shutil.which("veripb"))
SOLVE_S, CHECK_S = 20, 60


def run(cmd, t):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=t)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return None, "", ""


def one(mode, seed, out):
    p = os.path.join(out, f"m{seed}")
    files = [p + x for x in (".fzn", ".opb", ".pbp", ".log")]
    with open(p + ".fzn", "w") as f:
        f.write(gen(mode, seed))

    def drop():
        for x in files:
            if os.path.exists(x):
                os.remove(x)

    rc, so, se = run([SOLVER, p + ".fzn", "--proof", p], SOLVE_S)
    if rc is None:
        return "timeout", "solver"
    if rc != 0:
        if re.search(r"unsupported|refus|not in the", se, re.I):
            drop()
            return "refused", ""
        with open(p + ".log", "w") as f:
            f.write(se)
        return "crash", f"exit {rc}: " + se.strip().splitlines()[-1][:160] if se.strip() else f"exit {rc}"
    verdict = "UNSAT" if "UNSATISFIABLE" in so else "SAT"
    rc, vo, ve = run([VERIPB, p + ".opb", p + ".pbp"], CHECK_S)
    if rc is None:
        return "timeout", "veripb"
    if rc == 0:
        drop()
        return "ok", ""
    msg = vo + ve
    with open(p + ".log", "w") as f:
        f.write(msg)
    m = re.search(r"\.pbp:(\d+)", msg)
    ln = int(m.group(1)) if m else -1
    line = "?"
    if ln > 0:
        with open(p + ".pbp") as f:
            ls = f.read().split("\n")
        line = ls[ln - 1][:120] if ln <= len(ls) else "?"
    last = msg.strip().splitlines()[-1].strip()[:110] if msg.strip() else ""
    return "rejected", f"{verdict} L{ln} {line} | {last}"


def main():
    if len(sys.argv) != 5 or sys.argv[1] not in MODES:
        sys.exit(f"usage: run.py {{{'|'.join(MODES)}}} FIRST_SEED COUNT OUTDIR")
    if not VERIPB:
        sys.exit("run.py: no veripb found -- a sweep with no checker checks nothing")
    if not os.path.exists(SOLVER):
        sys.exit(f"run.py: no solver at {SOLVER}; build it first")
    mode, first, count, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    os.makedirs(out, exist_ok=True)
    tally = {}
    for seed in range(first, first + count):
        kind, info = one(mode, seed, out)
        tally[kind] = tally.get(kind, 0) + 1
        if kind not in ("ok", "refused"):
            print(f"{mode} {seed} {kind} {info}", flush=True)
    print("summary: " + " ".join(f"{k}={v}" for k, v in sorted(tally.items())))
    sys.exit(1 if any(k not in ("ok", "refused") for k in tally) else 0)


if __name__ == "__main__":
    main()
