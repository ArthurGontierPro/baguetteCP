#!/usr/bin/env python3
"""Shrink a fuzz disagreement (M22-review-T7, D-0258): delete `constraint` lines of a kept m.mzn,
and turn an objective into `solve satisfy`, one at a time, while the same verdict reproduces.

Usage: shrink_mzn.py IN.mzn OUT.mzn VERDICT [FLAG...]
  VERDICT   the verdict to preserve (STATUS-MISMATCH, PROOF-REJECTED, BAD-SOLUTION, ...), as
            streams.py's check_run names it
  FLAG...   baguette flags of the failing configuration; env assignments NAME=VALUE among them
            are passed as the environment (e.g. BAGUETTE_RETENTION=fifo:1 --cdcl)

The result is a local minimum (no single deletion keeps the verdict), not the smallest model.
Same environment as streams.py (FUZZ_BIN, FUZZ_MZNLIB). Exit 0 with OUT.mzn written, 1 when the
input does not reproduce the verdict."""
import os, re, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import streams as S  # noqa: E402


def verdict_of(ctx, mzn, flags, env):
    model = S.Model(ctx, mzn, 0)
    v = S.pre(ctx, model)
    if v:
        return v
    run = S.bag(model, flags, env, os.path.join(ctx.outdir, "p"), timeout=60)
    return S.check_run(ctx, model, run, cfg="shrink", all_sols=True)[0]


def main():
    if len(sys.argv) < 4:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    src, dst, want = sys.argv[1], sys.argv[2], sys.argv[3]
    flags = [a for a in sys.argv[4:] if not re.match(r"^[A-Z_]+=", a)]
    env = dict(a.split("=", 1) for a in sys.argv[4:] if re.match(r"^[A-Z_]+=", a))
    tmp = tempfile.mkdtemp(prefix="shrink-", dir=os.path.dirname(os.path.abspath(dst)))
    ctx = S.Ctx("shrink", tmp, 0)
    lines = open(src).read().splitlines(keepends=True)
    if verdict_of(ctx, "".join(lines), flags, env) != want:
        print("does not reproduce %s" % want, file=sys.stderr)
        sys.exit(1)
    changed = True
    while changed:
        changed = False
        for i in range(len(lines)):
            ln = lines[i]
            if ln.startswith("constraint "):
                cand = lines[:i] + lines[i + 1:]
            elif re.match(r"^solve (minimize|maximize) ", ln):
                cand = lines[:i] + ["solve satisfy;\n"] + lines[i + 1:]
            else:
                continue
            if verdict_of(ctx, "".join(cand), flags, env) == want:
                lines = cand
                changed = True
                break
    open(dst, "w").write("".join(lines))
    print("%s: %d lines" % (dst, len(lines)))


if __name__ == "__main__":
    main()
