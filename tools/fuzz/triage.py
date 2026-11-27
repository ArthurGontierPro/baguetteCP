#!/usr/bin/env python3
"""Re-judge kept fuzz disagreements (M22-review-T7, D-0258): for each OUTDIR/.../bad/<case>/,
run its m.mzn again under the configuration its name records, with the binary and mznlib of
the environment (FUZZ_BIN, FUZZ_MZNLIB), and print `<case> <old verdict> -> <new verdict>`.
Point FUZZ_BIN at a fix's build to tell a known defect (fixed there) from a new one, or at an
older build to tell a regression. The `configs` stream's configuration names are streams.py's
CONFIGS; other cases run under the default flags (`-i` for an incr case named `_i`).

Usage: triage.py CASE_DIR...    (exit 0; one line per case)"""
import os, re, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import streams as S  # noqa: E402

CFG = {name: (flags, env) for name, flags, env in S.CONFIGS}


def main():
    tmp = tempfile.mkdtemp(prefix="triage-")
    ctx = S.Ctx("triage", tmp, 0)
    for case in sys.argv[1:]:
        base = os.path.basename(case.rstrip("/"))
        m = re.match(r"^\d+_\d+_([A-Za-z-]+)(?:_(.*))?$", base)
        old, cfg = (m.group(1), m.group(2)) if m else ("?", None)
        flags, env = CFG.get(cfg, ([], {}))
        if cfg == "i":
            flags = ["-i"]
        mm = re.match(r"^nodes(\d+)(-cdcl)?$", cfg or "")
        if mm:
            flags, env = (["--cdcl"] if mm.group(2) else []), {"BAGUETTE_NODE_LIMIT": mm.group(1)}
        mt = re.match(r"^t(\d+)ms$", cfg or "")
        if mt:
            flags = ["-t", mt.group(1)]
        model = S.Model(ctx, open(os.path.join(case, "m.mzn")).read(), 0, gecode_timeout=60)
        v = S.pre(ctx, model)
        if not v:
            run = S.bag(model, flags, env, os.path.join(tmp, "p"), timeout=60)
            v = S.check_run(ctx, model, run, cfg=cfg, all_sols=True)[0]
        print("%s %s -> %s" % (base, old, v), flush=True)


if __name__ == "__main__":
    main()
