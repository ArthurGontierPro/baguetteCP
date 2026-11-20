#!/usr/bin/env python3
"""Summarise a results.tsv of bench/e2e_spike/series.sh (M14-e2e-verification-T8, D-0182).

Usage: python3 -I summarise.py RESULTS.tsv [--rows]

The chain's cost is `veripb --elaborate` + `cake_pb_cp` (check) against `veripb` alone on
baguette's own files, per instance; the bridge (untrusted, written by a Python matcher today
and by the solver once T3 lands) and the encoder are reported apart. Times below 0.05 s are
process start-up, so ratios are given over every VERIFIED instance and over those whose
`veripb` alone took at least 1 s.
"""
import statistics
import sys

COLS = ("id answer verdict t_tr rss_tr t_enc rss_enc t_solve rss_solve t_veripb rss_veripb "
        "t_bridge rss_bridge t_elab rss_elab t_cake rss_cake opb pbp bridged core cake_s_line").split()


def num(x):
    try:
        return float(x)
    except ValueError:
        return None


def main(path, rows=False):
    recs = []
    for line in open(path):
        if line.startswith("#") or not line.strip():
            continue
        f = line.rstrip("\n").split("\t")
        if len(f) < len(COLS) - 1:
            print(f"malformed: {line[:80]!r}", file=sys.stderr)
            continue
        recs.append(dict(zip(COLS, f + [""] * (len(COLS) - len(f)))))
    seen = {}
    for r in recs:   # a rerun replaces an earlier row of the same instance
        seen[r["id"]] = r
    recs = list(seen.values())
    by = {}
    for r in recs:
        by.setdefault(r["verdict"], []).append(r)
    print(f"instances {len(recs)}: " + ", ".join(f"{k} {len(v)}" for k, v in sorted(by.items())))
    ok = by.get("VERIFIED", [])
    kinds = {}
    for r in ok:
        k = r["answer"].split("=")[0]
        kinds[k] = kinds.get(k, 0) + 1
    print("VERIFIED by answer: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())))
    if not ok:
        return 0

    def ratio(r):
        v = num(r["t_veripb"])
        return (num(r["t_elab"]) + num(r["t_cake"])) / max(v, 0.01)

    def show(name, sel):
        if not sel:
            print(f"{name}: none")
            return
        rs = sorted(ratio(r) for r in sel)
        tv = sum(num(r["t_veripb"]) for r in sel)
        te = sum(num(r["t_elab"]) for r in sel)
        tc = sum(num(r["t_cake"]) for r in sel)
        print(f"{name}: n={len(sel)} veripb {tv:.1f} s, elaborate {te:.1f} s, cake_pb_cp {tc:.1f} s; "
              f"total ratio x{(te + tc) / tv:.2f}; per instance median x{statistics.median(rs):.2f}, "
              f"min x{rs[0]:.2f}, max x{rs[-1]:.2f}")
        worst = max(sel, key=ratio)
        print(f"  worst ratio {worst['id']}: veripb {worst['t_veripb']} s, elaborate {worst['t_elab']} s, "
              f"cake {worst['t_cake']} s")
        for st in ("solve", "veripb", "bridge", "elab", "cake", "enc"):
            w = max(sel, key=lambda r: num(r["rss_" + st]) or 0)
            print(f"  peak RSS {st:7s} {num(w['rss_' + st]) / 1024:.2f} GB ({w['id']})")
        tb = sum(num(r["t_bridge"]) for r in sel)
        wb = max(sel, key=lambda r: num(r["t_bridge"]))
        print(f"  bridge {tb:.1f} s in all, worst {wb['t_bridge']} s ({wb['id']}); "
              f"encode {sum(num(r['t_enc']) for r in sel):.1f} s in all")
        for k in ("pbp", "bridged", "core"):
            print(f"  {k:8s} {sum(num(r[k]) for r in sel) / 1e9:.2f} GB in all, "
                  f"largest {max(num(r[k]) for r in sel) / 1e9:.2f} GB")
        cmax = max(sel, key=lambda r: num(r["t_cake"]))
        print(f"  slowest cake_pb_cp {cmax['t_cake']} s ({cmax['id']}, veripb alone {cmax['t_veripb']} s)")

    show("all VERIFIED", ok)
    show("veripb alone >= 1 s", [r for r in ok if num(r["t_veripb"]) >= 1])
    if rows:
        for r in sorted(recs, key=lambda r: num(r["t_veripb"]) or 0):
            print("\t".join(r[c] for c in ("id", "answer", "verdict", "t_solve", "t_veripb", "t_bridge",
                                         "t_elab", "t_cake", "rss_veripb", "rss_elab", "rss_cake",
                                         "pbp", "core")))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], "--rows" in sys.argv[2:]))
