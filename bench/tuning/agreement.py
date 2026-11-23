#!/usr/bin/env python3
"""M19-config-T0 (D-0205): does the tuning set rank the arms as the full set does?

    agreement.py <repo> bench/tuning/set.lst NAME=results.tsv [NAME=results.tsv ...] [--trust NAME] [--cut SECONDS]

For each arm: complete (verified unless --trust), incumbents, and a Borda score under the Challenge's
order (arms_compare.verdict: complete > better objective > nothing, two complete answers by time,
ties within 5 % or 1 s): per instance each arm gets 1 per arm it beats and 0.5 per tie. Printed for
the full set and for the subset, with the ordering and each arm's share of the total score, then
the per-pair wins/losses on both. Standard library only.
"""
import os, sys
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "../../tools/compare"))
import arms_compare as ac


def load(path, trust, cut=None):
    rows = {}
    for line in open(path, errors="replace"):
        f = line.rstrip("\n").split("\t")
        if len(f) < 12 or f[1] != "baguette":
            continue
        r = dict(id=f[0], status=f[2], wall=f[3], obj=f[4], verdict=f[9], trust=trust)
        try:
            r["t"] = float(f[3])
        except ValueError:
            r["t"] = None
        if cut and r["t"] is not None and r["t"] > cut and r["status"] in ("OPT", "UNSAT", "SAT"):
            r["status"], r["verdict"] = "TIMEOUT", "NOT-CHECKED"   # a 1 200 s answer after the cut
            # (its incumbent at the cut is unknown, the 1 200 s one is kept: optimistic)
        rows[f[0]] = r
    return rows


def main(argv):
    lst = argv[2]
    trust = argv[argv.index("--trust") + 1] if "--trust" in argv else None
    arms = [a.split("=", 1) for a in argv[3:] if "=" in a]
    cut = float(argv[argv.index("--cut") + 1]) if "--cut" in argv else None
    data = {n: load(p, n == trust, cut) for n, p in arms}
    sub = {l.split("\t")[0] for l in open(lst) if not l.startswith("#")}
    ids = sorted(set.intersection(*[set(d) for d in data.values()]))
    ids = [i for i in ids if not any(data[n][i]["status"] in ac.INPUT for n in data)]
    for label, sel in (("full set", ids), ("tuning set", [i for i in ids if i in sub])):
        score = {n: 0.0 for n in data}
        comp = {n: 0 for n in data}
        inc = {n: 0 for n in data}
        pw = {}
        for i in sel:
            for n in data:
                comp[n] += ac.complete(data[n][i])
                inc[n] += ac.has_value(data[n][i])
            names = list(data)
            for a in range(len(names)):
                for b in range(a + 1, len(names)):
                    v = ac.verdict(data[names[a]][i], data[names[b]][i])   # +1: b better
                    score[names[b]] += (1 + v) / 2
                    score[names[a]] += (1 - v) / 2
                    w = pw.setdefault((names[a], names[b]), [0, 0, 0])
                    w[0 if v > 0 else 1 if v < 0 else 2] += 1
        tot = sum(score.values())
        order = sorted(data, key=lambda n: -score[n])
        print("== %s: %d instances; order %s" % (label, len(sel), " > ".join(order)))
        for n in order:
            print("   %-3s score %7.1f (%.3f of total, %.3f per instance)  complete %d  incumbents %d" % (
                n, score[n], score[n] / tot, score[n] / len(sel) / (len(data) - 1), comp[n], inc[n]))
        for (a, b), w in pw.items():
            print("   %s over %s: %d wins, %d losses, %d ties" % (b, a, w[0], w[1], w[2]))


main(sys.argv)
