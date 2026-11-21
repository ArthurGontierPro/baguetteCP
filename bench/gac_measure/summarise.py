#!/usr/bin/env python3
r"""M4-T6b (D-0194): per-family table of bounds against GAC, from gecode_pair.sh's
gecode.tsv or bag_pair.sh's bag.tsv.

  summarise.py gecode RUN/gecode.tsv [MINMAX]   or   summarise.py bag RUN/bag.tsv [MINMAX]

MINMAX is a file of `id<TAB>min|max|sat` (the objective sense) used to decide which
objective is better when both arms hit the limit; without it the sense is read from
nothing and a differing objective is reported as `obj-differs`.

Per instance: `both-closed` when both arms closed the search (OPT/UNSAT/SAT), and the
node ratio G/B; `answer-change` when one arm closed and the other did not, or when both
hit the limit with a different best objective. Per family: instances, both-closed, the
geometric mean of G/B over both-closed, the min and max ratio, the time ratio, and how many
answer changes go each way (GAC_better: GAC closed where bounds did not, or found a better
objective at the limit; GAC_worse: the reverse).
"""
import collections
import math
import sys

CLOSED = {"OPT", "UNSAT", "SAT"}


def main():
    mode, path = sys.argv[1], sys.argv[2]
    # columns after the id: gecode: tab arith  B(st nodes fail time obj nsol) G(...)
    #                        bag:    twin arith flags B(st nodes fail time obj) G(...)
    pre, w = (2, 6) if mode == "gecode" else (3, 5)
    fam = collections.defaultdict(lambda: dict(n=0, skip=0, err=0, better=0, worse=0, closed=0, ratios=[], changes=[],
                                               tratio=[]))
    rows = []
    senses = {}
    if len(sys.argv) > 3:
        for line in open(sys.argv[3]):
            f = line.split()
            if len(f) >= 2:
                senses[f[0]] = f[1]
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        ident = f[0]
        family = "codes" if ident.startswith("codes_") else ident.split("_")[1]
        d = fam[family]
        if len(f) < 1 + pre + 2 * w:
            d["skip"] += 1
            rows.append((ident, f[1:]))
            continue
        b = f[1 + pre:1 + pre + w]
        g = f[1 + pre + w:1 + pre + 2 * w]
        bst, gst = b[0].split("/")[0], g[0].split("/")[0]
        # no statistics block: the run died before printing it (a crash or the memory
        # scope), whatever solutions it printed first
        bst = "ERR" if b[1] == "-" else bst
        gst = "ERR" if g[1] == "-" else gst
        d["n"] += 1
        note = ""
        if bst in CLOSED and gst in CLOSED:
            d["closed"] += 1
            bn, gn = max(1, int(b[1])), max(1, int(g[1]))
            r = gn / bn
            d["ratios"].append(r)
            try:
                d["tratio"].append(max(1e-3, float(g[3])) / max(1e-3, float(b[3])))
            except ValueError:
                pass
            note = f"G/B nodes {r:.3f}"
            if bst != gst:
                note += f" STATUS {bst}->{gst}"
                d["changes"].append(ident)
        elif "ERR" in (bst, gst):
            note = f"error {bst}/{gst}"
            d["err"] += 1
        elif (bst in CLOSED) != (gst in CLOSED):
            d["better" if gst in CLOSED else "worse"] += 1
            note = f"ANSWER {bst}->{gst}"
            d["changes"].append(ident + f"({bst}->{gst})")
        else:
            if b[4] != g[4]:
                sense = senses.get(ident, "?")
                verdict = "differs"
                if b[4] == "-" or g[4] == "-":
                    verdict = "GAC-better" if b[4] == "-" else "GAC-worse"
                elif sense in ("min", "max"):
                    better = int(g[4]) < int(b[4]) if sense == "min" else int(g[4]) > int(b[4])
                    verdict = "GAC-better" if better else "GAC-worse"
                note = f"obj {verdict} {b[4]}->{g[4]}"
                d["changes"].append(ident + f"(obj {verdict} {b[4]}->{g[4]})")
                d["better" if verdict == "GAC-better" else "worse"] += 1
            else:
                note = f"limit, same obj {b[4]}"
        rows.append((ident, [bst, b[1], b[4], gst, g[1], g[4], note]))
    for ident, r in rows:
        print("#", ident, *r, sep="\t")
    print("family\tran\tskipped\terr\tboth_closed\tgeo_G/B_nodes\tmin\tmax\tgeo_G/B_time\tGAC_better\tGAC_worse\tanswer_changes")
    for k in sorted(fam):
        d = fam[k]
        rs = d["ratios"]
        gm = math.exp(sum(map(math.log, rs)) / len(rs)) if rs else float("nan")
        tm = math.exp(sum(map(math.log, d["tratio"])) / len(d["tratio"])) if d["tratio"] else float("nan")
        print(k, d["n"], d["skip"], d["err"], d["closed"], f"{gm:.3f}", f"{min(rs):.3f}" if rs else "-",
              f"{max(rs):.3f}" if rs else "-", f"{tm:.3f}", d["better"], d["worse"], ";".join(d["changes"]) or "-", sep="\t")


if __name__ == "__main__":
    main()
