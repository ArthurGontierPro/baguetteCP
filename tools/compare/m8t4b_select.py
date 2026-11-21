#!/usr/bin/env python3
"""M8-bits-encoding-T4 continuation (D-0199): choose the TARGETED instance set of the middle-W check
from D-0175's two arms (/scratch/arthur/m8t4/{none,w0}/<Y>/results.tsv).

  (1) every instance that `none` wins over `w0` (complete VERIFIED, or an incumbent `w0` lacks),
      and every instance of the families they belong to, in the sixteen editions;
  (2) a random sample (seed 199) of 40 instances that `w0` wins over `none` (same two criteria),
      drawn outside the families of (1).

FLATTEN-FAIL rows are left out (no .fzn to solve). Prints `<year>\t<id>\t<group>\t<family>` lines.
Usage: python3 -I m8t4b_select.py [<d0175 root>=/scratch/arthur/m8t4] [<repo>=.]"""
import os, random, sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else "/scratch/arthur/m8t4"
REPO = sys.argv[2] if len(sys.argv) > 2 else "."
YEARS = [str(y) for y in range(2011, 2027)]


def family_of(year):
    fam = {}
    for line in open(os.path.join(REPO, "bench/challenge/%s.lst" % year)):
        if line.startswith("#"):
            continue
        f = line.rstrip("\n").split("\t")
        if len(f) >= 3:
            fam[f[0]] = os.path.basename(os.path.dirname(f[1]))
    return fam


def read(arm, year):
    rows = {}
    for line in open(os.path.join(ROOT, arm, year, "results.tsv"), errors="replace"):
        f = line.rstrip("\n").split("\t")
        if len(f) < 12 or f[1] != "baguette":
            continue
        rows[f[0]] = dict(status=f[2], obj=f[4], verdict=f[9])
    return rows


def has_value(r):
    o = r["obj"]
    return ":" in o and o.split(":", 1)[1] not in ("-", "")


def solved(r):  # complete optimisation answer or solved satisfaction problem, proof VERIFIED
    return r["verdict"] == "VERIFIED" and (r["status"] in ("OPT", "UNSAT") or (r["status"] == "SAT" and r["obj"] == "-"))


def wins(a, b):
    return (solved(a) and not solved(b)) or (has_value(a) and not has_value(b))


def main():
    inst = []  # (year, id, family, none row, w0 row)
    for y in YEARS:
        fam, n, w = family_of(y), read("none", y), read("w0", y)
        for i in n:
            if i in w and n[i]["status"] != "FLATTEN-FAIL":
                inst.append((y, i, fam.get(i, "?"), n[i], w[i]))
    order_wins = [t for t in inst if wins(t[3], t[4])]
    fams = sorted({t[2] for t in order_wins})
    group1 = [t for t in inst if t[2] in fams]
    pool = sorted((t for t in inst if t[2] not in fams and wins(t[4], t[3])), key=lambda t: t[1])
    sample = random.Random(199).sample(pool, 40)
    win_ids = {t[1] for t in order_wins}
    for t in group1:
        print("%s\t%s\t%s\t%s" % (t[0], t[1], "order-win" if t[1] in win_ids else "order-family", t[2]))
    for t in sorted(sample, key=lambda t: t[1]):
        print("%s\t%s\t%s\t%s" % (t[0], t[1], "w0-win", t[2]))
    print("# order wins %d in families %s; family rows %d; w0-win pool %d, sampled 40"
          % (len(order_wins), ",".join(fams), len(group1), len(pool)), file=sys.stderr)


main()
