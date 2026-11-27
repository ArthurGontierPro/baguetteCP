#!/usr/bin/env python3
"""M19-config-T0 (D-0205): draw the tuning set from D-0185's three arms, deterministically.

    draw_set.py <repo> <results_dir> [--size 200] [--out bench/tuning/set.lst] [--stats]
                [--exclude bench/tuning/set.lst]

--exclude (D-0252): the ids of that list (first column) are removed from the candidates BEFORE the
rounds, so the same rule draws a set disjoint from it. Without it the draw is D-0205's, unchanged.

<results_dir> holds results_A.tsv results_B.tsv results_C.tsv (D-0185, 1 200 s, release binary
7c880bce). The rule is written in D-0205 and in bench/tuning/README.md; this file is its code.
Standard library only. A re-draw from the same inputs gives the same list (ties by md5 of the id).
"""
import hashlib, os, sys
YEARS = [str(y) for y in range(2011, 2027)]
INPUT = ("FLATTEN-FAIL", "NO-DATA", "INPUT-INVALID")
DIED = ("REFUSED", "CAPPED", "ERROR")
TRIVIAL_S = 10.0   # complete in <= this by every arm
PER_FAMILY_MAX = 6


def read(path):
    rows = {}
    for line in open(path, errors="replace"):
        f = line.rstrip("\n").split("\t")
        if len(f) < 12 or f[1] != "baguette":
            continue
        try:
            t = float(f[3])
        except ValueError:
            t = None
        rows[f[0]] = dict(id=f[0], status=f[2], t=t, obj=f[4], verdict=f[9])
    return rows


def complete(r, trust):
    c = r["status"] in ("OPT", "UNSAT") or (r["status"] == "SAT" and r["obj"] == "-")
    return c and (trust or r["verdict"] == "VERIFIED")


def has_value(r):
    o = r["obj"]
    return ":" in o and o.split(":", 1)[1] not in ("-", "")


def families(repo):
    fam = {}
    for y in YEARS:
        p = os.path.join(repo, "bench/challenge/%s.lst" % y)
        if not os.path.exists(p):
            continue
        for line in open(p):
            if line.startswith("#"):
                continue
            f = line.rstrip("\n").split("\t")
            if len(f) >= 5:
                fam[f[0]] = (y, f[4])      # edition, problem
    return fam


def tier(rs):
    """1 contested, 2 attempted and hard, 3 solved by all but not trivially, 4 nothing to compare,
    None excluded."""
    A, B, C = rs
    if any(r["status"] in INPUT for r in rs):
        return None
    if all(r["status"] in ("REFUSED", "ERROR") for r in rs):
        return None
    comp = [complete(A, False), complete(B, False), complete(C, True)]
    ts = [r["t"] for r in rs if r["t"] is not None]
    if all(comp) and all(r["t"] is not None and r["t"] <= TRIVIAL_S for r in rs):
        return None
    if any(comp) and not all(comp):
        return 1
    if any(r["status"] in DIED for r in rs) and not all(r["status"] in DIED for r in rs):
        return 1                                   # an arm refused or hit the cap, another did not
    objs = {r["obj"] for r in rs if has_value(r)}
    if len(objs) > 1:
        return 1                                   # the arms' incumbents differ
    if all(comp):
        return 3
    if any(has_value(r) for r in rs):
        return 2
    return 4


def main(argv):
    repo, res = argv[1], argv[2]
    size = int(argv[argv.index("--size") + 1]) if "--size" in argv else 200
    out = argv[argv.index("--out") + 1] if "--out" in argv else None
    excl = set()
    if "--exclude" in argv:
        for line in open(argv[argv.index("--exclude") + 1]):
            if line.strip() and not line.startswith("#"):
                excl.add(line.split("\t")[0].strip())
    arms = [read(os.path.join(res, "results_%s.tsv" % a)) for a in "ABC"]
    fam = families(repo)
    cand = {}
    for i in arms[0]:
        if i in arms[1] and i in arms[2] and i in fam and i not in excl:
            t = tier([arms[0][i], arms[1][i], arms[2][i]])
            if t is not None:
                cand[i] = t
    byfam = {}
    for i, t in cand.items():
        byfam.setdefault(fam[i][1], []).append(i)
    h = lambda i: hashlib.md5(i.encode()).hexdigest()
    for f in byfam:
        byfam[f].sort(key=lambda i: (cand[i], h(i)))
    chosen = {}
    # round r gives every family its r-th best instance (tier, then md5), the better tiers first,
    # until size is reached or PER_FAMILY_MAX rounds are done. With more than size/2 families that
    # is one instance per family, then the best second ones.
    rounds = 0
    while len(chosen) < size and rounds < PER_FAMILY_MAX:
        rounds += 1
        want = []
        for f, l in byfam.items():
            k = sum(1 for i in l if i in chosen)
            if k < len(l) and k < rounds:
                nxt = next(i for i in l if i not in chosen)
                want.append((cand[nxt], h(nxt), nxt))
        for _, _, i in sorted(want):
            if len(chosen) < size:
                chosen[i] = cand[i]
    lines = sorted(chosen, key=lambda i: (fam[i][0], fam[i][1], i))
    head = ("# M19-config-T0 tuning set (D-0205), drawn by bench/tuning/draw_set.py from D-0185\n"
            if not excl else
            "# D-0252 held-out set: D-0205's rule (bench/tuning/draw_set.py) from D-0185, size %d,"
            " the %d ids of the --exclude list removed\n" % (size, len(excl)))
    text = head + \
           "# id\tfamily\tedition\ttier\n" + "".join(
               "%s\t%s\t%s\t%d\n" % (i, fam[i][1], fam[i][0], chosen[i]) for i in lines)
    if out:
        open(out, "w").write(text)
    else:
        sys.stdout.write(text)
    from collections import Counter
    sys.stderr.write("candidates %d in %d families; chosen %d in %d families; tiers %s\n" % (
        len(cand), len(byfam), len(chosen), len({fam[i][1] for i in chosen}),
        dict(Counter(chosen.values()))))


main(sys.argv)
