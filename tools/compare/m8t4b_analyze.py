#!/usr/bin/env python3
"""Read the four arms (none, w0, w64, w100) of the targeted middle-W check of the bits encoding,
one compare_run.sh output dir per (arm, year, id) under <root>/<arm>/<year>/<id>/. W is the
solver's --bits-above: an eligible variable declared wider than W gets the bits (binary)
encoding instead of the order encoding; `none` never uses bits. A one-off analysis of the
continuation of M8-bits-encoding-T4 (the measurement that chose the default W), recorded as
D-0199: a middle W wins back 4 of the 14 complete answers the order encoding had over W = 0.

Usage: python3 -I m8t4b_analyze.py [<root>=/scratch/arthur/m8t4b] [<repo>=.]   (read-only on the runs)
Reads <root>/selection.tsv (m8t4b_select.py's output) and the flatten tables of D-0175's run,
/scratch/arthur/m8t4/flat/<year>/flatten.tsv (a fixed path). Writes <root>/per_instance.tsv
and, per arm and edition, <root>/merged/<arm>/<year>/{results,flatten}.tsv (the selected instances
only, plus the DONE line) for challenge_rank.py, then prints the tables on stdout. Exit 0; a
missing selection.tsv or flatten table stops on a Python exception (status 1). <repo> is
read but not used."""
import glob, os, re, sys
from collections import Counter, defaultdict

ROOT = sys.argv[1] if len(sys.argv) > 1 else "/scratch/arthur/m8t4b"
REPO = sys.argv[2] if len(sys.argv) > 2 else "."
ARMS = ["none", "w0", "w64", "w100"]
R_NODES = re.compile(r"^stats: nodes\s+(\d+)", re.M)
R_BITS = re.compile(r"^stats: bits\s+(\d+) vars", re.M)
R_RSS = re.compile(r"rss_kb=(\d+)")


def read_one(d, i):
    tsv = os.path.join(d, "results.tsv")
    if not os.path.exists(tsv):
        return None
    lines = open(tsv, errors="replace").read().splitlines()
    done = [l for l in lines if l.startswith("DONE-")]
    rows = [l.split("\t") for l in lines if l.startswith(i + "\t")]
    if not rows or not done:
        return None
    f = rows[-1]
    r = dict(line="\t".join(f), status=f[2], wall=f[3], obj=f[4], verdict=f[9])
    L = os.path.join(d, "log", i + ".baguette")
    try:
        err = open(L + ".err", errors="replace").read()
    except OSError:
        err = ""
    m = R_NODES.findall(err)
    r["nodes"] = int(m[-1]) if m else None
    m = R_BITS.search(err)
    r["bits"] = int(m.group(1)) if m else None
    try:  # veripb rc 134 under the harness's 16 GiB ulimit -v: the checker's memory, not a judgement
        r["chkmem"] = r["verdict"] == "CHECK-ERROR" and "memory allocation of" in open(L + ".vp", errors="replace").read()
    except OSError:
        r["chkmem"] = False
    try:
        r["rss"] = int(R_RSS.search(open(L + ".rss").read()).group(1))
    except (OSError, AttributeError):
        r["rss"] = None
    return r


def has_value(r):
    o = r["obj"]
    return ":" in o and o.split(":", 1)[1] not in ("-", "")


def solved(r):
    """complete (OPT/UNSAT) or a solved satisfaction problem, with the proof VERIFIED -- or with the check
    stopped by the checker's own memory (CHECK-ERROR rc 134, `memory allocation ... failed`), counted as
    complete the same way in every arm (orchestrator, 2026-11-21: re-checked under 32 GB, such a proof
    verifies). Proof-side failures (REJECTED) and TIMEOUT-CHECK are not counted."""
    return (r["verdict"] == "VERIFIED" or r.get("chkmem")) and (r["status"] in ("OPT", "UNSAT") or (r["status"] == "SAT" and r["obj"] == "-"))


def quality(r):
    """(rank, objective value to compare) for the pairwise rule among the arms."""
    if solved(r):
        return (2, 0)
    if has_value(r):
        k, v = r["obj"].split(":", 1)
        return (1, int(v) if k == "min" else -int(v))
    return (0, 0)


def main():
    sel = [l.rstrip("\n").split("\t") for l in open(os.path.join(ROOT, "selection.tsv"))]
    data = {}
    for y, i, g, fam in sel:
        data[i] = (y, g, fam, {a: read_one(os.path.join(ROOT, a, y, i), i) for a in ARMS})
    missing = Counter(a for (_, _, _, rs) in data.values() for a in ARMS if rs[a] is None)
    print("== runs not finished:", dict(missing) or 0)

    # merged per-edition tables for challenge_rank.py
    for a in ARMS:
        for y in sorted({v[0] for v in data.values()}):
            d = os.path.join(ROOT, "merged", a, y)
            os.makedirs(d, exist_ok=True)
            with open(os.path.join(d, "results.tsv"), "w") as out:
                for i, (yy, _, _, rs) in sorted(data.items()):
                    if yy == y and rs[a] is not None:
                        out.write(rs[a]["line"] + "\n")
                out.write("DONE-0\t0\t0\n")
            src = os.path.join("/scratch/arthur/m8t4/flat", y, "flatten.tsv")
            with open(src) as s, open(os.path.join(d, "flatten.tsv"), "w") as o:
                o.write(s.read())

    groups = ["order-win", "order-family", "w0-win"]
    keys = ["solved", "of which chk-mem", "incumbent", "TIMEOUT-noval", "REFUSED", "CAPPED", "unverified"]
    with open(os.path.join(ROOT, "per_instance.tsv"), "w") as out:
        out.write("id\tgroup\tfamily\t" + "\t".join("%s_%s" % (k, a) for a in ARMS for k in ("status", "obj", "verdict", "wall", "bits", "rss_kb")) + "\n")
        for i, (y, g, fam, rs) in sorted(data.items()):
            cols = []
            for a in ARMS:
                r = rs[a]
                cols += ["-"] * 6 if r is None else [r["status"], r["obj"], r["verdict"], r["wall"], str(r["bits"]), str(r["rss"])]
            out.write("\t".join([i, g, fam] + cols) + "\n")

    def tally(ids):
        c = {a: Counter() for a in ARMS}
        for i in ids:
            rs = data[i][3]
            for a in ARMS:
                r = rs[a]
                if r is None:
                    continue
                c[a]["solved"] += solved(r)
                c[a]["of which chk-mem"] += solved(r) and r["verdict"] != "VERIFIED"
                c[a]["incumbent"] += has_value(r)
                c[a]["TIMEOUT-noval"] += r["status"] == "TIMEOUT" and not has_value(r)
                c[a]["REFUSED"] += r["status"] == "REFUSED"
                c[a]["CAPPED"] += r["status"] == "CAPPED"
                c[a]["unverified"] += r["status"] in ("OPT", "UNSAT") and not solved(r)
        return c

    def pairwise(ids):
        """the Challenge's complete rule among the four arms only: better quality 1, equal quality split
        by solve time for complete answers (0.5 otherwise)."""
        s = Counter()
        for i in ids:
            rs = data[i][3]
            if any(rs[a] is None for a in ARMS):
                continue
            for a in ARMS:
                for b in ARMS:
                    if a == b:
                        continue
                    qa, qb = quality(rs[a]), quality(rs[b])
                    if qa[0] != qb[0]:
                        s[a] += qa[0] > qb[0]
                    elif qa[0] == 1 and qa[1] != qb[1]:
                        s[a] += qa[1] < qb[1]
                    elif qa[0] == 2:
                        ta, tb = float(rs[a]["wall"]), float(rs[b]["wall"])
                        s[a] += 0.5 if ta + tb == 0 else tb / (ta + tb)
                    else:
                        s[a] += 0.5
        return s

    def show(title, ids):
        c, s = tally(ids), pairwise(ids)
        print("== %s (%d instances): %s | pairwise among arms" % (title, len(ids), " / ".join(keys)))
        for a in ARMS:
            print("   %-5s %s | %.1f" % (a, " / ".join(str(c[a][k]) for k in keys), s[a]))

    show("ALL", list(data))
    for g in groups:
        show(g, [i for i in data if data[i][1] == g])
    for fam in sorted({v[2] for v in data.values() if v[1] != "w0-win"}):
        show("family " + fam, [i for i in data if data[i][2] == fam])

    print("== order-win instances, status/obj/verdict per arm")
    for i, (y, g, fam, rs) in sorted(data.items()):
        if g == "order-win":
            print("  ", i, " | ".join("%s %s %s %s" % (a, r["status"], r["obj"], r["verdict"][:4]) if r else a + " -"
                                      for a, r in ((a, rs[a]) for a in ARMS)))
    print("== where W=64 / W=100 differ from both none and w0 in quality (solved/incumbent)")
    for i, (y, g, fam, rs) in sorted(data.items()):
        if any(rs[a] is None for a in ARMS):
            continue
        q = {a: quality(rs[a])[0] for a in ARMS}
        if len(set(q.values())) > 1:
            print("  ", i, g, " ".join("%s=%d" % (a, q[a]) for a in ARMS),
                  "bits:" + ",".join(str(rs[a]["bits"]) for a in ARMS))


main()
