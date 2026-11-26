#!/usr/bin/env python3
"""M17-bench-series-T1 (D-0203). The README's "Performance on the MiniZinc Challenge" section, written
from a series directory instead of copied by hand.

    readme_table.py SERIES_DIR [--record D-0203] [--previous TEXT] [--notes FILE] [--readme README.md]

SERIES_DIR is what bench/series/read_series.sh wrote (SERIES_DIR/tables, or the published copy in
/cluster/arthur/baguette-results/series-<name>): series.conf (the arms, commit, binary hash,
dates), results_<L>.tsv per arm, rank_<L>_<YEAR>.txt (rank_<L>fd_ for a `-f` arm, which is
scored in the fixed-search category so the rows compare), arms.txt (arms_compare.py).

It prints the section on stdout: the settings sentence, the OUTCOME table (one column per arm,
rows that add up to the number of flattened instances, checked), the cost of proof logging (median
ratios of the first `noproof` arm to the first arm, read from arms.txt, and the size of the
verified proofs, whose files the series deletes), and the rank per edition with the summed scores.
--notes FILE is appended as it stands (the caveat paragraphs are prose, written by hand), and
--previous is a one-line pointer to the series before this one. With --readme the section replaces
the one in that file, up to the next `## ` heading, and nothing is printed.
Standard library only; read-only over SERIES_DIR.
"""
import os, re, statistics, sys

YEARS = list(range(2026, 2010, -1))
INPUT = ("FLATTEN-FAIL", "NO-DATA", "INPUT-INVALID")
COMPLETE = ("OPT", "UNSAT", "SAT")
MEMORY_MARK = "SERIES-CHECKER-MEMORY"


def fmt(n):
    return "{:,}".format(n).replace(",", " ")


def conf(tdir):
    c = {"arms": []}
    for line in open(os.path.join(tdir, "series.conf")):
        line = line.rstrip("\n")
        if "=" not in line:
            continue
        k, v = line.split("=", 1)
        if k == "arm":
            label, proof, flags = (v.split(":", 2) + ["", ""])[:3]
            c["arms"].append(dict(label=label, proof=proof == "proof", flags=flags.strip()))
        else:
            c[k] = v
    return c


def rows_of(tdir, label):
    rows = []
    for line in open(os.path.join(tdir, "results_%s.tsv" % label), errors="replace"):
        f = line.rstrip("\n").split("\t")
        if len(f) < 12 or f[0].startswith("DONE-"):
            continue
        rows.append(dict(id=f[0], status=f[2], wall=f[3], obj=f[4], opb=f[7], pbp=f[8],
                         verdict=f[9], detail=f[11]))
    return rows


def has_value(r):
    o = r["obj"]
    return ":" in o and o.split(":", 1)[1] not in ("-", "")


def classify(r, proof):
    s, v = r["status"], r["verdict"]
    if s in INPUT:
        return None
    # M6-T24 (D-0225): a run stopped with a solution. TIMEOUT, or SAT on an OPTIMISATION model
    # (a heap-budget stop with an incumbent exits 0): never an answer, whatever its proof says.
    # A SAT row of an optimisation model is one even when no value could be read ("min:-").
    if (s == "TIMEOUT" and has_value(r)) or (s == "SAT" and ":" in r["obj"]):
        if v == "REJECTED":
            return "rejected"
        if v == "VERIFIED-WEAK":
            return "incumbent_weak"
        return "incumbent_verified" if v == "VERIFIED-INCUMBENT" else "incumbent_unverified"
    if s in COMPLETE:
        if not proof:
            return "complete_unverified_" + ("sat" if s == "SAT" else "opt")
        if v == "VERIFIED":
            return "verified_" + ("sat" if s == "SAT" else "opt")
        if v == "REJECTED":
            return "rejected"
        if v == "TIMEOUT-CHECK":
            return "check_time"
        if v == "CHECK-ERROR" and MEMORY_MARK in r["detail"]:
            return "check_memory"
        return "check_other"  # CHECK-ERROR, VERIFIED-WEAK, NO-PROOF
    return {"TIMEOUT": "timeout", "CAPPED": "capped", "REFUSED": "refused", "ERROR": "crash"}.get(s, "unknown")


def arm_title(a):
    flags = a["flags"]
    search = "Default search" if not flags else ("Free search `-f`" if flags == "-f" else "`%s`" % flags)
    return "%s, %s" % (search, "with proof" if a["proof"] else "`--no-proof`")


def score_label(a):
    if not a["proof"]:
        return "without proof"
    return "with proof" + (" under `%s`" % a["flags"] if a["flags"] else "")


def size(b):
    return "%.0f MB" % (b / 1e6) if b < 1e9 else "%.1f GB" % (b / 1e9)


def outcome_table(c, data):
    arms = c["arms"]
    cols = []
    for a in arms:
        k = {}
        n = 0
        for r in data[a["label"]]:
            t = classify(r, a["proof"])
            if t is None:
                continue
            k[t] = k.get(t, 0) + 1
            n += 1
        k["_n"] = n
        k["_inc"] = sum(1 for r in data[a["label"]] if r["status"] not in INPUT and has_value(r))
        cols.append(k)
    ns = {k["_n"] for k in cols}
    assert len(ns) == 1, "arms disagree on the instance count: %s" % ns
    n = ns.pop()
    rows = [
        ("Optimal or UNSAT, proof verified", "verified_opt", "complete_unverified_opt"),
        ("Satisfiable, proof verified", "verified_sat", "complete_unverified_sat"),
        ("Complete answer, VeriPB hit its time limit (3 600 s)", "check_time", None),
        ("Complete answer, VeriPB ran out of memory (64 GB)", "check_memory", None),
        ("Complete answer, proof check failed for another reason", "check_other", None),
        ("Solution found, not proved optimal, proof verified", "incumbent_verified", None),
        ("Solution found, not proved optimal, proof not verified", "incumbent_unverified", "incumbent_unverified"),
        ("Solution found, the proof records another value", "incumbent_weak", None),
        ("Timeout at 1 200 s, no solution", "timeout", "timeout"),
        ("Proof larger than the harness's cap (none since D-0203)", "capped", None),
        ("Refused, memory budget reached", "refused", "refused"),
        ("Crash", "crash", "crash"),
        ("No cause recorded", "unknown", "unknown"),
    ]
    out = ["| Outcome per instance | " + " | ".join(arm_title(a) for a in arms) + " |",
           "|---|" + "---|" * len(arms)]
    top = {}
    for i, a in enumerate(arms):
        for key in ("verified_opt", "verified_sat"):
            top.setdefault(key, []).append(cols[i].get(key, 0))
    shown_rows = 0
    for label, key, nokey in rows:
        vals = []
        for i, a in enumerate(arms):
            if a["proof"]:
                v = cols[i].get(key, 0)
                s = fmt(v)
            elif nokey is None:
                s = "not applicable"
                v = 0
            else:
                v = cols[i].get(nokey, 0)
                s = fmt(v) + (" (unverified)" if nokey.startswith("complete") else "")
            vals.append((v, s))
        if key in ("check_time", "check_memory", "check_other", "unknown", "incumbent_weak") and not any(v for v, _ in vals):
            continue
        if key == "capped" and not any(v for v, _ in vals):
            continue
        shown_rows += 1
        # Bold the best VERIFIED count; an unverified column is not a competitor.
        ver = [v for (v, _), a in zip(vals, arms) if a["proof"]]
        best = max(ver) if key in ("verified_opt", "verified_sat") and len(ver) > 1 else None
        cells = []
        for (v, s), a in zip(vals, arms):
            cells.append("**%s**" % s if best is not None and a["proof"] and v == best and ver.count(best) == 1 else s)
        out.append("| %s | %s |" % (label, " | ".join(cells)))
    rej = [("**%s**" % fmt(cols[i].get("rejected", 0))) if a["proof"] else "not applicable"
           for i, a in enumerate(arms)]
    out.append("| **Proofs rejected by VeriPB** | " + " | ".join(rej) + " |")
    out.append("| Optimisation runs that printed an objective value (optimal ones included) | "
               + " | ".join(fmt(k["_inc"]) for k in cols) + " |")
    # The rows above the rejected one add up to n, rejected included.
    for i, a in enumerate(arms):
        tot = sum(v for kk, v in cols[i].items() if not kk.startswith("_"))
        assert tot == cols[i]["_n"], (a["label"], tot, cols[i]["_n"])
    return out, n, cols


def parse_pair(tdir, first, other):
    """From arms.txt: the median ratios and the attempts gained of `other` over `first`."""
    p = os.path.join(tdir, "arms.txt")
    if not os.path.exists(p):
        return None
    txt = open(p, errors="replace").read()
    m = re.search(r"^== %s against %s .*?(?=^== |\Z)" % (re.escape(other), re.escape(first)), txt, re.S | re.M)
    if not m:
        return None
    sec = m.group(0)
    res = {}
    for key, rx in (("wall", r"^wall ratio on the (\d+) complete in both: ([\d.]+)"),
                    ("rss", r"^peak RSS ratio \(both >= 64 MB\): ([\d.]+)"),
                    ("nps", r"^nodes/s ratio: ([\d.]+)")):
        mm = re.search(rx, sec, re.M)
        if mm:
            res[key] = mm.group(mm.lastindex)
    mm = re.search(r"^attempts gained by %s .*?: (\d+)" % re.escape(other), txt, re.M)
    if mm:
        res["gained"] = int(mm.group(1))
    comp = 0
    for t in re.finditer(r"^\s+(REFUSED|CAPPED|ERROR)\s+->\s+(OPT|UNSAT|SAT)\s+(\d+)", sec, re.M):
        comp += int(t.group(3))
    res["gained_complete"] = comp
    return res


def rank_cells(tdir, a):
    suffix = "fd" if a["flags"] == "-f" or re.search(r"(^| )-f( |$)", a["flags"]) else ""
    cells, total = [], 0.0
    for y in YEARS:
        p = os.path.join(tdir, "rank_%s%s_%d.txt" % (a["label"], suffix, y))
        rank = ent = None
        score = 0.0
        if os.path.exists(p):
            t = open(p, errors="replace").read()
            m = re.search(r"category, (\d+) entrants", t)
            ent = int(m.group(1)) if m else None
            m = re.search(r"^\s*(\d+)\s+baguette\S*\s+([\d.]+)", t, re.M)
            if m:
                rank, score = int(m.group(1)), float(m.group(2))
        cells.append((rank, ent))
        total += score
    return cells, total


def section(tdir, record, previous, notes):
    c = conf(tdir)
    arms = c["arms"]
    data = {a["label"]: rows_of(tdir, a["label"]) for a in arms}
    tab, n, cols = outcome_table(c, data)
    L = ["## Performance on the MiniZinc Challenge", ""]
    date = (c.get("started", "")[:10] + ("/" + c["ended"][8:10] if c.get("ended") else "")) if c.get("started") else ""
    L.append("All sixteen editions of the MiniZinc Challenge (2011 to 2026, 1 600 instances, %s flattened), "
             "run with the Challenge's own settings: 1 200 s per instance, 16 GiB of memory, one thread, on an "
             "AMD EPYC 7643. An answer with a proof counts only when VeriPB verifies the proof. Measured on %s "
             "(`docs/DECISIONS.md` %s, release binary `%s`, commit `%s`)." % (
                 fmt(n), date.replace("-", "-", 1), record, c.get("binary_md5", "?")[:8], c.get("commit", "?")[:7]))
    L.append("")
    L += tab
    L.append("")
    L.append("The first rows down to the rejected proofs add up to the %s instances, checked when this table was written. "
             "A check that ran out of time or memory is the checker's limit, not a rejected proof, so it is counted apart." % fmt(n))
    L.append("")
    # Cost of proof.
    first = arms[0]
    nop = next((a for a in arms[1:] if not a["proof"]), None)
    pair = parse_pair(tdir, first["label"], nop["label"]) if nop and first["proof"] else None
    if pair and "wall" in pair:
        L.append("What proof logging costs, over the instances both runs complete, comparing the run without "
                 "proof to the run with proof:")
        L.append("")
        L += ["| | median ratio (no proof / proof) |", "|---|---|",
              "| wall time | %s |" % pair["wall"], "| peak memory | %s |" % pair.get("rss", "-"),
              "| nodes per second | %s |" % pair.get("nps", "-"), ""]
        L.append("Without proof, %s instances that hit the memory budget or a crash "
                 "with proof become ordinary attempts, and %s of them end with a complete answer." % (
                     fmt(pair.get("gained", 0)), fmt(pair["gained_complete"])))
        L.append("")
    sizes = sorted(int(r["pbp"]) for a in arms if a["proof"] for r in data[a["label"]]
                   if r["verdict"] == "VERIFIED" and r["pbp"].isdigit())
    if sizes:
        L.append("The %s verified proofs (all proof arms) have a median size of %s, the largest is %s and "
                 "together they were %s. They are deleted once checked, their sizes stay in the tables." % (
                     fmt(len(sizes)), size(statistics.median(sizes)), size(sizes[-1]), size(sum(sizes))))
        L.append("")
    # Ranks.
    ranks = [(a, rank_cells(tdir, a)) for a in arms]
    ent = None
    for a, (cells, tot) in ranks:
        for r, e in cells:
            pass
    ent_cells = ranks[0][1][0]
    L.append("Rank in the fixed-search category of each edition, scored against that year's official entrants "
             "by `tools/compare/challenge_rank.py` (the free-search arm is scored in this category too, so the rows compare):")
    L.append("")
    L.append("| Edition | " + " | ".join(str(y) for y in YEARS) + " |")
    L.append("|---|" + "---|" * len(YEARS))
    L.append("| entrants | " + " | ".join(str(e) if e else "-" for r, e in ent_cells) + " |")
    for a, (cells, tot) in ranks:
        L.append("| %s | %s |" % (arm_title(a).replace("Default search, ", "").replace("Free search `-f`, ", "`-f`, ")
                                  .replace("`--no-proof`", "without proof"),
                                  " | ".join(str(r) if r else "-" for r, e in cells)))
    L.append("")
    L.append("The other entrants do not log proofs. baguette's score summed over the sixteen editions is "
             + ", ".join("%s %s" % (fmt(round(t)), score_label(a)) for a, (cells, t) in ranks)
             + ".")
    L.append("")
    if previous:
        L.append(previous)
        L.append("")
    if notes:
        L.append(open(notes).read().rstrip("\n"))
        L.append("")
    return "\n".join(L)


def main(argv):
    if not argv or argv[0].startswith("-"):
        print(__doc__)
        return 2
    d = argv[0]
    tdir = os.path.join(d, "tables") if os.path.exists(os.path.join(d, "tables", "series.conf")) else d
    opt = {"--record": "D-????", "--previous": None, "--notes": None, "--readme": None}
    i = 1
    while i < len(argv):
        opt[argv[i]] = argv[i + 1]
        i += 2
    s = section(tdir, opt["--record"], opt["--previous"], opt["--notes"])
    if opt["--readme"]:
        t = open(opt["--readme"]).read()
        m = re.search(r"^## Performance on the MiniZinc Challenge\n.*?(?=^## )", t, re.S | re.M)
        assert m, "no performance section in %s" % opt["--readme"]
        open(opt["--readme"], "w").write(t[:m.start()] + s + "\n" + t[m.end():])
    else:
        print(s)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
