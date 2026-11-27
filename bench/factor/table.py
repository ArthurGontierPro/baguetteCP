#!/usr/bin/env python3
"""The per-node factor lane's tables (M17-bench-series-T6, D-0256). Called by
scripts/factor_lane.sh, not by hand:

    table.py OUTDIR REFERENCE_TSV MD5 COMMIT HOST DATE RECORD WALL

Reads OUTDIR/plan.selected and OUTDIR/runs/<id>.<config>/{base,full}/ (perf.txt, err, out, rc,
verdict), writes OUTDIR/factor.tsv and OUTDIR/factor.txt, prints the text, and with RECORD=1 writes
REFERENCE_TSV. Exit 0 when every run finished and every proof was VERIFIED, 1 otherwise. The rules
(cost per unit, which unit, the factor, the geometric mean) are stated in the lane's header.
"""
import math
import os
import re
import sys

CONFIGS = ["pf", "np", "cdpf", "cdnp"]
CONFIG_TEXT = {"pf": "default, proof", "np": "default, --no-proof",
               "cdpf": "--cdcl, proof", "cdnp": "--cdcl, --no-proof"}
SAME_TREE = 0.02
COLS = ["id", "family", "config", "ref", "unit", "tree", "nodes", "failures", "kinstr_per_unit",
        "ref_nodes", "ref_failures", "ref_kinstr_per_unit", "factor", "answer", "ref_answer",
        "verdict", "pbp_bytes"]


def read(path):
    try:
        with open(path, errors="replace") as f:
            return f.read()
    except OSError:
        return None


def instructions(d):
    t = read(os.path.join(d, "perf.txt")) or ""
    for line in t.splitlines():
        f = line.split(",")
        if len(f) > 2 and f[2].startswith("instructions") and f[0].isdigit():
            return int(f[0])
    return None


def answer(out):
    if out is None:
        return "?"
    if "=====UNSATISFIABLE=====" in out:
        return "UNSAT"
    if "=====ERROR=====" in out:
        return "ERROR"
    if "==========" in out:
        return "COMPLETE"
    if "----------" in out:
        return "SAT"
    if "=====UNKNOWN=====" in out:
        return "LIMIT"
    return "NONE"


def bag_stage(d):
    err = read(os.path.join(d, "err")) or ""
    def stat(name):
        m = re.search(r"^stats: %s\s+(\d+)" % name, err, re.M)
        return int(m.group(1)) if m else None
    return {"rc": (read(os.path.join(d, "rc")) or "?").strip(), "instr": instructions(d),
            "nodes": stat("nodes"), "fail": stat("conflicts"),
            "answer": answer(read(os.path.join(d, "out"))),
            "verdict": (read(os.path.join(d, "verdict")) or "").strip(),
            "pbp": (read(os.path.join(d, "pbpsize")) or "").strip()}


def ref_stage(d):
    out = read(os.path.join(d, "out")) or ""
    def stat(name):
        m = re.search(r"^%%%%%%mzn-stat: %s=(\d+)" % name, out, re.M)
        return int(m.group(1)) if m else None
    return {"rc": (read(os.path.join(d, "rc")) or "?").strip(), "instr": instructions(d),
            "nodes": stat("nodes"), "fail": stat("failures"), "answer": answer(out)}


def per(full, base, key):
    if full["instr"] is None or base["instr"] is None or full[key] is None or base[key] is None:
        return None
    du = full[key] - base[key]
    return (full["instr"] - base["instr"]) / du if du > 0 else None


def close(a, b):
    return a is not None and b is not None and abs(a - b) <= SAME_TREE * max(b, 1)


def geomean(xs):
    xs = [x for x in xs if x is not None and x > 0]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else None


def fx(x):
    if x is None:
        return "-"
    return "%.0f" % x if x >= 100 else "%.1f" % x if x >= 10 else "%.2f" % x


def kfmt(x):
    if x is None:
        return "-"
    k = x / 1000.0
    s = "%.0f" % k if k >= 100 else "%.1f" % k
    if k >= 1000:
        s = "{:,}".format(int(round(k))).replace(",", " ")
    return s


def main():
    out, ref_tsv, md5, commit, host, date, record, wall = sys.argv[1:9]
    record = record == "1"
    plan = [l.split("\t") for l in (read(os.path.join(out, "plan.selected")) or "").splitlines() if l]
    rows, broken, unchecked = [], [], []
    for id_, fam, blim, refname, rlim, _bf, _rf in plan:
        rd = os.path.join(out, "runs", id_ + ".ref")
        rb, rfull = ref_stage(os.path.join(rd, "base")), ref_stage(os.path.join(rd, "full"))
        for st, name in ((rb, "base"), (rfull, "full")):
            if st["rc"] != "0" or st["instr"] is None or st["nodes"] is None or st["fail"] is None:
                broken.append("%s %s %s: rc %s, instructions %s, nodes %s, failures %s"
                              % (id_, refname, name, st["rc"], st["instr"], st["nodes"], st["fail"]))
        for c in CONFIGS:
            d = os.path.join(out, "runs", "%s.%s" % (id_, c))
            b, f = bag_stage(os.path.join(d, "base")), bag_stage(os.path.join(d, "full"))
            for st, name in ((b, "base"), (f, "full")):
                if st["rc"] != "0" or st["instr"] is None or st["nodes"] is None or st["fail"] is None:
                    broken.append("%s %s %s: rc %s, instructions %s, nodes %s, failures %s"
                                  % (id_, c, name, st["rc"], st["instr"], st["nodes"], st["fail"]))
                if c.endswith("pf") and not st["verdict"].startswith("s VERIFIED"):
                    unchecked.append("%s %s %s: %s" % (id_, c, name, st["verdict"] or "no verdict"))
            same = (not c.startswith("cd") and close(f["nodes"], rfull["nodes"])
                    and close(f["fail"], rfull["fail"]))
            unit = "node" if same else "failure"
            key = "nodes" if same else "fail"
            bc, rc = per(f, b, key), per(rfull, rb, key)
            factor = bc / rc if bc is not None and rc else None
            rows.append({"id": id_, "family": fam, "config": c, "ref": refname, "unit": unit,
                         "tree": "same" if same else "own", "nodes": f["nodes"], "failures": f["fail"],
                         "kinstr_per_unit": None if bc is None else bc / 1000.0,
                         "ref_nodes": rfull["nodes"], "ref_failures": rfull["fail"],
                         "ref_kinstr_per_unit": None if rc is None else rc / 1000.0,
                         "factor": factor, "answer": f["answer"], "ref_answer": rfull["answer"],
                         "verdict": f["verdict"] if c.endswith("pf") else "-",
                         "pbp_bytes": f["pbp"] if c.endswith("pf") else "-"})

    def cell(v):
        if v is None:
            return "-"
        if isinstance(v, float):
            return "%.4f" % v
        return str(v)

    tsv = "\t".join(COLS) + "\n" + "".join(
        "\t".join(cell(r[k]) for k in COLS) + "\n" for r in rows)
    with open(os.path.join(out, "factor.tsv"), "w") as fh:
        fh.write(tsv)

    L = []
    L.append("per-node factor: binary %s, commit %s, host %s, %s, %s s" % (md5, commit, host, date, wall))
    L.append("thousands of user instructions per unit (node on the same tree, else failure on each")
    L.append("solver's own tree), and in brackets the factor over the reference on the same unit")
    L.append("")
    hdr = "%-11s %-10s %-22s" % ("instance", "family", "reference k/node k/fail")
    hdr += "".join(" | %-24s" % CONFIG_TEXT[c] for c in CONFIGS)
    L.append(hdr)
    L.append("-" * len(hdr))
    by = {(r["id"], r["config"]): r for r in rows}
    for id_, fam, _bl, refname, _rl, _bf, _rf in plan:
        r0 = by[(id_, "np")]
        rd = os.path.join(out, "runs", id_ + ".ref")
        rb, rfull = ref_stage(os.path.join(rd, "base")), ref_stage(os.path.join(rd, "full"))
        refs = "%s %s %s" % ("G" if refname == "gecode" else "CN", kfmt(per(rfull, rb, "nodes")),
                             kfmt(per(rfull, rb, "fail")))
        line = "%-11s %-10s %-22s" % (id_, fam, refs)
        for c in CONFIGS:
            r = by[(id_, c)]
            k = None if r["kinstr_per_unit"] is None else r["kinstr_per_unit"] * 1000
            line += " | %-24s" % ("%s/%s (%sx)" % (kfmt(k), "n" if r["unit"] == "node" else "f",
                                                  fx(r["factor"])))
        L.append(line)
    L.append("")
    L.append("geometric mean of the factors, per family")
    fams = []
    for p in plan:
        if p[1] not in fams:
            fams.append(p[1])
    gm = {}
    for fam in fams:
        line = "%-22s" % ("%s (%d)" % (fam, sum(1 for p in plan if p[1] == fam)))
        for c in CONFIGS:
            g = geomean([r["factor"] for r in rows if r["family"] == fam and r["config"] == c])
            gm[(fam, c)] = g
            line += " | %-24s" % ("%sx" % fx(g))
        L.append(line)
    L.append("")
    L.append("answers (baguette per configuration; the reference) and search trees")
    for id_, fam, bl, refname, rl, _bf, _rf in plan:
        L.append("%-11s %s; ref %s %s nodes %s failures (budget %s); baguette nodes/failures %s"
                 % (id_, " ".join("%s=%s" % (c, by[(id_, c)]["answer"]) for c in CONFIGS),
                    by[(id_, "np")]["ref_answer"], by[(id_, "np")]["ref_nodes"],
                    by[(id_, "np")]["ref_failures"], rl,
                    " ".join("%s %s/%s" % (c, by[(id_, c)]["nodes"], by[(id_, c)]["failures"])
                             for c in CONFIGS)))
    L.append("")

    # The comparison with the recorded reference: information only.
    reftxt = read(ref_tsv)
    if reftxt and not record:
        rec_head = [l for l in reftxt.splitlines() if l.startswith("#")]
        lines = [l.split("\t") for l in reftxt.splitlines() if l and not l.startswith("#")]
        cols = lines[0] if lines else []
        recd = {}
        for l in lines[1:]:
            d = dict(zip(cols, l))
            recd[(d.get("id"), d.get("config"))] = d
        L.append("against the recorded reference (INFORMATION, never a failure): %s"
                 % (rec_head[1].lstrip("# ") if len(rec_head) > 1 else ""))
        for r in rows:
            d = recd.get((r["id"], r["config"]))
            if not d:
                L.append("  %-11s %-5s not in the reference" % (r["id"], r["config"]))
                continue
            try:
                old = float(d["kinstr_per_unit"])
                new = r["kinstr_per_unit"]
                same_unit = d.get("unit") == r["unit"]
                ch = ("%+.2f %%" % (100.0 * (new - old) / old)) if new is not None and same_unit else \
                    "unit changed (%s -> %s)" % (d.get("unit"), r["unit"])
                L.append("  %-11s %-5s %s/%s now, %s recorded: %s; factor %s -> %s"
                         % (r["id"], r["config"], kfmt(None if new is None else new * 1000),
                            r["unit"][0], kfmt(old * 1000), ch, fx(float(d["factor"])),
                            fx(r["factor"])))
            except (KeyError, ValueError, TypeError):
                L.append("  %-11s %-5s the recorded line is unreadable" % (r["id"], r["config"]))
        L.append("")

    L.append("bench/series/HISTORY.md row (factors pf / np / cdpf / cdnp; fill the Record cell):")
    L.append("| %s | | `%s` | `%s` | %s, %s s | %s |" % (
        date, commit, md5[:8], host, wall,
        " | ".join(" / ".join(fx(gm[(fam, c)]) for c in CONFIGS) for fam in fams)))
    L.append("  (family columns: %s)" % ", ".join(fams))
    L.append("")

    rc = 0
    for b in broken:
        L.append("factor_lane: BROKEN %s" % b)
    for u in unchecked:
        L.append("factor_lane: PROOF NOT VERIFIED %s" % u)
    if broken or unchecked:
        L.append("factor_lane: FAIL -- %d run(s) broken, %d proof(s) not verified" % (len(broken), len(unchecked)))
        rc = 1
    else:
        nproofs = 2 * sum(1 for r in rows if r["config"].endswith("pf"))
        L.append("factor_lane: ok -- %d runs measured, %d proofs VERIFIED and deleted (%s s)"
                 % (4 * len(rows) // 2 + 2 * len(plan), nproofs, wall))
    text = "\n".join(L) + "\n"
    with open(os.path.join(out, "factor.txt"), "w") as fh:
        fh.write(text)
    sys.stdout.write(text)

    if record:
        # A broken run has no measurement, so it cannot be a reference. A proof the checker did not
        # verify is a FAILURE of the lane (rc 1) but its instruction counts are still measured: the
        # reference is written with that line's verdict in it, for the next run to compare with.
        if broken:
            sys.stdout.write("factor_lane: NOT recording a reference with broken runs\n")
            return 1
        with open(ref_tsv, "w") as fh:
            fh.write("# M17-bench-series-T6 (D-0256). The per-node factor lane's recorded reference, written by\n")
            fh.write("# binary %s, commit %s, %s, %s. scripts/factor_lane.sh --record; compared as information.\n"
                     % (md5, commit, host, date))
            fh.write(tsv)
        sys.stdout.write("factor_lane: reference recorded in %s%s\n" % (
            ref_tsv, " WITH %d proof(s) not verified (their verdict is in it)" % len(unchecked)
            if unchecked else ""))
    return rc


if __name__ == "__main__":
    sys.exit(main())
