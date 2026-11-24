#!/usr/bin/env python3
"""Search-heavy differential fuzz: random 3-SAT near the threshold and small integer
optimisation problems. Same checks as fuzz.py (Gecode answer, VeriPB on baguette's proof,
Gecode re-check of baguette's solution). Usage: fuzz2.py OUTDIR SEED N [extra flags]"""
import os, random, sys, shutil, re, collections
import importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("fz", os.path.join(HERE, "fuzz.py"))
fz = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fz)


def sat3(r):
    n = r.randint(25, 45)
    m = int(n * r.uniform(3.9, 4.6))
    decls = ["var bool: b%d;" % i for i in range(n)]
    cons = []
    for _ in range(m):
        vs = r.sample(range(n), 3)
        pos = [("b%d" % v) for v in vs if r.random() < 0.5]
        neg = [("b%d" % v) for v in vs if ("b%d" % v) not in pos]
        cons.append("constraint bool_clause([%s],[%s]);" % (",".join(pos), ",".join(neg)))
    out = "output [%s, \"\\n\"];" % ", ".join('"b%d=\\(b%d) "' % (i, i) for i in range(n))
    return "\n".join(decls + cons) + "\nsolve satisfy;\n" + out + "\n"


def intopt(r):
    n = r.randint(6, 10)
    decls = ["var 0..%d: x%d;" % (r.randint(2, 6), i) for i in range(n)]
    cons = []
    for _ in range(r.randint(3, 6)):
        vs = r.sample(range(n), r.randint(2, min(5, n)))
        terms = " + ".join("%d*x%d" % (r.choice([-3, -2, -1, 1, 2, 3, 4]), v) for v in vs)
        cons.append("constraint %s %s %d;" % (terms, r.choice(["<=", ">=", "!="]), r.randint(-4, 12)))
    if r.random() < 0.5:
        cons.append("constraint alldifferent([%s]);" % ",".join("x%d" % v for v in r.sample(range(n), r.randint(3, min(5, n)))))
    if r.random() < 0.4:
        a, b, c = r.sample(range(n), 3)
        cons.append("constraint x%d * x%d >= x%d;" % (a, b, c))
    obj = " + ".join("%d*x%d" % (r.randint(-5, 9), i) for i in range(n))
    decls.append("var -500..500: obj;")
    cons.append("constraint obj = %s;" % obj)
    out = "output [%s, \"obj=\\(obj)\", \"\\n\"];" % ", ".join('"x%d=\\(x%d) "' % (i, i) for i in range(n))
    return ('include "globals.mzn";\n' + "\n".join(decls + cons) +
            "\nsolve %s obj;\n" % r.choice(["minimize", "maximize"]) + out + "\n")


def main():
    outdir, seed, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    extra = " ".join(sys.argv[4:])
    os.makedirs(os.path.join(outdir, "bad"), exist_ok=True)
    fz.ensure_msc(outdir)
    r = random.Random(seed)
    tally = collections.Counter()
    for it in range(n):
        mzn = sat3(r) if r.random() < 0.5 else intopt(r)
        path = os.path.join(outdir, "m.mzn")
        open(path, "w").write(mzn)
        rc_g, out_g, _ = fz.run("minizinc --solver gecode %s" % path, 60)
        st_g, obj_g, _ = fz.status(out_g) if rc_g is not None else ("TIMEOUT", None, None)
        prefix = os.path.join(outdir, "p")
        for ext in (".opb", ".pbp"):
            if os.path.exists(prefix + ext):
                os.remove(prefix + ext)
        rc_b, out_b, err_b = fz.run("minizinc --solver %s %s --proof %s %s -s" % (fz.MSC, path, prefix, extra), 60)
        st_b, obj_b, vals_b = fz.status(out_b) if rc_b is not None else ("TIMEOUT", None, None)
        m = re.search(r"failures=(\d+)", out_b)
        tally["conflicts>=10" if m and int(m.group(1)) >= 10 else "conflicts<10"] += 1
        verdict, note = "ok", ""
        if st_b in ("ERROR", "UNKNOWN", "TIMEOUT") or rc_b != 0:
            verdict, note = ("bag-timeout" if st_b == "TIMEOUT" else "bag-error"), (err_b or out_b)[-800:]
        elif st_g in ("TIMEOUT", "ERROR", "UNKNOWN"):
            verdict = "gecode-" + st_g
        else:
            if not ((st_g == st_b) or ({st_g, st_b} <= {"SAT", "OPT"})):
                verdict, note = "STATUS-MISMATCH", "gecode=%s baguette=%s" % (st_g, st_b)
            elif st_b == "OPT" and obj_g != obj_b:
                verdict, note = "OBJ-MISMATCH", "gecode=%s baguette=%s" % (obj_g, obj_b)
            if verdict == "ok" and os.path.exists(prefix + ".pbp"):
                rc_v, out_v, err_v = fz.run("%s %s.opb %s.pbp" % (fz.VERIPB, prefix, prefix), 120)
                txt = (out_v or "") + (err_v or "")
                if rc_v != 0 or "VERIFIED" not in txt:
                    verdict, note = "PROOF-REJECTED", txt[-800:]
            if verdict == "ok" and st_b in ("SAT", "OPT") and vals_b:
                fix = "".join("constraint %s = %s;\n" % (k, v) for k, v in vals_b.items() if k != "obj")
                chk = re.sub(r"solve [a-z]+( obj)?;", "", mzn) + fix + "solve satisfy;\n"
                cpath = os.path.join(outdir, "chk.mzn")
                open(cpath, "w").write(chk)
                _, out_c, _ = fz.run("minizinc --solver gecode %s" % cpath, 60)
                if "=====UNSATISFIABLE=====" in out_c:
                    verdict, note = "BAD-SOLUTION", str(vals_b)
        tally[verdict] += 1
        tally["st_" + st_b] += 1
        if verdict != "ok" and not verdict.startswith("gecode-"):
            d = os.path.join(outdir, "bad", "%d_%d_%s" % (seed, it, verdict))
            os.makedirs(d, exist_ok=True)
            shutil.copy(path, os.path.join(d, "m.mzn"))
            for ext in (".opb", ".pbp"):
                if os.path.exists(prefix + ext):
                    shutil.copy(prefix + ext, os.path.join(d, "p" + ext))
            open(os.path.join(d, "note.txt"), "w").write("%s\n%s\n--- gecode\n%s\n--- baguette\n%s\n%s\n" % (verdict, note, out_g, out_b, err_b[-2000:]))
    print(seed, extra, dict(tally), flush=True)


if __name__ == "__main__":
    main()
