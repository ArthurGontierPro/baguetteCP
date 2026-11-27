#!/usr/bin/env python3
"""Random small .scp files, baguette's .scp reader against tools/e2e/scpsem.py. This is test 4 of
the plan in D-0228 section 14 (the record that made .scp baguette's second input), run for
M23-inputs-T5, the milestone's acceptance; D-0230 records the reader and its lanes.

Usage: python3 -I random_lane.py BAGUETTE OUTDIR [N] [SEED]

Writes N (default 300) random problems over 2 to 5 variables with domains of at most 6
values, each with 1 to 3 constraints drawn from every family lib/scp/reader.ml reads, a
third of them optimisation problems. Each is solved by BAGUETTE with a proof, the proof
checked by veripb, and the answer judged by tools/scp/validate.py (the .scp's own
semantics, enumerated). Prints one line per failure and the totals; exits 0 when there is
none, 1 on any failure (a missing argument also stops with status 1, on a Python exception).
The seed (default 2026) makes a run reproducible.
"""
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))


def gen(rng):
    nv = rng.randint(2, 5)
    vs = []
    for i in range(nv):
        lo = rng.randint(-3, 2)
        hi = lo + rng.randint(0, 5)
        if rng.random() < 0.25:
            lo, hi = 0, 1
        vs.append((f"v{i}", lo, hi))
    names = [v[0] for v in vs]

    def vc():
        return rng.choice(names) if rng.random() < 0.85 else str(rng.randint(-3, 4))

    def cmpkw():
        return rng.choice(["equals", "not_equals", "less_equal", "less_than", "greater_equal",
                           "greater_than"])

    def cond():
        return f"({rng.choice(names)} {rng.choice(['=', '!=', '<', '<=', '>', '>='])} {rng.randint(-2, 3)})"

    def lst(k):
        return "(" + " ".join(vc() for _ in range(k)) + ")"

    cons = []
    for k in range(rng.randint(1, 3)):
        f = rng.randrange(24)
        n = f"c{k}"
        if f == 0:
            terms = " ".join(f"{rng.randint(-3, 3)} {vc()}" for _ in range(rng.randint(1, 3)))
            cons.append(f"({n} lin_{cmpkw()} ({terms}) {vc()})")
        elif f == 1:
            terms = " ".join(f"{rng.randint(-3, 3)} {vc()}" for _ in range(rng.randint(1, 3)))
            kw = rng.choice(["less_equal", "less_than", "greater_equal", "greater_than"])
            cons.append(f"({n} lin_{kw}_iff {cond()} ({terms}) {vc()})")
        elif f == 2:
            cons.append(f"({n} {cmpkw()} {vc()} {vc()})")
        elif f == 3:
            cons.append(f"({n} {cmpkw()}_iff {cond()} {vc()} {vc()})")
        elif f == 4:
            cs = " ".join(cond() for _ in range(rng.randint(0, 3)))
            cons.append(f"({n} {rng.choice(['and', 'or'])} ({cs}) {cond()})")
        elif f == 5:
            cons.append(f"({n} {rng.choice(['plus', 'minus', 'max', 'min'])} {vc()} {vc()} {vc()})")
        elif f == 6:
            cons.append(f"({n} {rng.choice(['neg', 'abs'])} {vc()} {vc()})")
        elif f == 7:
            cons.append(f"({n} {rng.choice(['multiply', 'divide'])} {vc()} {vc()} {vc()})")
        elif f == 8:
            cons.append(f"({n} all_different {lst(rng.randint(2, 4))})")
        elif f == 9:
            kw = rng.choice(["increasing", "strictly_increasing", "decreasing", "strictly_decreasing"])
            cons.append(f"({n} {kw} {lst(rng.randint(2, 4))})")
        elif f == 10:
            k = rng.randint(1, 3)
            vals = " ".join(str(x) for x in rng.sample(range(-2, 4), k))
            kw = rng.choice(["gacglobalcardinality", "gacglobalcardinalityclosed",
                             "boundsglobalcardinality", "boundsglobalcardinalityclosed"])
            cons.append(f"({n} {kw} {lst(rng.randint(1, 4))} ({vals}) {lst(k)})")
        elif f == 11:
            cons.append(f"({n} count {lst(rng.randint(1, 4))} {rng.randint(-1, 3)} {vc()})")
        elif f == 12:
            vals = " ".join(str(rng.randint(-3, 4)) for _ in range(rng.randint(1, 4)))
            cons.append(f"({n} in ({vals}) {vc()})")
        elif f == 13:
            cons.append(f"({n} in {lst(rng.randint(1, 3))} {vc()})")
        elif f == 14:
            arr = " ".join(str(rng.randint(-3, 4)) for _ in range(rng.randint(1, 5)))
            cons.append(f"({n} element ({arr}) ({vc()} {rng.randint(-2, 2)}) {vc()})")
        elif f == 15:
            cons.append(f"({n} {rng.choice(['array_max', 'array_min'])} {lst(rng.randint(1, 4))} {vc()})")
        elif f == 16:
            k = rng.randint(1, 3)
            cons.append(f"({n} inverse ({lst(k)} {rng.randint(-1, 2)}) ({lst(k)} {rng.randint(-1, 2)}))")
        elif f == 17:
            k = rng.randint(1, 3)
            ds = " ".join(str(rng.randint(0, 3)) for _ in range(k))
            hs = " ".join(str(rng.randint(0, 3)) for _ in range(k))
            cons.append(f"({n} cumulative {lst(k)} ({ds}) ({hs}) {rng.randint(0, 4)})")
        elif f == 18 or f == 19:
            k = rng.randint(1, 3)
            rows = " ".join("(" + " ".join(str(rng.randint(-2, 3)) for _ in range(k)) + ")"
                            for _ in range(rng.randint(0, 5)))
            cons.append(f"({n} table ({rows}) {lst(k)})")
        elif f == 20 or f == 21:
            q = rng.randint(1, 3)
            trans = []
            for s in range(q):
                syms = rng.sample(range(-1, 3), rng.randint(0, 3))
                trans.append("(" + " ".join(f"({a} {rng.randrange(q + 1)})" for a in syms) + ")")
            fin = " ".join(str(x) for x in rng.sample(range(q + 1), rng.randint(0, 2)))
            cons.append(f"({n} regular {lst(rng.randint(0, 4))} {q} ({' '.join(trans)}) ({fin}))")
        else:
            cons.append(f"({n} circuit {lst(rng.randint(1, 4))})")
    r = rng.random()
    pt = "decide" if r < 0.5 else ("enumerate" if r < 0.67 else
                                   f"({rng.choice(['minimize', 'maximize'])} {rng.choice(names)})")
    var_s = " ".join(f"({a} {b} {c})" for a, b, c in vs)
    return f"( (version 1) (variables {var_s}) (constraints {' '.join(cons)}) (prob_type {pt}) )\n"


def main(argv):
    solver, out = argv[1], argv[2]
    n = int(argv[3]) if len(argv) > 3 else 300
    seed = int(argv[4]) if len(argv) > 4 else 2026
    rng = random.Random(seed)
    os.makedirs(out, exist_ok=True)
    veripb = os.environ.get("VERIPB", os.path.expanduser("~/.cargo/bin/veripb"))
    stats = {}
    fails = 0
    for i in range(n):
        p = os.path.join(out, f"r{i}")
        with open(p + ".scp", "w") as f:
            f.write(gen(rng))
        with open(p + ".out", "w") as fo, open(p + ".err", "w") as fe:
            rc = subprocess.run([solver, p + ".scp", "--proof", p], stdout=fo, stderr=fe,
                                timeout=120).returncode
        if rc != 0:
            why = open(p + ".err").read().strip().splitlines()
            key = "refused " + (why[0].split("refused: ")[-1][:50] if why else f"rc={rc}")
            if rc != 2 or any("Fatal error" in l for l in why):
                fails += 1
                print(f"FAIL r{i}: exit {rc}: {why[:1]}")
            stats[key] = stats.get(key, 0) + 1
            continue
        v = subprocess.run([veripb, p + ".opb", p + ".pbp"], capture_output=True, text=True,
                           timeout=300)
        verdict = next((l for l in v.stdout.splitlines() if l.startswith("s ")), "s none")
        j = subprocess.run([sys.executable, "-I", os.path.join(HERE, "validate.py"), p + ".scp",
                            p + ".out"], capture_output=True, text=True, timeout=300)
        val = j.stdout.strip()
        for ext in (".opb", ".pbp"):
            try:
                os.remove(p + ext)
            except OSError:
                pass
        if not verdict.startswith("s VERIFIED") or not (val.startswith("OK") or val == "TOOBIG"):
            fails += 1
            print(f"FAIL r{i}: {verdict} / {val}")
            continue
        key = val.split()[1] if val.startswith("OK") else val
        stats[key] = stats.get(key, 0) + 1
    print("random lane:", ", ".join(f"{k}: {v}" for k, v in sorted(stats.items())),
          f"; {fails} FAIL")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
