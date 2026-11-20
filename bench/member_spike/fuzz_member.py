#!/usr/bin/env python3
"""M7-T34 (D-0169): random small `baguette_member` models, end to end.

Each model: 2..4 positions over 1..7 (set domains, so declared holes; sometimes a
constant, sometimes a variable twice or y itself among x), y over a set (sometimes a
constant), a few side constraints that punch holes and move bounds during search, and a
random search order. For each: the solver's answer against a brute-force oracle, the
printed solution against the constraints, and veripb over the proof. Domains stay in
single digits (CLAUDE.md).

usage: fuzz_member.py BINARY OUTDIR [N] [SEED] [EXTRA SOLVER FLAGS...]
Prints one line per failure and a summary; exit 1 on any failure. With LOAD_BEARING=1
(the default) every threshold lemma of a SATISFIABLE model's proof is also deleted in
turn, and counted load-bearing when veripb then refuses at the RUP wording.
"""
import itertools
import os
import random
import re
import subprocess
import sys

BIN, OUT = sys.argv[1], sys.argv[2]
N = int(sys.argv[3]) if len(sys.argv) > 3 else 200
SEED = int(sys.argv[4]) if len(sys.argv) > 4 else 1
EXTRA = sys.argv[5:]
os.makedirs(OUT, exist_ok=True)


def rnd_dom(r):
    lo = r.randint(1, 3)
    hi = r.randint(lo, 7)
    vals = [v for v in range(lo, hi + 1) if v in (lo, hi) or r.random() < 0.6]
    return vals


def dom_txt(vals):
    if vals == list(range(vals[0], vals[-1] + 1)):
        return "%d..%d" % (vals[0], vals[-1])
    return "{" + ",".join(map(str, vals)) + "}"


def gen(r):
    nv = r.randint(3, 5)
    doms = [rnd_dom(r) for _ in range(nv)]
    names = ["v%d" % i for i in range(nv)]
    ycell = 0 if r.random() > 0.1 else ("c", r.randint(1, 6))
    n = r.randint(2, 4)
    xs = []
    for _ in range(n):
        u = r.random()
        if u < 0.15:
            xs.append(("c", r.randint(1, 7)))
        elif u < 0.25 and ycell == 0:
            xs.append(0)  # y itself
        else:
            xs.append(r.randint(1, nv - 1))
    side = []
    for _ in range(r.randint(0, 3)):
        k = r.randint(0, 3)
        a, b = r.randrange(nv), r.randrange(nv)
        if k == 0:
            side.append(("ne_c", a, r.randint(1, 7)))
        elif k == 1 and a != b:
            side.append(("ne", a, b))
        elif k == 2 and a != b:
            side.append(("le", a, b))
        elif k == 3 and a != b:
            side.append(("sum_le", a, b, r.randint(4, 12)))
    order = list(range(nv))
    r.shuffle(order)
    sel = r.choice(["indomain_min", "indomain_max"])
    return doms, names, ycell, xs, side, order, sel


def cell_txt(names, c):
    return str(c[1]) if isinstance(c, tuple) else names[c]


def render(m):
    doms, names, ycell, xs, side, order, sel = m
    L = ["predicate baguette_member(array [int] of var int: x,var int: y,"
         "array [int] of var bool: b);"]
    for nm, d in zip(names, doms):
        L.append("var %s: %s :: output_var;" % (dom_txt(d), nm))
    for i in range(len(xs)):
        L.append("var bool: b%d;" % i)
    L.append("constraint baguette_member([%s], %s, [%s]);" % (
        ", ".join(cell_txt(names, c) for c in xs), cell_txt(names, ycell),
        ", ".join("b%d" % i for i in range(len(xs)))))
    for s in side:
        if s[0] == "ne_c":
            L.append("constraint int_ne(%s, %d);" % (names[s[1]], s[2]))
        elif s[0] == "ne":
            L.append("constraint int_ne(%s, %s);" % (names[s[1]], names[s[2]]))
        elif s[0] == "le":
            L.append("constraint int_le(%s, %s);" % (names[s[1]], names[s[2]]))
        else:
            L.append("constraint int_lin_le([1, 1], [%s, %s], %d);" % (
                names[s[1]], names[s[2]], s[3]))
    L.append("solve :: int_search([%s], input_order, %s, complete) satisfy;" % (
        ", ".join(names[i] for i in order), sel))
    return "\n".join(L) + "\n"


def val(a, c):
    return c[1] if isinstance(c, tuple) else a[c]


def holds(m, a):
    doms, names, ycell, xs, side, order, sel = m
    if not any(val(a, c) == val(a, ycell) for c in xs):
        return False
    for s in side:
        if s[0] == "ne_c" and a[s[1]] == s[2]:
            return False
        if s[0] == "ne" and a[s[1]] == a[s[2]]:
            return False
        if s[0] == "le" and a[s[1]] > a[s[2]]:
            return False
        if s[0] == "sum_le" and a[s[1]] + a[s[2]] > s[3]:
            return False
    return True


def sat(m):
    return any(holds(m, a) for a in itertools.product(*m[0]))


LOAD_BEARING = os.environ.get("LOAD_BEARING", "1") == "1"


def load_bearing(base):
    """On a SATISFIABLE model's proof: for each `pol` written ahead of a line, delete each
    threshold lemma it weakens back out (a cited id followed by literal axioms), with the
    pol, and ask veripb again. A lemma is load-bearing when the proof is then refused at
    the RUP wording. Returns (load-bearing, redundant)."""
    lines = open(base + ".pbp").read().split("\n")
    lb = red = 0
    for i, line in enumerate(lines):
        toks = line.split()
        if len(toks) < 2 or toks[1] != "pol":
            continue
        lemmas = []
        rest = toks[2:]
        for j, w in enumerate(rest):
            if w.startswith("@"):
                nxt = rest[j + 1:j + 3]
                if nxt and (is_lit(nxt[0]) or (nxt[0] == "+" and len(nxt) > 1 and is_lit(nxt[1]))):
                    lemmas.append(w)
        for lem in lemmas:
            gone = {lem, toks[0]}
            kept = []
            for l in lines:
                t = l.split()
                if t and t[0] in gone:
                    continue
                if l.startswith("del id "):
                    ids = [w for w in l[7:].split() if w not in gone]
                    if ids == [";"]:
                        continue
                    l = "del id " + " ".join(ids)
                kept.append(l)
            with open(base + ".lb.pbp", "w") as f:
                f.write("\n".join(kept))
            v = subprocess.run(["veripb", base + ".opb", base + ".lb.pbp"],
                               capture_output=True, text=True, timeout=300)
            out = v.stdout + v.stderr
            if v.returncode != 0 and "reverse unit propagation" in out:
                lb += 1
            else:
                red += 1
                print("REDUNDANT %s: lemma %s of %s" % (base, lem, toks[0]))
                os.system("cp %s.fzn %s.redundant.fzn" % (base, base))
        os.remove(base + ".lb.pbp") if os.path.exists(base + ".lb.pbp") else None
    return lb, red


def is_lit(w):
    return w not in ("+", "*", "d", ";") and not w.startswith("@") and not w[0].isdigit()


r = random.Random(SEED)
fails = 0
stats = {"SAT": 0, "UNSAT": 0, "pol": 0, "with_pol": 0, "lemmas_lb": 0, "lemmas_redundant": 0}
for i in range(N):
    m = gen(r)
    base = os.path.join(OUT, "f%04d" % i)
    with open(base + ".fzn", "w") as f:
        f.write(render(m))
    p = subprocess.run([BIN] + EXTRA + ["--proof", base, base + ".fzn"], capture_output=True,
                       text=True, timeout=120)
    out = p.stdout
    expect = sat(m)
    got = None
    if "=====UNSATISFIABLE=====" in out:
        got = False
    elif "----------" in out:
        got = True
        a = [None] * len(m[1])
        for line in out.splitlines():
            mm = re.match(r"^(v\d+) = (-?\d+);$", line)
            if mm:
                a[int(mm.group(1)[1:])] = int(mm.group(2))
        if None in a or not holds(m, a) or any(x not in d for x, d in zip(a, m[0])):
            print("FAIL %s: printed solution does not satisfy the model" % base)
            fails += 1
            continue
    if got is None or got != expect:
        print("FAIL %s: answer %s, oracle %s (rc %d) %s" % (base, got, expect,
                                                           p.returncode, p.stderr[-300:]))
        fails += 1
        continue
    stats["SAT" if got else "UNSAT"] += 1
    v = subprocess.run(["veripb", base + ".opb", base + ".pbp"], capture_output=True,
                       text=True, timeout=300)
    if v.returncode != 0 or "VERIFIED" not in v.stdout + v.stderr:
        print("FAIL %s: veripb: %s" % (base, (v.stdout + v.stderr)[-400:]))
        fails += 1
        continue
    with open(base + ".pbp") as f:
        pols = sum(1 for line in f if " pol " in line or line.startswith("pol "))
    stats["pol"] += pols
    stats["with_pol"] += 1 if pols else 0
    if got and pols and LOAD_BEARING:
        lb, red = load_bearing(base)
        stats["lemmas_lb"] += lb
        stats["lemmas_redundant"] += red
    for ext in (".fzn", ".opb", ".pbp"):
        os.remove(base + ext)
print("fuzz_member: %d models (%d SAT, %d UNSAT; %d proofs with a derivation ahead, "
      "%d pol lines; on the SAT ones %d threshold lemmas load-bearing, %d redundant), "
      "%d failure(s)" % (N, stats["SAT"], stats["UNSAT"], stats["with_pol"], stats["pol"],
                         stats["lemmas_lb"], stats["lemmas_redundant"], fails))
sys.exit(1 if fails else 0)
