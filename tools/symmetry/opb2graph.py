#!/usr/bin/env python3
"""opb2graph.py IN.opb[.gz] OUT.dimacs -- a pseudo-Boolean formula as a coloured graph for dejavu,
whose automorphisms are the literal permutations that map the formula onto itself (the witnesses the
dominance rule of VeriPB can use). notes/dejavu-plan.md.

- Each variable x has two literal vertices, x and ~x (colour 0), joined by an edge. An automorphism
  may swap them, which is a negation symmetry and a valid witness.
- Each constraint is normalized to Σ c_i l_i >= d with c_i > 0 (a negative coefficient moves to the
  negated literal), and is one vertex whose colour is its kind (>= or =), its degree and the multiset
  of its coefficients. When all its coefficients are equal it is joined to its literals directly;
  otherwise it is joined to one vertex per distinct coefficient (coloured by that value), each joined
  to the literals that carry it. An "=" constraint is kept as such (not split in two). A constraint
  equal to an earlier one after normalization is dropped: its twin vertex would only add swaps of
  duplicate constraints, which inflate dejavu's group order (seen on aut.mzn).
- A `min:` objective is one vertex of a colour of its own, joined (through coefficient vertices as
  above, signs kept) to its literals, so that every automorphism keeps the objective. A `<=` row is
  turned into `>=`, and anything that is not a list of "coefficient literal" pairs is refused
  (non-linear terms, for instance). These two traps and the objective were found by a session that
  looked for counterexamples ($WORK/dvcex/README.md).
Known losses, not fixed here: two equivalent constraints written differently (2y1+2y2+2y3 >= 4 and
y1+y2+y3 >= 2, or a coefficient above the degree) get different colours, since nothing divides by
the gcd or saturates; and values of an order-encoded integer are only seen up to reversal.
Also writes OUT.map: one line per literal vertex, "vertex literal" (vertex numbers as in the DIMACS
file, 1-based), so that the generators of dejavu (0-based, `--gens-file`) can be read back.
"""
import sys, gzip, re, collections
inp, outp = sys.argv[1], sys.argv[2]
op = gzip.open if inp.endswith(".gz") else open
lit_v = {}; col = []; E = []
def vert(c):
    col.append(c); return len(col)
def lit(name):
    neg = name.startswith("~"); x = name[1:] if neg else name
    if x not in lit_v:
        a = vert(0); b = vert(0); lit_v[x] = (a, b); E.append((a, b))
    return lit_v[x][1 if neg else 0]
colours = {}
def colour(key):
    if key not in colours: colours[key] = 10 + len(colours)
    return colours[key]
ncons = 0; seen = set(); twins = 0
with op(inp, "rt") as f:
    for line in f:
        line = line.strip()
        if not line or line.startswith("*"): continue
        line = re.sub(r"^@\S+\s+", "", line).rstrip(";").strip()
        if line.startswith("min:"):                      # the objective: one vertex of its own colour, so
            toks = line[4:].split(); obj = True          # that a symmetry must keep the objective
            rel, d = "min", 0
        else:
            obj = False
            m = re.match(r"(.*?)\s*(>=|<=|=)\s*(-?\d+)$", line)
            if not m: sys.exit(f"cannot parse: {line[:120]}")
            body, rel, d = m.group(1), m.group(2), int(m.group(3))
            toks = body.split()
        if len(toks) % 2 or not all(re.fullmatch(r"[+-]?\d+", c) and re.fullmatch(r"~?[A-Za-z_][\w\[\]]*", l)
                                    for c, l in zip(toks[0::2], toks[1::2])):
            sys.exit(f"not a linear pseudo-Boolean constraint (coefficient literal pairs): {line[:120]}")
        if rel == "<=":                                  # Σ c l <= d  is  Σ -c l >= -d
            toks = [str(-int(t)) if i % 2 == 0 else t for i, t in enumerate(toks)]; rel, d = ">=", -d
        terms = collections.defaultdict(int)
        for c, l in zip(toks[0::2], toks[1::2]):
            c = int(c)
            if c < 0 and not obj:                        # c l = c - c ~l = c + |c| ~l
                d -= c; l = l[1:] if l.startswith("~") else "~" + l; c = -c
            terms[l] += c
        byc = collections.defaultdict(list)
        for l, c in terms.items(): byc[c].append(l)
        key = ("cons", rel, d, tuple(sorted((c, len(ls)) for c, ls in byc.items())))
        sig = (key, frozenset((c, frozenset(ls)) for c, ls in byc.items()))
        if sig in seen:                                  # the same constraint twice: a twin vertex
            twins += 1; continue                         # would only add trivial swaps
        seen.add(sig)
        cv = vert(colour(key)); ncons += 1
        if len(byc) == 1:
            for l in next(iter(byc.values())): E.append((cv, lit(l)))
        else:
            for c, ls in byc.items():
                h = vert(colour(("coef", c))); E.append((cv, h))
                for l in ls: E.append((h, lit(l)))
with open(outp, "w") as f:
    f.write(f"p edge {len(col)} {len(E)}\n")
    for v, c in enumerate(col, 1): f.write(f"n {v} {c}\n")
    for a, b in E: f.write(f"e {a} {b}\n")
with open(outp + ".map", "w") as f:
    for x, (a, b) in lit_v.items():
        f.write(f"{a} {x}\n{b} ~{x}\n")
print(f"{inp}: {len(lit_v)} variables, {ncons} constraints ({twins} duplicates dropped), {len(col)} vertices, {len(E)} edges, {len(colours)} colours")
