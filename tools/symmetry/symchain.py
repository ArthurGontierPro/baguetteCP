#!/usr/bin/env python3
"""symchain.py IN.fzn IN.opb OUT [--vars V,..] [--depth D] [--score orbit|first|shared]
                                [--order static|search] [--orient auto|max|min]
-- a stabilizer chain of the model's symmetry group, found by dejavu as distributed, and the
symmetry-breaking clauses it licenses (M15-symmetry-T2, D-0179; the study is D-0177; the chain that
follows the search, `--order search`, is M15-symmetry-T3, D-0181).

IN.opb is baguette's .opb of IN.fzn, without breaking (`main.exe IN.fzn --proof P --time-limit 0`
writes it without searching). The pipeline, one dejavu run per level (D-0177 §4, backend A):

  1. opb2graph.py IN.opb OUT.dimacs: the coloured graph (codes-cp's, byte for byte), whose
     automorphisms restricted to the literal vertices are literal permutations mapping the .opb
     onto itself.
  2. level i: dejavu on the graph with the points c_1 .. c_{i-1} already chosen coloured apart, so
     its generators generate (as far as dejavu found them) the stabilizer G_{i-1} of those points.
     The candidates are the positive literals of the model's 0/1 variables (`var bool` and
     `var 0..1`) among the BREAK VARIABLES: the search annotation's variables by default (`int_search`,
     `bool_search`, `seq_search`), every non-defined 0/1 variable when there is none, `--vars` to
     override (FlatZinc names, or array names standing for their elements). The orbit of each
     candidate under the generators is a BFS over LITERALS (an image may be negative: a negation
     symmetry), recording for every image b a word w_b in the generators with w_b(c) = b.
     The point c_i is chosen among the candidates with a nontrivial orbit whose every literal is a
     0/1 FlatZinc variable of one kind (so that the clauses can be written in FlatZinc), by the
     score: `orbit` (largest orbit, ties in break-variable order: codes-cp's rule), `first` (the
     first in break-variable order) or `shared` (most .opb rows shared with the points already
     chosen, ties by orbit: satsuma's `common_clauses`).
  3. for every b != c_i in the orbit, the CUT c_i v ~b (b = ~c_i gives the unit c_i), with its
     word w_b. The next level's dejavu run gives G_i, the stabilizer of c_i; when u(c_i) reaches b
     under G_i (u = w_b^-1, which sends b to c_i) by a word h, the element h o u of G_{i-1}
     SWAPS c_i and b, and the cut records h as its `swap`. symmerge.py proves a cut with a swap by
     `red` (no order), and one without by `dom` under the lex order of the points (D-0179 §2 says
     why the swap matters: D-0177's `red` with w_b^-1 alone is refused on the second cut of a
     level, measured on php_unsat).
  4. stop at --depth levels, at a trivial group, or when no candidate is eligible.

THE CHAIN THAT FOLLOWS THE SEARCH (`--order search`, M15-symmetry-T3, D-0181). For a static search
order (`bool_search(x, input_order, ...)`, or SPEC 3.4's default over 0/1 variables) the chain can
take the search's own order: at each level the point is the FIRST break variable in search order
with a nontrivial eligible orbit (the `first` score), and the cut is ORIENTED by the value choice.
The point is then a LITERAL p, the value the search tries first: p = x for indomain_max
(the cut x_c v ~x_b, T2's), p = ~x for indomain_min, indomain, indomain_split and the default
(the cut ~x_c v x_b). Why this agrees with the search: every break variable before c_i in search
order is fixed by G_{i-1} (it is an earlier point, or its orbit is trivial), so for any solution s
an element of G_{i-1} that brings a preferred value onto c_i keeps the prefix before c_i. The
first solution a depth-first search finds (the lex-first one in search order under the value
choice, learning and propagation do not change which) therefore satisfies every cut, and the
broken search still finds it first: on a satisfiable model the breaking can no longer cut the
branch the search was heading to. The proof is unchanged, because a literal permutation commutes
with negation: the orbit of ~x is the negation of the orbit of x with the same words, a swap of x
and y swaps ~x and ~y, and the `dom` order is the lex order of the points' negations (the
preferred value first). `--orient max|min` forces one orientation for every point (the control:
a chain that fights the value choice); `auto` is `max` under `--order static` (T2's chains, byte
for byte) and the annotation's value choice under `--order search`.

Writes OUT.chain.json (the generators of each level as {var: literal} over the moved literal
variables, the levels, and each cut with its word, so that symmerge.py recomputes the witness
without dejavu) and OUT.fzn: IN.fzn with one constraint per cut before `solve` (bool_clause over
`var bool`, int_lin_le over `var 0..1`), which baguette then solves with --proof.

Trust: none of this is trusted. A wrong generator, a wrong orbit or a wrong word gives a `red` line
that VeriPB refuses. What the chain cannot do is find more symmetry than dejavu reports: its error
is one-sided (a missing generator is a smaller orbit, so fewer cuts).
Environment: DEJAVU (the binary; default /cluster/arthur/tools/dejavu-f984485/build/dejavu).
Optimisation models (`min:` in the .opb) are refused: their `red` steps would also have to show
that the witness keeps the objective (M15-symmetry-T4).
"""
import argparse, collections, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
DEJAVU = os.environ.get("DEJAVU", "/cluster/arthur/tools/dejavu-f984485/build/dejavu")


def neg(l):
    return l[1:] if l.startswith("~") else "~" + l


def apply(p, l):
    """the image of literal l under p, a {var: literal} map over the moved variables"""
    if l.startswith("~"):
        return neg(p.get(l[1:], l[1:]))
    return p.get(l, l)


def compose(s, t):
    """s o t (t first)"""
    r = {}
    for v in set(s) | set(t):
        im = apply(s, t.get(v, v))
        if im != v:
            r[v] = im
    return r


def inverse(p):
    r = {}
    for v, l in p.items():
        if l.startswith("~"):
            r[l[1:]] = "~" + v
        else:
            r[l] = v
    return r


def word_perm(gens, word):
    """the permutation of a word [g_k .. g_1] read right to left: g_k o .. o g_1"""
    p = {}
    for g in reversed(word):
        p = compose(gens[g], p)
    return p


# ---- the FlatZinc side: 0/1 variables, arrays, the search annotation -----------------------
def split_top(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def read_fzn(path):
    """kinds {name: 'bool'|'int01'|'other'}, arrays {name: [element names]}, defined vars,
    search variables in annotation order (None when the model has no search annotation),
    and whether the model optimises"""
    kinds, arrays, defined, order = {}, {}, set(), []
    solve = ""
    text = re.sub(r"%[^\n]*", "", open(path).read())     # comments may hold `;`
    for st in text.split(";"):
        st = " ".join(st.split())
        if not st:
            continue
        m = re.match(r"array\s*\[\s*(\d+)\s*\.\.\s*(\d+)\s*\]\s*of\s+var\s+(.+?)\s*:\s*([A-Za-z_][\w]*)\s*(::[^=]*)?(=\s*\[(.*)\])?\s*$", st, re.S)
        if m:
            lo, hi, dom, name = int(m.group(1)), int(m.group(2)), m.group(3).strip(), m.group(4)
            if m.group(6):
                arrays[name] = [e.strip() for e in split_top(m.group(7))]
            else:                                         # baguette's array-of-vars extension:
                k = kind_of(dom)                          # the elements are x[1] .. x[n]
                arrays[name] = [f"{name}[{i}]" for i in range(lo, hi + 1)]
                for e in arrays[name]:
                    kinds[e] = k
                    order.append(e)
            continue
        m = re.match(r"var\s+(.+?)\s*:\s*([A-Za-z_][\w]*)\s*(::.*?)?(=.*)?$", st, re.S)
        if m:
            name = m.group(2)
            kinds[name] = kind_of(m.group(1).strip())
            if m.group(3) and "is_defined_var" in m.group(3):
                defined.add(name)
            order.append(name)
            continue
        if st.startswith("solve"):
            solve = st
        elif st.startswith("constraint"):
            m = re.search(r"::\s*defines_var\(\s*([A-Za-z_][\w\[\]]*)\s*\)", st)
            if m:
                defined.add(m.group(1))
    search, value = None, {}
    if "_search" in solve:
        search = []
        for m in re.finditer(r"(?:int|bool)_search\(\s*(\[[^\]]*\]|[A-Za-z_][\w]*)\s*,\s*(\w+)\s*,\s*(\w+)", solve):
            vs = expand(m.group(1), arrays)
            search += vs
            for v in vs:                                  # the first annotation naming v decides
                value.setdefault(v, "max" if m.group(3) in ("indomain_max", "indomain_reverse_split") else "min")
    optimise = bool(re.search(r"\b(minimize|maximize)\b", solve))
    natural = [v for v in order if v not in defined]
    return kinds, arrays, search, natural, optimise, value


def kind_of(dom):
    if dom == "bool":
        return "bool"
    if re.fullmatch(r"0\s*\.\.\s*1", dom) or re.fullmatch(r"\{\s*0\s*,\s*1\s*\}", dom):
        return "int01"
    return "other"


def expand(tok, arrays):
    tok = tok.strip()
    if tok.startswith("["):
        out = []
        for e in split_top(tok[1:-1]):
            out += expand(e, arrays) if e in arrays else [e]
        return out
    return list(arrays.get(tok, [tok]))


def opb_names(opb):
    """baguette's `* name FZN -> PB` comments: the identifiers it had to sanitise"""
    names = {}
    for line in open(opb):
        if not line.startswith("*"):
            break
        m = re.match(r"\* name (\S+) -> (\S+)", line)
        if m:
            names[m.group(1)] = m.group(2)
    return names


# ---- dejavu ----------------------------------------------------------------------------------
def run_dejavu(graph, fixed, tag, vlit):
    """generators ({var: literal}, identity dropped) and group order of the automorphisms of the
    graph fixing each vertex of `fixed` ({vertex: rank})"""
    g = f"{graph}.{tag}"
    with open(graph) as fi, open(g, "w") as fo:
        for line in fi:
            if line.startswith("n "):
                _, v, c = line.split()
                if int(v) in fixed:
                    line = f"n {v} {1000 + fixed[int(v)]}\n"
            fo.write(line)
    t0 = time.time()
    out = subprocess.run([DEJAVU, g, "--silent", "--grp-sz", "--gens-file", g + ".gens"],
                         capture_output=True, text=True, check=True).stdout
    dt = time.time() - t0
    order = out.strip().splitlines()[-1]
    G = []
    for line in open(g + ".gens"):
        p = {}
        for cyc in re.findall(r"\(([^)]*)\)", line):
            vs = [int(t) + 1 for t in cyc.split()]
            for a, b in zip(vs, vs[1:] + vs[:1]):
                if a in vlit and not vlit[a].startswith("~"):
                    assert b in vlit, f"dejavu maps literal vertex {a} to non-literal {b}"
                    p[vlit[a]] = vlit[b]
        if p:
            G.append(p)
    os.remove(g)
    os.remove(g + ".gens")
    return G, order, dt


def orbit(G, c):
    """{literal b: word w_b} with w_b(c) = b, a BFS over literals"""
    W = {c: []}
    queue = collections.deque([c])
    while queue:
        p = queue.popleft()
        for i, s in enumerate(G):
            q = apply(s, p)
            if q not in W:
                W[q] = [i] + W[p]
                queue.append(q)
    return W


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    ap.add_argument("fzn"); ap.add_argument("opb"); ap.add_argument("out")
    ap.add_argument("--vars", help="break variables, FlatZinc names or arrays, comma separated")
    ap.add_argument("--depth", type=int, default=3)
    ap.add_argument("--score", choices=["orbit", "first", "shared"], default="orbit")
    ap.add_argument("--order", choices=["static", "search"], default="static",
                    help="search: the point is the first break variable in search order (--score "
                         "first) and the cut is oriented by the value choice (D-0181)")
    ap.add_argument("--orient", choices=["auto", "max", "min"], default="auto",
                    help="the value each point is pushed to: max (x_c v ~x_b, T2's), min "
                         "(~x_c v x_b); auto: max under --order static, the value choice under search")
    a = ap.parse_args()
    if a.order == "search":
        a.score = "first"

    kinds, arrays, search, natural, optimise, value = read_fzn(a.fzn)
    if optimise or any(l.startswith("min:") for l in open(a.opb)):
        sys.exit("symchain: optimisation model refused: a `red` cut would also have to keep the "
                 "objective (M15-symmetry-T4)")
    if a.vars:
        brk = []
        for v in a.vars.split(","):
            brk += expand(v.strip(), arrays)
        source = "--vars"
    elif search:
        brk, source = search, "search annotation"
    else:
        brk, source = natural, "non-defined variables (no search annotation)"
    names = opb_names(a.opb)
    pb = lambda v: names.get(v, v)
    lit_of = {v: pb(v) + "_ge_1" for v, k in kinds.items() if k in ("bool", "int01")}
    fzn_of = {l: v for v, l in lit_of.items()}            # PB literal -> FlatZinc 0/1 variable
    cands = [lit_of[v] for v in brk if v in lit_of]

    graph = a.out + ".dimacs"
    r = subprocess.run([sys.executable, os.path.join(HERE, "opb2graph.py"), a.opb, graph],
                       capture_output=True, text=True, check=True)
    graph_line = r.stdout.strip()
    vlit, litv = {}, {}
    for line in open(graph + ".map"):
        v, l = line.split()
        vlit[int(v)] = l
        litv[l] = int(v)
    cands = [c for c in cands if c in litv]
    rows = []
    if a.score == "shared":
        for line in open(a.opb):
            if line.startswith("@c"):
                rows.append(set(re.findall(r"~?([A-Za-z_][\w]*_ge_\d+)", line)))

    def orient(v):
        """the value the chain pushes FlatZinc variable v to: 'max' or 'min'"""
        if a.orient != "auto":
            return a.orient
        if a.order == "static":
            return "max"
        return value.get(v, "min")                       # SPEC 3.4: no annotation, min value

    def writable(lits):
        ks = {kinds[fzn_of[l.lstrip("~")]] for l in lits if l.lstrip("~") in fzn_of}
        return all(l.lstrip("~") in fzn_of for l in lits) and len(ks) == 1

    fixed, levels, cuts, gens_all = [], [], [], []
    dj_total = 0.0
    for lev in range(a.depth + 1):
        G, order, dt = run_dejavu(graph, {litv[c.lstrip("~")]: i for i, c in enumerate(fixed)}, f"L{lev}", vlit)
        dj_total += dt
        level = {"order": order, "dejavu_s": round(dt, 3), "generators": len(G)}
        gens_all.append(G)
        if lev > 0:                                       # G is the stabilizer of c_{lev-1}:
            c = fixed[-1]                                 # the swaps of the previous level's cuts
            for ct in cuts:
                if ct["level"] == lev - 1:
                    u = inverse(word_perm(gens_all[lev - 1], ct["word"]))   # u(b) = c
                    H = orbit(G, apply(u, c))
                    ct["swap"] = H.get(ct["b"])          # h(u(c)) = b, so h o u swaps b and c
            levels[-1]["swaps"] = sum(1 for ct in cuts if ct["level"] == lev - 1 and ct["swap"] is not None)
        if lev == a.depth or not G:
            level["stop"] = "depth" if G else "trivial group"
            levels.append(level)
            break
        seen, orbs = set(), {}
        for c in cands:
            if c in seen or c in {f.lstrip("~") for f in fixed}:
                continue
            W = orbit(G, c)
            for b in W:
                seen.add(b.lstrip("~"))
            if len(W) > 1 and writable(list(W)):
                orbs[c] = W
        if not orbs:
            level["stop"] = "no eligible break variable in a nontrivial orbit"
            levels.append(level)
            break
        pos = {c: i for i, c in enumerate(cands)}
        if a.score == "orbit":
            c = max(orbs, key=lambda s: (len(orbs[s]), -pos[s]))
        elif a.score == "first":
            c = min(orbs, key=lambda s: pos[s])
        else:
            fv = {f.lstrip("~") for f in fixed}
            sh = lambda s: sum(1 for R in rows if s in R and R & fv)
            c = max(orbs, key=lambda s: (sh(s), len(orbs[s]), -pos[s]))
        W = orbs[c]
        if a.order == "search":
            # the agreement argument needs every break variable before c in search order to be
            # fixed by G (an earlier point, or a trivial orbit). A break variable that is not a
            # candidate (an integer, or an orbit of mixed kinds) may be moved: say so.
            moved = {k for g in G for k in g}
            moved_vars = {k.rsplit("_", 2)[0] for k in moved if re.search(r"_(ge|eq)_-?\d+$", k)}
            cpos = brk.index(fzn_of[c])
            bad = [v for v in brk[:cpos] if pb(v) in moved_vars or (pb(v) + "_ge_1") in moved]
            level["prefix_fixed"] = not bad
            if bad:
                level["prefix_moved"] = bad[:3]
        val = orient(fzn_of[c])
        if val == "min":                                  # the point is ~x: the same words send
            W = {neg(b): w for b, w in W.items()}         # ~c to ~b
            c = neg(c)
        level.update({"point": c, "fzn": fzn_of[c.lstrip("~")], "value": val, "orbit": len(W),
                      "orbit_sizes": sorted((len(o) for o in orbs.values()), reverse=True)})
        levels.append(level)
        for b in sorted(W, key=lambda l: (l.lstrip("~") not in pos, pos.get(l.lstrip("~"), 0), l)):
            if b == c:
                continue
            cuts.append({"level": lev, "c": c, "b": b, "word": W[b],
                         "clause": [c] if b == neg(c) else [c, neg(b)]})
        fixed.append(c)

    # the cuts in FlatZinc, before `solve`
    def fzn_clause(clause):
        k = kinds[fzn_of[clause[0].lstrip("~")]]
        P = [fzn_of[l] for l in clause if not l.startswith("~")]
        N = [fzn_of[l[1:]] for l in clause if l.startswith("~")]
        if k == "bool":
            return f"constraint bool_clause([{','.join(P)}],[{','.join(N)}]);"
        cs = [-1] * len(P) + [1] * len(N)                 # sum(N) - sum(P) <= |N| - 1
        return f"constraint int_lin_le([{','.join(map(str, cs))}],[{','.join(P + N)}],{len(N) - 1});"
    F = open(a.fzn).read()
    i = F.rindex("solve")
    add = "".join(fzn_clause(ct["clause"]) + "\n" for ct in cuts)
    open(a.out + ".fzn", "w").write(F[:i] + "% ---- symmetry-breaking cuts, tools/symmetry/symchain.py ----\n" + add + F[i:])
    J = {"tool": "symchain.py", "dejavu": DEJAVU, "fzn": a.fzn, "opb": a.opb, "graph": graph_line,
         "break_vars": source, "score": a.score, "order": a.order, "orient": a.orient, "depth": a.depth, "dejavu_s": round(dj_total, 3),
         "levels": levels, "generators": gens_all, "cuts": cuts}
    with open(a.out + ".chain.json", "w") as f:
        json.dump(J, f)
    print(f"symchain: {graph_line}")
    for lev in levels:
        print("  level " + json.dumps(lev))
    print(f"symchain: group {levels[0]['order']}, {len(fixed)} levels, {len(cuts)} cuts, "
          f"dejavu {dj_total:.2f} s, break variables from {source}, order {a.order}, "
          f"points {' '.join(lv['point'] for lv in levels if 'point' in lv)} -> {a.out}.fzn")


if __name__ == "__main__":
    main()
