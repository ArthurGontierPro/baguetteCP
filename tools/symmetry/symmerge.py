#!/usr/bin/env python3
"""symmerge.py CHAIN.json ORIG.opb BROKEN.opb BROKEN.pbp MERGED.pbp [--bad-witness K | --bad-cut K]
                   [--as-rup K | --unit-probe K] [--rule auto|red|dom|transversal]
-- baguette's proof of the BROKEN model turned into a proof about the ORIGINAL one. Written for
M15-symmetry-T2, the pipeline beside baguette (D-0179: cuts proved by `red` with a swap, `dom`
where the group has none).

CHAIN.json is symchain.py's, BROKEN.opb/.pbp baguette's run on symchain's OUT.fzn, ORIG.opb
baguette's .opb of the model without breaking. The merged proof is checked by VeriPB against
ORIG.opb itself, unchanged:

  veripb ORIG.opb MERGED.pbp

baguette names every row (@c1, @c2, ...) and its proof cites rows by these names only. The cuts are
the last constraints before `solve`, so baguette mints them last: BROKEN.opb must be ORIG.opb
label for label, row for row, plus one row per cut and nothing else, and each extra row must be
its cut's clause. symmerge refuses anything else. The merged proof is BROKEN.pbp with its `f`
line counting ORIG.opb's rows, and, right after it, one line per cut, in chain order:

  @cK red <the row of @cK> : <witness> ;      or      @cK dom <the row of @cK> : <witness> ;

The rule and its witness, by --rule (default auto):
  auto          a cut with a `swap` (symchain.py's step 3) is `red` with the element h o u of
                G_{i-1} that SWAPS c and b (checked here); a cut without one is `dom` with the
                word w_b itself, under the lex order of the points' negations: codes-cp's order
                definition (def_order below), loaded by `load_order` before the cuts and
                unloaded after them. No order is loaded when no cut is `dom`.
  red           the swap where there is one, the transversal witness below otherwise.
  dom           every cut by `dom`.
  transversal   every cut by `red` with w_b^-1, the inverse of the cut's word in its level's
                generators, which sends b to c (the witness of D-0177, the first study, with
                dejavu as distributed and satsuma's Schreier cuts; D-0179 section 2 measured it
                refused on the second cut of a level, on php_unsat).

Why a `red` line with w_b^-1 holds (D-0177 §4): under the negated cut (c false, b true) the image of
the cut contains ~c, which holds; the witness is an automorphism of ORIG.opb, so the model's rows
map onto rows; and the earlier cuts must map onto constraints that follow by unit propagation, which
VeriPB checks rather than this script. baguette's proof then follows unchanged.

Mutation controls (negative tests, each on one cut K, 0-based in chain order):
  --bad-witness K   the witness of cut K becomes the transposition of c and b alone, which is
                    not an automorphism of the model (codes-cp's BAD=1)
  --bad-cut K       cut K (on a level >= 1) is derived as c v ~c_1 instead of c v ~b, with its
                    true witness: c_1, the first point, is fixed by the level's group, so it is in
                    no orbit of it and no element of the chain sends it to c.
                    (Flipping the second literal, c v b, is NOT a sound control under `dom`: on
                    hamming_w4 VeriPB accepts it, and rightly, because with c, b and the points
                    before c at 0 the parity rows propagate every coordinate to 0, against
                    sum x >= 1, so the dominance goal closes by propagation.)
VeriPB must refuse both at the mutated line, which symmerge prints (`line N`).
  --as-rup K        the PROBE that makes a control meaningful (D-0181, the record of what VeriPB
                    accepts mid-proof): cut K written as a bare
                    `rup` line. If VeriPB accepts it, cut K is implied by the lines before it, so
                    any witness or any weaker mutation of it would be accepted too, and a control
                    on it tests nothing (measured: under `--order search` on php_escape_sat every
                    cut after the first of a level is RUP, through the pigeon's exactly-one row).
  --unit-probe K    cut K written as the UNIT clause c (its point alone), with its true witness and
                    rule. If VeriPB accepts it, every clause c v X is a weakening of a derivable
                    line, so --bad-cut (c v ~c_1) cannot be refused there and that control is
                    VACUOUS, not failed (measured: php_escape_sat under `--order search`, where c =
                    ~x_2 and the pigeon's exactly-one row makes the swapped image ~x_3 hold).

A point may be a NEGATIVE literal (`symchain.py --order search` under a min value choice, D-0181):
its cuts are ~x_c v x_b, the witnesses are the same permutations, and the `dom` order is the lex
order of the points' negations, so the preferred value comes first either way.

Prints one summary line (cuts by rule, the largest witness, the mutated line if any). Exit 0 once
MERGED.pbp is written; 1 with a `symmerge: ...` message when BROKEN.opb is not ORIG.opb plus one
row per cut or --bad-cut names a level-0 cut, and on a failed internal check (an AssertionError:
a word that does not send c to b, a swap that does not swap, a proof without its header); 2
(argparse) on a usage error.
"""
import argparse, json, re, sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symchain import apply, compose, inverse, word_perm, neg  # noqa: E402


def def_order(name, N, coef):
    """codes-cp's scripts/domproof.py, verbatim: an order on N variables, u <= v iff
    sum coef[p] * (v_p - u_p) >= 0 (a weighted sum: lex with coef 2^(N-1-p))"""
    terms = " ".join(f"{-c} u{p + 1}" for p, c in enumerate(coef)) + " " + \
            " ".join(f"{c} v{p + 1}" for p, c in enumerate(coef))
    us = " ".join(f"u{p + 1}" for p in range(N)); vs = " ".join(f"v{p + 1}" for p in range(N))
    ws = " ".join(f"w{p + 1}" for p in range(N))
    return [f"def_order {name}", "  vars", f"    left {us};", f"    right {vs};", "    aux;", "  end;",
            "  def", f"    {terms} >= 0;", "  end;",
            "  transitivity", "    vars", f"      fresh_right {ws};", "    end;", "    proof",
            "      proofgoal #1", "        pol 1 2 + 3 +;", "      qed : -1;", "    qed;", "  end;", "end;"]


def lit_swap(c, b):
    """the map on variables of the literal transposition c <-> b (b = ~c: c's variable negated)"""
    def put(m, src, dst):                                 # literal src -> literal dst
        if src.startswith("~"):
            m[src[1:]] = neg(dst)
        else:
            m[src] = dst
    m = {}
    put(m, c, b)
    if b.lstrip("~") != c.lstrip("~"):
        put(m, b, c)
    return m


def rows(opb):
    """[(label, body)] in file order, and the `#constraint=` count"""
    R, n = [], None
    for line in open(opb):
        if line.startswith("* #variable="):
            n = int(re.search(r"#constraint=\s*(\d+)", line).group(1))
        elif line.startswith("@c"):
            lab, body = line.rstrip("\n").split(" ", 1)
            R.append((lab, body))
    return R, n


def lits_of(body):
    """the literal set and degree of a clause row `+1 l1 +1 l2 >= 1 ;`, else None"""
    m = re.fullmatch(r"((?:\+1 ~?\S+ )+)>= 1 ;", body.strip())
    if not m:
        return None
    return frozenset(m.group(1).split()[1::2])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("chain"); ap.add_argument("orig"); ap.add_argument("broken")
    ap.add_argument("pbp"); ap.add_argument("merged")
    ap.add_argument("--rule", choices=["auto", "red", "dom", "transversal"], default="auto")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--bad-witness", type=int)
    g.add_argument("--bad-cut", type=int)
    g.add_argument("--as-rup", type=int)
    g.add_argument("--unit-probe", type=int)
    a = ap.parse_args()

    J = json.load(open(a.chain))
    cuts = J["cuts"]
    O, n0 = rows(a.orig)
    B, nb = rows(a.broken)
    assert n0 == len(O) and nb == len(B), "a #constraint= count disagrees with the rows"
    if B[:len(O)] != O:
        k = next(i for i, (x, y) in enumerate(zip(B, O)) if x != y) if len(B) >= len(O) else len(B)
        sys.exit(f"symmerge: BROKEN.opb is not ORIG.opb plus rows at the end (first difference at "
                 f"row {k + 1})")
    extra = B[len(O):]
    if len(extra) != len(cuts):
        sys.exit(f"symmerge: {len(extra)} extra rows for {len(cuts)} cuts")
    lines, nrule, rule_of = [], {"red": 0, "dom": 0}, []
    for i, ((lab, body), ct) in enumerate(zip(extra, cuts)):
        if lits_of(body) != frozenset(ct["clause"]):
            sys.exit(f"symmerge: row {lab} `{body}` is not cut {i} {ct['clause']}")
        lv, c, b = ct["level"], ct["c"], ct["b"]
        t = word_perm(J["generators"][lv], ct["word"])                    # t(c) = b
        assert apply(t, c) == b, f"cut {i}: its word does not send c to b"
        swap = ct.get("swap")
        if a.rule == "dom" or (a.rule == "auto" and swap is None):
            rule, w = "dom", t
        elif swap is None or a.rule == "transversal":                    # D-0177's witness
            rule, w = "red", inverse(t)
        else:
            rule, w = "red", compose(word_perm(J["generators"][lv + 1], swap), inverse(t))
            assert apply(w, b) == c and apply(w, c) == b, f"cut {i}: the swap does not swap"
        nrule[rule] += 1
        rule_of.append(rule)
        if a.bad_witness == i:                            # the literal transposition c <-> b,
            c, b = ct["c"], ct["b"]                       # as a map on variables (T2's map
            if not c.startswith("~"):                     # when c is positive, unchanged)
                w = {c: b, b: c} if not b.startswith("~") else {c: b}
            else:
                w = lit_swap(c, b)
        if a.bad_cut == i:
            if lv == 0:
                sys.exit(f"symmerge: --bad-cut {i}: cut {i} is on level 0, take one on a later level")
            d = J["levels"][0]["point"]                   # fixed by G_lv: never in c's orbit
            body = f"+1 {c} +1 {neg(d)} >= 1 ;"
        wit = " ".join(f"{v} -> {l}" for v, l in sorted(w.items()))
        if a.unit_probe == i:                             # the probe: is the point alone derivable?
            body = f"+1 {c} >= 1 ;"
        if a.as_rup == i:                                 # the probe: is cut i implied already?
            lines.append(f"{lab} rup {body.rstrip(' ;')} ;")
        else:
            lines.append(f"{lab} {rule} {body.rstrip(' ;')} : {wit} ;")
    points = [lv["point"] for lv in J["levels"] if "point" in lv]
    k = next((x for x in (a.bad_witness, a.bad_cut, a.as_rup, a.unit_probe) if x is not None), None)
    target = lines[k] if k is not None else None
    if nrule["dom"]:
        N = len(points)
        lines = def_order(f"symlex{N}", N, [2 ** (N - 1 - p) for p in range(N)]) + \
            [f"load_order symlex{N} " + " ".join(neg(c) for c in points) + " ;"] + lines + ["load_order ;"]

    P = open(a.pbp).read().splitlines()
    assert P[0].startswith("pseudo-Boolean proof version") and P[1] == f"f {nb} ;", P[:2]
    head = [P[0], f"f {n0} ;",
            f"% ---- {len(cuts)} symmetry-breaking cuts, `red` with dejavu's permutations "
            "(tools/symmetry/symmerge.py) ----"]
    with open(a.merged, "w") as f:
        f.write("\n".join(head + lines + ["% ---- baguette's proof of the broken model, unchanged ----"]
                          + P[2:]) + "\n")
    what = ("bad witness" if a.bad_witness is not None else "bad cut" if a.bad_cut is not None
            else "as rup" if a.as_rup is not None else "unit probe")
    mut = "" if k is None else (f", MUTATED: {what}"
                                f" at cut {k}, {rule_of[k]}, line {len(head) + lines.index(target) + 1}")
    wl = [len(l.split(" : ")[-1].split(" -> ")) - 1 for l in lines if " red " in l or " dom " in l]
    print(f"symmerge: {len(cuts)} cuts, {nrule['red']} red, {nrule['dom']} dom, largest witness "
          f"{max(wl, default=0)} moved variables{mut} -> {a.merged}")


if __name__ == "__main__":
    main()
