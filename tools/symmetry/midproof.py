#!/usr/bin/env python3
"""The proof-side probe: can a symmetry-breaking cut be introduced in the MIDDLE of baguette's
proof, at the point a search would decide to use it, rather than at the head before any learned
constraint exists? Written for M15-symmetry-T3 (symmetry breaking that follows the search);
D-0181 records the answer, what VeriPB accepts in the middle of a proof.

    midproof.py MERGED.pbp EXTRA.chain.json OUT.pbp [--level L] [--at F] [--stc] [--subproof]
                [--first K] [--as-rup]

Writes OUT.pbp and one summary line on stdout; exit 0. It stops with a `midproof: ...` message
and status 1 when level L has no cut with a swap or baguette's part has no labelled line, and
argparse's 2 on a usage error. --first K inserts only the first K cuts (0, the default: all);
--as-rup writes the inserted cuts as bare `rup` lines, the control: if VeriPB accepts them they
are implied where they stand, and a `red` there proves nothing.

MERGED.pbp is symmerge.py's output (the cuts of a chain at the head, then baguette's proof, whose
lines all carry @labels, so a new labelled line can go anywhere). EXTRA.chain.json is another
symchain.py run on the SAME .opb: the cuts of its level L are inserted, each as

  @t3_<k> red <cut> : <the swap witness> ;

after the fraction F of baguette's lines (default 0.5), as a search would when it extends its chain
or changes it during the run. Only cuts with a swap (`red`, no order) are inserted; `dom` would need
an order loaded mid-proof. Two uses:

  - EXTRA = the same chain one level deeper (symchain --depth D+1), L = D: a chain EXTENDED during
    the search. Its witness fixes every earlier point, so the earlier cuts map onto cuts.
  - EXTRA = a chain from another base (symchain --vars starting elsewhere), L = 0: a chain CHANGED
    during the search. Its witness need not fix the first chain's points: the mix that D-0179
    (the static pipeline, whose cuts are proved by `red` with a swap) and the ROADMAP row say
    `red` must refuse.

--stc writes `strengthening_to_core on ;` right after the `f` line, before the head's cuts. In that
mode VeriPB 3.0.2 checks a `red` only against the CORE, not against the derived constraints
(baguette's learned `rup` lines): veripb-checker src/rules/red_strengthening.rs,
`add_derived_goals = !is_strengthening_to_core`. Without it, every learned constraint the witness
touches is a proof goal of its own, and its image is in general not implied (measured: refused).

A CHECKER BUG this probe found (D-0181, both 3.0.2 builds, d5644ca4 and 78db9573): in that mode a
`red` line WITHOUT an explicit subproof adds its constraint to the DERIVED set (RedStrengtheningRule
does not override `add_constraints_to_core`, rules.rs:107, which DomStrengtheningRule does), and
later `red` lines skip the derived set: so they are checked against no earlier cut at all. Two
contradictory orientations of one cut are then both accepted, and a SATISFIABLE formula gets
`s VERIFIED UNSATISFIABLE` (two variables, x1 + x2 = 1: bench/symmetry/stc_bug/). --subproof is the
workaround: with `: subproof` .. `qed ;` the constraint goes to the core and is checked.
"""
import argparse, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symchain import apply, compose, inverse, word_perm  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("merged"); ap.add_argument("extra"); ap.add_argument("out")
    ap.add_argument("--level", type=int, default=0)
    ap.add_argument("--at", type=float, default=0.5)
    ap.add_argument("--stc", action="store_true")
    ap.add_argument("--subproof", action="store_true",
                    help="write every `red` line (the head's and the inserted ones) with an empty "
                         "explicit subproof (`: subproof` .. `qed ;`): the workaround, see below")
    ap.add_argument("--first", type=int, default=0, help="insert only the first K cuts (0: all)")
    ap.add_argument("--as-rup", action="store_true",
                    help="the probe: write the inserted cuts as bare `rup` lines. If VeriPB accepts "
                         "them they are implied where they stand, and a `red` there proves nothing")
    a = ap.parse_args()

    J = json.load(open(a.extra))
    ins, skipped = [], 0
    for k, ct in enumerate(c for c in J["cuts"] if c["level"] == a.level):
        if ct.get("swap") is None:
            skipped += 1
            continue
        lv, c, b = ct["level"], ct["c"], ct["b"]
        t = word_perm(J["generators"][lv], ct["word"])
        w = compose(word_perm(J["generators"][lv + 1], ct["swap"]), inverse(t))
        assert apply(w, b) == c and apply(w, c) == b
        cl = " ".join(f"+1 {l}" for l in ct["clause"])
        wit = " ".join(f"{v} -> {l}" for v, l in sorted(w.items()))
        ins.append(f"@t3_{k} rup {cl} >= 1 ;" if a.as_rup else f"@t3_{k} red {cl} >= 1 : {wit} ;")
    if a.first:
        ins = ins[:a.first]
    if not ins:
        sys.exit(f"midproof: no cut with a swap on level {a.level} ({skipped} without)")

    P = open(a.merged).read().splitlines()
    start = next(i for i, l in enumerate(P) if l.startswith("% ---- baguette's proof"))
    body = [i for i in range(start + 1, len(P)) if P[i].startswith("@")]
    if not body:
        sys.exit("midproof: baguette's part has no labelled line")
    pos = body[min(len(body) - 1, int(a.at * len(body)))] + 1      # after that line
    learned = sum(1 for i in body if i < pos and " rup " in P[i])
    # baguette deletes its learned constraints by `del range @a @b` ([a, b) in id order). A range
    # that spans the insertion point would delete the inserted cuts too, which in
    # strengthening-to-core mode are core and may not be deleted: split it around them.
    after = next((P[i].split()[0] for i in body if i >= pos), None)
    where = {P[i].split()[0]: i for i in body}
    rest = []
    for l in P[pos:]:
        t = l.split()
        if len(t) >= 4 and t[0] == "del" and t[1] == "range" and t[2] in where and t[3] in where \
                and where[t[2]] < pos <= where[t[3]]:
            rest += [f"del range {t[2]} @t3_0 ;"] + ([f"del range {after} {t[3]} ;"] if after != t[3] else [])
        else:
            rest.append(l)
    out = P[:pos] + [f"% ---- {len(ins)} cuts of level {a.level} inserted here (tools/symmetry/midproof.py) ----"] \
        + ins + rest
    if a.stc:
        f = next(i for i, l in enumerate(out) if l.startswith("f "))
        out = out[:f + 1] + ["strengthening_to_core on ;"] + out[f + 1:]
    if a.subproof:
        out2 = []
        for l in out:
            if l.startswith("@") and " red " in l and l.endswith(" ;"):
                out2 += [l[:-2] + " : subproof", "qed ;"]
            else:
                out2.append(l)
        out = out2
        ins = [l[:-2] + " : subproof" for l in ins]
    open(a.out, "w").write("\n".join(out) + "\n")
    first = out.index(ins[0]) + 1
    print(f"midproof: {len(ins)} cuts of level {a.level} ({skipped} without a swap skipped) after "
          f"{learned} learned rup lines, first at line {first}{', strengthening_to_core on' if a.stc else ''}"
          f"{', explicit subproofs' if a.subproof else ''}"
          f" -> {a.out}")


if __name__ == "__main__":
    main()
