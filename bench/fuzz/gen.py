#!/usr/bin/env python3
"""Random small FlatZinc models for proof-checking sweeps (M7-T21, D-0084).

    python3 bench/fuzz/gen.py MODE SEED        # prints one model on stdout

MODE is one of gcc, elem, mix, ad. The model is a pure function of (MODE, SEED):
the same pair always prints the same bytes, which is what makes a failing seed a
reproducer. Do NOT reorder the random calls below -- every seed quoted in README.md
was found with exactly this sequence.

Widths are SINGLE DIGIT by construction (D-0028: the order encoding is
width-proportional): 4..7 variables over 1..D with D in 3..5, counts in 0..3.
"""
import random
import sys

MODES = ("gcc", "elem", "mix", "ad")


def gen(mode, seed):
    r = random.Random(seed)
    nv = r.randint(4, 7)
    D = r.randint(3, 5)
    L = []
    names = [f"x{k}" for k in range(nv)]
    for k in range(nv):
        L.append(f"var 1..{D}: x{k} :: output_var;")
    cons = []
    if mode in ("gcc", "mix"):
        for g in range(r.randint(1, 2)):
            sc = r.sample(names, r.randint(3, min(5, nv)))
            cov = sorted(r.sample(range(1, D + 1), r.randint(1, min(3, D))))
            cs = []
            for ci, cv in enumerate(cov):
                if r.random() < 0.5:
                    cn = f"n{g}_{ci}"
                    lo = r.randint(0, 1)
                    hi = r.randint(lo + 1, 3)
                    L.append(f"var {lo}..{hi}: {cn} :: output_var;")
                    cs.append(cn)
                    names.append(cn)  # a count may join a LATER gcc's scope
                else:
                    cs.append(str(r.randint(0, 2)))
            cons.append(
                f"constraint fzn_global_cardinality([{','.join(sc)}],"
                f"[{','.join(map(str, cov))}],[{','.join(cs)}]);")
    if mode in ("ad",):
        for g in range(r.randint(1, 2)):
            sc = r.sample(names[:nv], r.randint(3, min(4, nv)))
            cons.append(f"constraint all_different_int([{','.join(sc)}]);")
    if mode in ("elem", "mix", "ad"):
        for e in range(r.randint(1, 3)):
            i, c = r.sample(names[:nv], 2)
            arr = [r.randint(1, D) for _ in range(D)]
            cons.append(f"constraint array_int_element({i},[{','.join(map(str, arr))}],{c});")
    for _ in range(r.randint(1, 4)):
        a, b = r.sample(names[:nv], 2)
        cons.append(f"constraint int_ne({a},{b});")
    for _ in range(r.randint(0, 2)):
        k = r.randint(2, 3)
        vs = r.sample(names[:nv], k)
        co = [r.choice([1, -1, 2]) for _ in vs]
        cons.append(
            f"constraint int_lin_le([{','.join(map(str, co))}],[{','.join(vs)}],{r.randint(0, D * k)});")
    sv = names[:]
    r.shuffle(sv)
    ann = (f"int_search([{','.join(sv)}], "
           f"{r.choice(['input_order', 'first_fail', 'smallest', 'largest'])}, "
           f"{r.choice(['indomain_min', 'indomain_max', 'indomain_median', 'indomain_split'])}, complete)")
    return "\n".join(L + cons + [f"solve :: {ann} satisfy;"]) + "\n"


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] not in MODES:
        sys.exit(f"usage: gen.py {{{'|'.join(MODES)}}} SEED")
    sys.stdout.write(gen(sys.argv[1], int(sys.argv[2])))
