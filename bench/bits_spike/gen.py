#!/usr/bin/env python3
"""gen.py -- M8-bits-encoding-T0: the SAME bound propagation, written four ways.

Stdlib only; run it with `python3 -I`. No solver code is involved: this writes an
`.opb` and a `.pbp` by hand, for VeriPB 3.0.2 (docs/PROOF-FORMAT.md section 2a), so
that the checker, its elaborator and `cake_pb` can be measured on the derivation
ALONE, free of search, of the writer and of the heap.

The model is D-0028's two-variable shape made satisfiable: `a, b` declared `0..w`,
one row `a + b <= c` with `c = w // 2`, objective `min -b`. The propagation is the
root pruning `Linear` makes from that row with `a` at its declared lower bound:
`b <= c`, i.e. the literal `~b_ge_m` with `m = c + 1`. It is load-bearing because
the proof concludes `BOUNDS -c INF` on the objective, and the checker can establish
that lower bound only from the derived literal (see README.md, "What makes the
lines load-bearing"). The model is satisfiable (a = b = 0), so a `red`, a `pol` or
a `rup` is judged, not waved through (D-0053, D-0066).

Two arms, two styles:

  order   the eager order encoding of PROOF-FORMAT section 3: `x_ge_v` for
          1 <= v <= w and the w-1 ladder rungs per variable, all in the `.opb`.
          The row is the encoding's expansion, one literal per value. The
          justification is the cancellation of w ladder rungs (D-0028): weaken
          every `a` literal, fold `b`'s ladder up to rung m-1 (one row moves one
          term one rung, lib/core/ladder.ml), weaken `b` above m, saturate.
  bits    GCS's carrier: n = bit_length(w) bits per variable plus two bound rows.
          The order atom `[b >= m]` does not exist in the `.opb`; the proof mints
          it with a `red` pair whose witness touches ONLY the fresh atom
          (docs/ROADMAP.md, M8-bits-encoding preamble; NOT D-0031's rotation,
          which permutes existing literals). The justification is then three
          citations: row + lower-bound row + the atom's defining row, saturate.

  rup     the pruning is one `rup` line and the checker reconstructs the reason.
  pol     the pruning is an explicit cutting-planes line.

In both styles an `e` line pins the derived constraint syntactically to the claim
(M1-T51: the control `pol` never had), so a `pol` that derives the wrong thing is
REJECTED at that line rather than silently carried.

Broken variants, one per arm x style plus one per `red` of the bits arm, each of
which the checker must refuse with a checking error over this SATISFIABLE model:

  order/rup, bits/rup     the claim's literal flipped: `b_ge_m >= 1`
  order/pol               the fold stops one rung too high (derives b <= c+1,
                          a weaker bound) -- the `e` pin catches it
  bits/pol                the atom's defining row cited in the wrong direction
  bits/* broken-red-B1    B1's witness `b_ge_m -> 1` instead of `-> 0`
  bits/* broken-red-B2    B2's witness `b_ge_m -> 0` instead of `-> 1`

Layout: <out>/w<w>/<arm>/<style>/{model.opb,proof.pbp,proof.broken.pbp,...}
"""

import argparse
import os
import sys

STYLES = ("rup", "pol")
ARMS = ("order", "bits")


def params(w):
    c = w // 2  # a + b <= c
    m = c + 1  # the pruned literal is ~[b >= m]
    assert 2 <= m < w, "m must be an interior value so the atom is genuine"
    return c, m


# ---------------------------------------------------------------- order arm


def order_opb(w, c):
    lines = []
    nrows = 1 + 2 * (w - 1)
    lines.append(f"* #variable= {2 * w} #constraint= {nrows}")
    lines.append("min: " + " ".join(f"-1 b_ge_{v}" for v in range(1, w + 1)) + " ;")
    row = " ".join(f"-1 a_ge_{v}" for v in range(1, w + 1)) + " " + " ".join(
        f"-1 b_ge_{v}" for v in range(1, w + 1)
    )
    lines.append(f"@R {row} >= {-c} ;")
    for x in ("a", "b"):
        for v in range(1, w):
            lines.append(f"@l{x}_{v} +1 ~{x}_ge_{v + 1} +1 {x}_ge_{v} >= 1 ;")
    return "\n".join(lines) + "\n", nrows


def order_pol(w, m, top):
    """R, weaken all of a, fold b's ladder to rung `top`-1, weaken b above `top`, s."""
    toks = ["@R"]
    toks += [f"a_ge_{v} w" for v in range(1, w + 1)]
    for v in range(1, top):
        toks.append("@lb_%d +" % v if v == 1 else "@lb_%d %d * +" % (v, v))
    toks += [f"b_ge_{v} w" for v in range(top + 1, w + 1)]
    toks.append("s")
    return "@G pol " + " ".join(toks) + " ;"


def order_proof(w, c, m, nrows, style, broken=False):
    out = ["pseudo-Boolean proof version 3.0", f"f {nrows} ;"]
    if style == "rup":
        lit = f"b_ge_{m}" if broken else f"~b_ge_{m}"
        out.append(f"@G rup +1 {lit} >= 1 ;")
    else:
        out.append(order_pol(w, m, top=m + 1 if broken else m))
    out += tail(c, m)
    return "\n".join(out) + "\n"


# ----------------------------------------------------------------- bits arm


def bits_terms(x, n, neg=False, sign="+"):
    t = "~" if neg else ""
    return " ".join(f"{sign}{1 << i} {t}{x}_bit_{i}" for i in range(n))


def bits_opb(w, c):
    n = w.bit_length()
    lines = []
    lines.append(f"* #variable= {2 * n} #constraint= 5")
    lines.append("min: " + bits_terms("b", n, sign="-") + " ;")
    lines.append(f"@R {bits_terms('a', n, sign='-')} {bits_terms('b', n, sign='-')} >= {-c} ;")
    for x in ("a", "b"):
        lines.append(f"@{x.upper()}lo {bits_terms(x, n)} >= 0 ;")
        lines.append(f"@{x.upper()}hi {bits_terms(x, n, sign='-')} >= {-w} ;")
    return "\n".join(lines) + "\n", 5, n


def bits_atom(n, m, flip1=False, flip2=False):
    """The red pair that mints [b >= m]: B1 `b_ge_m -> B >= m`, B2 `B >= m -> b_ge_m`."""
    full = (1 << n) - m
    w1 = "1" if flip1 else "0"
    w2 = "0" if flip2 else "1"
    return [
        f"@B1 red {bits_terms('b', n)} +{m} ~b_ge_{m} >= {m} : b_ge_{m} -> {w1} ;",
        f"@B2 red {bits_terms('b', n, neg=True)} +{full} b_ge_{m} >= {full} : b_ge_{m} -> {w2} ;",
    ]


def bits_proof(n, c, m, nrows, style, broken=None):
    out = ["pseudo-Boolean proof version 3.0", f"f {nrows} ;"]
    out += bits_atom(n, m, flip1=(broken == "red-B1"), flip2=(broken == "red-B2"))
    if style == "rup":
        lit = f"b_ge_{m}" if broken == "claim" else f"~b_ge_{m}"
        out.append(f"@G rup +1 {lit} >= 1 ;")
    else:
        defn = "@B2" if broken == "claim" else "@B1"
        out.append(f"@G pol @R @Alo + {defn} + s ;")
    out += tail(c, m)
    return "\n".join(out) + "\n"


# ------------------------------------------------------------------- common


def tail(c, m):
    return [
        f"@E e +1 ~b_ge_{m} >= 1 : @G ;",
        "output NONE ;",
        f"conclusion BOUNDS {-c} INF ;",
        "end pseudo-Boolean proof ;",
    ]


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(text)
    return len(text.encode())


def top_level_lines(text):
    return sum(1 for ln in text.splitlines() if ln and not ln.startswith("%"))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", default="out")
    ap.add_argument("--widths", default="1000,10000,100000,1000000")
    ap.add_argument("--arms", default=",".join(ARMS))
    ap.add_argument("--styles", default=",".join(STYLES))
    args = ap.parse_args()
    widths = [int(x) for x in args.widths.split(",")]
    print("width\tarm\tstyle\tatoms\tlines\topb_bytes\tpbp_bytes\tfiles")
    for w in widths:
        c, m = params(w)
        for arm in args.arms.split(","):
            if arm == "order":
                opb, nrows = order_opb(w, c)
            else:
                opb, nrows, n = bits_opb(w, c)
            for style in args.styles.split(","):
                d = os.path.join(args.out, f"w{w}", arm, style)
                ob = write(os.path.join(d, "model.opb"), opb)
                if arm == "order":
                    proof = order_proof(w, c, m, nrows, style)
                    broken = {"proof.broken.pbp": order_proof(w, c, m, nrows, style, broken=True)}
                    atoms = 0
                else:
                    proof = bits_proof(n, c, m, nrows, style)
                    broken = {
                        "proof.broken.pbp": bits_proof(n, c, m, nrows, style, broken="claim"),
                        "proof.broken-red-B1.pbp": bits_proof(n, c, m, nrows, style, broken="red-B1"),
                        "proof.broken-red-B2.pbp": bits_proof(n, c, m, nrows, style, broken="red-B2"),
                    }
                    atoms = 1
                pb = write(os.path.join(d, "proof.pbp"), proof)
                for name, text in broken.items():
                    write(os.path.join(d, name), text)
                print(
                    f"{w}\t{arm}\t{style}\t{atoms}\t{top_level_lines(proof)}\t{ob}\t{pb}\t"
                    f"{d}: model.opb proof.pbp {' '.join(broken)}"
                )
                sys.stdout.flush()


if __name__ == "__main__":
    main()
