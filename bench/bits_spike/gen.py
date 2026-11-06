#!/usr/bin/env python3
"""gen.py -- M8-bits-encoding-T0: the SAME bound propagation, written four ways.

Stdlib only; run it with `python3 -I`. No solver code is involved: this writes an
`.opb` and a `.pbp` by hand, for VeriPB 3.0.2 (docs/PROOF-FORMAT.md section 2a), so
that the checker, its elaborator and `cake_pb` can be measured on the derivation
ALONE, free of search, of the writer and of the heap.

The model is D-0028's two-variable shape made satisfiable, with one Boolean added
so that the conclusion can only be reached THROUGH the derived literal:

    a in [l, w]   b in [0, w]   z in {0, 1}        l = w//4
    R:  a + b <= c                                c = l + w//2
    T:  z  or  b >= m                             m = c - l + 1 = w//2 + 1
    min z

The propagation is the root pruning `Linear` makes from R with `a` at its declared
lower bound: `b <= c - l`, i.e. the literal `~b_ge_m`. The proof then derives
`z >= 1` from T and that literal (line Z, a `pol` that CITES the pruning), and
concludes `BOUNDS 1 : Z INF`. A proof whose pruning line carries no bound (the
`control-noG` variant, where it is a copy of R) is therefore refused at the
conclusion, which is what makes the pruning load-bearing. The model is satisfiable
(a = l, b = 0, z = 1), so a `red`, a `pol` or a `rup` is judged, not waved through
(D-0053, D-0066).

Two arms, two styles:

  order   the eager order encoding of PROOF-FORMAT section 3: `x_ge_v` for
          l < v <= u and the ladder rungs, all in the `.opb`; R is the encoding's
          expansion, one literal per value, its constant measured against the
          declared bound (D-0028, "declared offsets"). The justification is the
          cancellation of Theta(w) ladder rungs: weaken every `a` literal, fold
          `b`'s ladder up to rung m-1 (one row moves one term one rung,
          lib/core/ladder.ml), weaken `b` above m, saturate.
  bits    GCS's carrier: n = bit_length(w) bits per variable plus two bound rows.
          The order atom `[b >= m]` does not exist in the `.opb`; the proof mints
          it with a `red` pair whose witness touches ONLY the fresh atom
          (docs/ROADMAP.md, M8-bits-encoding preamble; NOT D-0031's rotation,
          which permutes existing literals). The justification is then three
          citations: row + lower-bound row + the atom's defining row, saturate.
          Using the literal in Z needs the atom's other direction (B2) as well.

  rup     the pruning is one `rup` line and the checker reconstructs the reason.
  pol     the pruning is an explicit cutting-planes line.

In both styles an `e` line pins the derived constraint syntactically to the claim
(M1-T51: the control `pol` never had), so a `pol` that derives the wrong thing is
REJECTED at that line rather than silently carried.

Variants the checker must refuse over this SATISFIABLE model, one per arm x style
plus one per `red` of the bits arm, plus the load-bearing control:

  broken        order/rup, bits/rup   the claim's literal flipped: `b_ge_m >= 1`
                order/pol             the fold stops one rung too high (derives
                                      b <= c-l+1, a weaker bound): the `e` pin
                                      catches it
                bits/pol              the atom's defining row cited in the wrong
                                      direction: the `e` pin catches it
  broken-red-B1 bits                  B1's witness `b_ge_m -> 1` instead of `-> 0`
  broken-red-B2 bits                  B2's witness `b_ge_m -> 0` instead of `-> 1`.
                                      Vacuous IN PRINCIPLE: the negation of B2
                                      (b >= m and ~b_ge_m) contradicts the model,
                                      so every goal is implied (D-0053, for a root
                                      pruning's atom). Judged IN PRACTICE only when
                                      the checker's unit propagation does not see
                                      that contradiction: measured accepted with
                                      a's lower bound at 0 (w=10), refused with it
                                      at w//4 (w=12 and up). Report, do not rely
  control-noG   all                   the pruning line is a copy of R and the pin
                                      is dropped; Z and the conclusion are kept.
                                      Must be refused at the conclusion, or the
                                      conclusion does not depend on the pruning

Layout: <out>/w<w>/<arm>/<style>/{model.opb,proof.pbp,proof.<variant>.pbp}
"""

import argparse
import os
import sys

STYLES = ("rup", "pol")
ARMS = ("order", "bits")


def params(w):
    l = w // 4
    c = l + w // 2
    m = c - l + 1
    assert 1 <= l and l + 2 <= w and 2 <= m < w, "interior values only"
    return l, c, m


# ---------------------------------------------------------------- order arm


def order_opb(w, l, c, m):
    a_vals = range(l + 1, w + 1)  # a_ge_v exists for l < v <= w
    b_vals = range(1, w + 1)
    nrows = 2 + (w - l - 1) + (w - 1)
    lines = [f"* #variable= {(w - l) + w + 1} #constraint= {nrows}", "min: +1 z_ge_1 ;"]
    row = " ".join(f"-1 a_ge_{v}" for v in a_vals) + " " + " ".join(f"-1 b_ge_{v}" for v in b_vals)
    lines.append(f"@R {row} >= {-(c - l)} ;")
    lines.append(f"@T +1 z_ge_1 +1 b_ge_{m} >= 1 ;")
    for v in range(l + 1, w):
        lines.append(f"@la_{v} +1 ~a_ge_{v + 1} +1 a_ge_{v} >= 1 ;")
    for v in range(1, w):
        lines.append(f"@lb_{v} +1 ~b_ge_{v + 1} +1 b_ge_{v} >= 1 ;")
    return "\n".join(lines) + "\n", nrows


def order_pol(w, l, top):
    """R, weaken all of a, fold b's ladder to rung top-1, weaken b above top, s."""
    toks = ["@R"]
    toks += [f"a_ge_{v} w" for v in range(l + 1, w + 1)]
    for v in range(1, top):
        toks.append("@lb_%d +" % v if v == 1 else "@lb_%d %d * +" % (v, v))
    toks += [f"b_ge_{v} w" for v in range(top + 1, w + 1)]
    toks.append("s")
    return "@G pol " + " ".join(toks) + " ;"


def order_proof(w, l, m, nrows, style, variant=None):
    out = ["pseudo-Boolean proof version 3.0", f"f {nrows} ;"]
    if variant == "control-noG":
        out.append("@G pol @R ;")
    elif style == "rup":
        lit = f"b_ge_{m}" if variant == "broken" else f"~b_ge_{m}"
        out.append(f"@G rup +1 {lit} >= 1 ;")
    else:
        out.append(order_pol(w, l, top=m + 1 if variant == "broken" else m))
    if variant != "control-noG":
        out.append(f"@E e +1 ~b_ge_{m} >= 1 : @G ;")
    out.append("@Z pol @T @G + ;")
    out += tail()
    return "\n".join(out) + "\n"


# ----------------------------------------------------------------- bits arm


def bits_terms(x, n, neg=False, sign="+"):
    t = "~" if neg else ""
    return " ".join(f"{sign}{1 << i} {t}{x}_bit_{i}" for i in range(n))


def bits_opb(w, l, c, m):
    n = w.bit_length()
    lines = [f"* #variable= {2 * n + 1} #constraint= 6", "min: +1 z_bit_0 ;"]
    lines.append(f"@R {bits_terms('a', n, sign='-')} {bits_terms('b', n, sign='-')} >= {-c} ;")
    lines.append(f"@T +{m} z_bit_0 {bits_terms('b', n)} >= {m} ;")
    lines.append(f"@Alo {bits_terms('a', n)} >= {l} ;")
    lines.append(f"@Ahi {bits_terms('a', n, sign='-')} >= {-w} ;")
    lines.append(f"@Blo {bits_terms('b', n)} >= 0 ;")
    lines.append(f"@Bhi {bits_terms('b', n, sign='-')} >= {-w} ;")
    return "\n".join(lines) + "\n", 6, n


def bits_atom(n, m, flip1=False, flip2=False):
    """The red pair that mints [b >= m]: B1 `b_ge_m -> B >= m`, B2 `B >= m -> b_ge_m`."""
    full = (1 << n) - m
    w1 = "1" if flip1 else "0"
    w2 = "0" if flip2 else "1"
    return [
        f"@B1 red {bits_terms('b', n)} +{m} ~b_ge_{m} >= {m} : b_ge_{m} -> {w1} ;",
        f"@B2 red {bits_terms('b', n, neg=True)} +{full} b_ge_{m} >= {full} : b_ge_{m} -> {w2} ;",
    ]


def bits_proof(n, m, nrows, style, variant=None):
    out = ["pseudo-Boolean proof version 3.0", f"f {nrows} ;"]
    out += bits_atom(n, m, flip1=(variant == "broken-red-B1"), flip2=(variant == "broken-red-B2"))
    if variant == "control-noG":
        out.append("@G pol @R ;")
    elif style == "rup":
        lit = f"b_ge_{m}" if variant == "broken" else f"~b_ge_{m}"
        out.append(f"@G rup +1 {lit} >= 1 ;")
    else:
        defn = "@B2" if variant == "broken" else "@B1"
        out.append(f"@G pol @R @Alo + {defn} + s ;")
    if variant != "control-noG":
        out.append(f"@E e +1 ~b_ge_{m} >= 1 : @G ;")
    out.append(f"@Z pol @T @B2 + @G {(1 << n) - m} * + s ;")
    out += tail()
    return "\n".join(out) + "\n"


# ------------------------------------------------------------------- common


def tail():
    return ["output NONE ;", "conclusion BOUNDS 1 : @Z INF ;", "end pseudo-Boolean proof ;"]


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
        l, c, m = params(w)
        for arm in args.arms.split(","):
            if arm == "order":
                opb, nrows = order_opb(w, l, c, m)
                variants = ("broken", "control-noG")
            else:
                opb, nrows, n = bits_opb(w, l, c, m)
                variants = ("broken", "broken-red-B1", "broken-red-B2", "control-noG")
            for style in args.styles.split(","):
                d = os.path.join(args.out, f"w{w}", arm, style)
                ob = write(os.path.join(d, "model.opb"), opb)

                def proof(variant=None):
                    if arm == "order":
                        return order_proof(w, l, m, nrows, style, variant)
                    return bits_proof(n, m, nrows, style, variant)

                main_text = proof()
                pb = write(os.path.join(d, "proof.pbp"), main_text)
                for v in variants:
                    write(os.path.join(d, f"proof.{v}.pbp"), proof(v))
                atoms = 0 if arm == "order" else 1
                print(
                    f"{w}\t{arm}\t{style}\t{atoms}\t{top_level_lines(main_text)}\t{ob}\t{pb}\t"
                    f"{d}: model.opb proof.pbp " + " ".join(f"proof.{v}.pbp" for v in variants)
                )
                sys.stdout.flush()


if __name__ == "__main__":
    main()
