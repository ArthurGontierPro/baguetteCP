#!/usr/bin/env python3
"""diag_pol.py -- which `pol` operator is quadratic on VeriPB 3.0.2 (M8-bits-encoding-T0).

run.sh measured the order arm's justification at 4.1 s for w = 10^5 and 383 s for
w = 10^6 while the same step as `rup` took 0.2 s and 2.6 s. The line has three
kinds of operator over a Theta(w)-term accumulator: Theta(w) weakenings (`x w`),
Theta(w) ladder-rung additions with a growing multiplier (`@lb_v v * +`), and one
`s`. This writes one proof per operator kind, over the order arm's model.opb of a
given width (reuses out/<run>/w<w>/order/pol/model.opb), so the cost can be
attributed. Each proof is legal, concludes NONE, and is only there to be timed.

  weaken   `pol @R x w ...` over every literal of a and b         (2w - l ops)
  sum      `pol @R @lb_1 + @lb_2 + ... @lb_{m-1} +`               (m - 1 plain adds)
  fold     `pol @R @lb_1 + @lb_2 2 * + ... @lb_{m-1} (m-1) * +`   (m - 1 mult-adds)
  foldT    the same fold started from the 2-term row @T instead of the
           Theta(w)-term @R: same number of ops, accumulator Theta(m) instead
           of Theta(w) -- separates "cost per op" from "cost per accumulator term"

usage: diag_pol.py <model-dir> <w> <variant>   writes <model-dir>/diag-<variant>.pbp
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # `python3 -I` adds nothing
from gen import params  # noqa: E402


def main():
    d, w, variant = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    l, c, m = params(w)
    nrows = 2 + (w - l - 1) + (w - 1)
    toks = ["@T" if variant == "foldT" else "@R"]
    if variant == "weaken":
        toks += [f"a_ge_{v} w" for v in range(l + 1, w + 1)]
        toks += [f"b_ge_{v} w" for v in range(1, w + 1)]
    elif variant == "sum":
        toks += [f"@lb_{v} +" for v in range(1, m)]
    elif variant in ("fold", "foldT"):
        for v in range(1, m):
            toks.append("@lb_%d +" % v if v == 1 else "@lb_%d %d * +" % (v, v))
    else:
        sys.exit("variant: weaken | sum | fold | foldT")
    text = "\n".join(
        [
            "pseudo-Boolean proof version 3.0",
            f"f {nrows} ;",
            "@G pol " + " ".join(toks) + " ;",
            "output NONE ;",
            "conclusion NONE ;",
            "end pseudo-Boolean proof ;",
        ]
    ) + "\n"
    path = f"{d}/diag-{variant}.pbp"
    with open(path, "w") as f:
        f.write(text)
    print(path, len(text.encode()), len(toks) - 1)


if __name__ == "__main__":
    main()
