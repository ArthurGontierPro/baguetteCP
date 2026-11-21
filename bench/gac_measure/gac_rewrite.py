#!/usr/bin/env python3
r"""M4-T6b (D-0194): turn a Gecode-flattened .fzn into its GAC twin.

Every int_times / int_div / int_mod / int_abs whose non-result operands each have at
most CAP declared values (and none is a constant) is replaced by
    gecode_table_int([x, y, z], [tuples...])
over the tuples of the relation inside the declared domains, which Gecode propagates
domain consistently. Everything else (search annotations included) is unchanged, so
running fzn-gecode on the original and on the twin compares bounds against GAC on the
same model and the same search. Rounding is MiniZinc's (truncation toward zero,
remainder with the sign of the dividend), SPEC 2.1; division by zero has no tuple.

Usage: gac_rewrite.py in.fzn out.fzn [CAP]   (prints a one-line count on stderr)
"""
import re
import sys

CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 64
VAR_RE = re.compile(r"^var\s+(.+?)\s*:\s*(\w+)")
CON_RE = re.compile(r"^constraint\s+int_(times|div|mod|abs)\(([^)]*)\)(.*);\s*$")


def parse_dom(s):
    s = s.strip()
    m = re.fullmatch(r"(-?\d+)\.\.(-?\d+)", s)
    if m:
        return list(range(int(m.group(1)), int(m.group(2)) + 1)) \
            if int(m.group(2)) - int(m.group(1)) < 10**6 else None
    m = re.fullmatch(r"\{([^}]*)\}", s)
    if m:
        return sorted(int(v) for v in m.group(1).split(",") if v.strip())
    return None


def tdiv(a, b):
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b > 0) else -q


def tmod(a, b):
    return a - b * tdiv(a, b)


F = {"times": lambda a, b: a * b,
     "div": lambda a, b: None if b == 0 else tdiv(a, b),
     "mod": lambda a, b: None if b == 0 else tmod(a, b)}


def main():
    src, dst = sys.argv[1], sys.argv[2]
    doms = {}
    n = dict(seen=0, tab=0, tuples=0)
    with open(src) as fi, open(dst, "w") as fo:
        for line in fi:
            if line.startswith("var "):
                m = VAR_RE.match(line)
                if m:
                    doms[m.group(2)] = parse_dom(m.group(1))
                fo.write(line)
                continue
            m = CON_RE.match(line) if line.startswith("constraint int_") else None
            if not m:
                fo.write(line)
                continue
            n["seen"] += 1
            kind = m.group(1)
            args = [a.strip() for a in m.group(2).split(",")]
            if any(re.fullmatch(r"-?\d+", a) for a in args[:-1]):
                fo.write(line)
                continue
            ds = [[int(a)] if re.fullmatch(r"-?\d+", a) else doms.get(a) for a in args]
            if any(d is None for d in ds) or any(len(d) > CAP for d in ds[:-1]):
                fo.write(line)
                continue
            zs = set(ds[-1])
            if kind == "abs":
                tup = [(a, abs(a)) for a in ds[0] if abs(a) in zs]
            else:
                f = F[kind]
                # an ALIASED operand (x*x) ranges once: (a, b, ab) with b != a would
                # support x = a through a value x cannot take at the same time
                same = args[0] == args[1]
                tup = [(a, b, f(a, b)) for a in ds[0] for b in ds[1] if not same or a == b]
                tup = [t for t in tup if t[2] is not None and t[2] in zs]
            if not tup:
                fo.write("constraint bool_eq(true, false);\n")
            else:
                flat = ",".join(str(v) for t in tup for v in t)
                fo.write(f"constraint gecode_table_int([{','.join(args)}],[{flat}]);\n")
            n["tab"] += 1
            n["tuples"] += len(tup)
    print(f"arith={n['seen']} tabulated={n['tab']} tuples={n['tuples']}", file=sys.stderr)


if __name__ == "__main__":
    main()
