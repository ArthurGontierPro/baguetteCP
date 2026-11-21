#!/usr/bin/env python3
r"""M4-T6b (D-0194): the GAC twin of a BAGUETTE-flattened .fzn, for a node count inside
baguette itself (learning, its own search and its own proof included).

Every int_times(x,y,z) / int_div(x,y,q) / int_abs(x,z) whose operands are variables with
at most CAP declared values each is replaced by the same relation as a DFA through
`baguette_regular` (lib/core/prop/regular.ml, DOMAIN consistent over its letters), over
the word [x, y, z] (or [x, z] for x*x and for abs, so no letter is aliased):

    state 1 --x=a--> A_a --y=b--> C_c (c = f(a,b) in Dz) --z=c--> ACCEPT

Q = 1 + |Dx| + |{c}| + 1 states, alphabet the hull of the letters' declared domains. A
constraint is kept as it is when Q * S exceeds TABLE_CAP (the transition table is written
into the .fzn). The regular rows ARE the relation, so the twin solves the same problem and
its proof is still checked; it is a MEASUREMENT device, not D-0184's option B (whose
proof would be the tabulation of D-0184 section 2, not a DFA).

Usage: bag_twin.py in.fzn out.fzn [CAP [TABLE_CAP]]   (one count line on stderr)
"""
import re
import sys

CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 64
TABLE_CAP = int(sys.argv[4]) if len(sys.argv) > 4 else 400000
VAR_RE = re.compile(r"^var\s+(.+?)\s*:\s*(\w+)")
CON_RE = re.compile(r"^constraint\s+int_(times|div|abs)\(([^)]*)\)(.*);\s*$")


def parse_dom(s):
    s = s.strip()
    m = re.fullmatch(r"(-?\d+)\.\.(-?\d+)", s)
    if m:
        lo, hi = int(m.group(1)), int(m.group(2))
        return list(range(lo, hi + 1)) if hi - lo < 10**6 else None
    m = re.fullmatch(r"\{([^}]*)\}", s)
    if m:
        return sorted(int(v) for v in m.group(1).split(",") if v.strip())
    if s == "bool":
        return [0, 1]
    return None


def tdiv(a, b):
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b > 0) else -q


def dfa(kind, args, ds):
    """Return (letters, Q, smin, delta list, final) or None."""
    zs = set(ds[-1])
    if kind == "abs" or (kind == "times" and args[0] == args[1]):
        X = ds[0]
        f = (lambda a: abs(a)) if kind == "abs" else (lambda a: a * a)
        pairs = [(a, f(a)) for a in X if f(a) in zs]
        letters = [args[0], args[-1]]
        cs = sorted({c for _, c in pairs})
        # 1 --x=a--> C_c --z=c--> ACC
        cid = {c: 2 + i for i, c in enumerate(cs)}
        Q = 2 + len(cs)
        acc = Q
        trans = [(1, a, cid[c]) for a, c in pairs] + [(cid[c], c, acc) for c in cs]
        lets = ds[0] + ds[-1]
    else:
        X, Y = ds[0], ds[1]
        if kind == "times":
            f = lambda a, b: a * b
        else:
            f = lambda a, b: None if b == 0 else tdiv(a, b)
        tup = [(a, b, f(a, b)) for a in X for b in Y]
        tup = [t for t in tup if t[2] is not None and t[2] in zs]
        letters = list(args)
        xs = sorted({t[0] for t in tup})
        cs = sorted({t[2] for t in tup})
        aid = {a: 2 + i for i, a in enumerate(xs)}
        cid = {c: 2 + len(xs) + i for i, c in enumerate(cs)}
        Q = 2 + len(xs) + len(cs)
        acc = Q
        trans = [(1, a, aid[a]) for a in xs] + [(aid[a], b, cid[c]) for a, b, c in tup] \
            + [(cid[c], c, acc) for c in cs]
        lets = ds[0] + ds[1] + ds[2]
    smin, smax = min(lets), max(lets)
    S = smax - smin + 1
    if Q * S > TABLE_CAP:
        return None
    d = [0] * (Q * S)
    for q, v, q2 in trans:
        d[(q - 1) * S + (v - smin)] = q2
    return letters, Q, smin, d, acc


def main():
    src, dst = sys.argv[1], sys.argv[2]
    doms = {}
    n = dict(arith=0, twin=0, capped=0, flags=0)
    newvars, body = [], []
    head_done = False
    with open(src) as fi:
        head = []
        for line in fi:
            if not head_done and not line.startswith("constraint") and not line.startswith("solve"):
                head.append(line)
                if line.startswith("var "):
                    m = VAR_RE.match(line)
                    if m:
                        doms[m.group(2)] = parse_dom(m.group(1))
                continue
            head_done = True
            m = CON_RE.match(line) if line.startswith("constraint int_") else None
            if not m:
                body.append(line)
                continue
            n["arith"] += 1
            kind = m.group(1)
            args = [a.strip() for a in m.group(2).split(",")]
            if any(re.fullmatch(r"-?\d+", a) for a in args):
                body.append(line)
                continue
            ds = [doms.get(a) for a in args]
            if any(d is None for d in ds) or any(len(d) > CAP for d in ds[:-1]):
                body.append(line)
                continue
            r = dfa(kind, args, ds)
            if r is None:
                n["capped"] += 1
                body.append(line)
                continue
            letters, Q, smin, d, acc = r
            k = n["twin"]
            nf = (len(letters) + 1) * Q
            flags = [f"GACS_{k}_{j}" for j in range(nf)]
            newvars.extend(f"var bool: {v};\n" for v in flags)
            body.append(f"constraint baguette_regular([{','.join(letters)}],{Q},{smin},"
                        f"[{','.join(map(str, d))}],1,[{acc}],[{','.join(flags)}]);\n")
            n["twin"] += 1
            n["flags"] += nf
    with open(dst, "w") as fo:
        fo.writelines(head)
        fo.writelines(newvars)
        fo.writelines(body)
    print(f"arith={n['arith']} twin={n['twin']} capped={n['capped']} flags={n['flags']}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
