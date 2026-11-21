#!/usr/bin/env python3
r"""M4-T6b (D-0194): census of the arithmetic builtins a flattened instance posts, and a
ROOT probe of what GAC would prune beyond bounds consistency on each one, from the
DECLARED domains, constraint by constraint, in isolation.

NOT part of the solver. Input: baguette-flattened .fzn files (the ones the Challenge
series ran). For every int_times(x,y,z), int_div(x,y,q), int_abs(x,z) it reads the
declared domains (an int literal is a fixed domain) and classifies the constraint:

  fixed    an operand is a constant: the relation is linear in what is left
  small    every non-result operand has <= CAP values (default 64): what D-0184's
           option B would tabulate
  wide     anything else

For a `small` constraint it computes, on the declared domains alone:
  GAC      the supported values of every variable (enumeration over the operands)
  BZ       the fixpoint of bounds(Z) consistency on the same constraint (each bound
           must have a support inside the HULLS of the others). This is an UPPER
           bound on what D-0060's rows do (they are bounds consistent only once the
           sign of x is settled, arith.ml's header), so `extra = |BZ \ GAC|` is a
           LOWER bound on what GAC would add at the root over baguette's arith.
A constraint is `gain` when extra > 0, and `gain_ops` when GAC removes a value of an
OPERAND (x or y) that BZ keeps: an extra value of the result z alone is a hole in a
product, which cuts search only if another constraint reads z's interior.

Output: one TSV line per instance:
  id family n_times n_div n_abs fixed small wide small_gain small_gain_ops extra_values
  extra_ops small_cells(sum |Dx||Dy| over small) small_bool(small with a two-valued
  operand, typically a 0..1 indicator times an integer)
"""
import re
import sys

CAP = 64
VAR_RE = re.compile(r"^var\s+(.+?)\s*:\s*(\w+)")
CON_RE = re.compile(r"^constraint\s+int_(times|div|abs)\(([^)]*)\)")


def parse_dom(s):
    s = s.strip()
    m = re.fullmatch(r"(-?\d+)\.\.(-?\d+)", s)
    if m:
        lo, hi = int(m.group(1)), int(m.group(2))
        return ("r", lo, hi)
    m = re.fullmatch(r"\{([^}]*)\}", s)
    if m:
        vals = sorted(int(v) for v in m.group(1).split(",") if v.strip())
        return ("s", vals)
    if s == "bool":
        return ("r", 0, 1)
    return None  # var int


def size(d):
    if d is None:
        return 10**18
    return d[2] - d[1] + 1 if d[0] == "r" else len(d[1])


def values(d):
    return list(range(d[1], d[2] + 1)) if d[0] == "r" else d[1]


def tdiv(a, b):
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b > 0) else -q


def rel(kind):
    if kind == "times":
        return lambda a, b: a * b
    if kind == "div":
        return lambda a, b: None if b == 0 else tdiv(a, b)
    return None


def gac_and_bz(kind, doms, aliased=False):
    """doms: list of sorted value lists (operands then result). Returns
    (gac_sets, bz_sets) as python sets. `aliased`: x and y are one variable (x*x), so a
    tuple must have a == b for GAC; BZ stays the hull reasoning over two operands, which
    is what D-0060's rows do with an aliased operand."""
    if kind == "abs":
        X, Z = doms
        zs = set(Z)
        gx = {a for a in X if abs(a) in zs}
        gz = {abs(a) for a in gx}
        tuples_fn = None
        # bounds(Z) on |x| = z over hulls, to fixpoint
        sx, sz = list(X), list(Z)
        changed = True
        while changed and sx and sz:
            changed = False
            zlo, zhi = sz[0], sz[-1]
            xlo, xhi = sx[0], sx[-1]
            # support of an x bound: |x| within [zlo, zhi]
            while sx and not (zlo <= abs(sx[0]) <= zhi):
                sx.pop(0); changed = True
            while sx and not (zlo <= abs(sx[-1]) <= zhi):
                sx.pop(); changed = True
            if not sx:
                break
            xlo, xhi = sx[0], sx[-1]
            amin = 0 if xlo <= 0 <= xhi else min(abs(xlo), abs(xhi))
            amax = max(abs(xlo), abs(xhi))
            while sz and not (amin <= sz[0] <= amax):
                sz.pop(0); changed = True
            while sz and not (amin <= sz[-1] <= amax):
                sz.pop(); changed = True
        return [gx, gz], [set(sx), set(sz)]
    f = rel(kind)
    X, Y, Z = doms
    zs = set(Z)
    tup = [(a, b, f(a, b)) for a in X for b in Y if not aliased or a == b]
    tup = [t for t in tup if t[2] is not None and t[2] in zs]
    gac = [{t[0] for t in tup}, {t[1] for t in tup}, {t[2] for t in tup}]
    # bounds(Z) consistency to fixpoint: a bound of one variable is kept iff some tuple
    # with that value has the other components inside the other variables' HULLS.
    cur = [list(X), list(Y), list(Z)]
    changed = True
    while changed and all(cur):
        changed = False
        hull = [(c[0], c[-1]) for c in cur]
        prods = None
        for i in range(3):
            for end in (0, -1):
                while cur[i]:
                    v = cur[i][end]
                    ok = False
                    j, k = [t for t in range(3) if t != i]
                    # enumerate the other operand over its hull (integers), solving the third
                    if i == 2:
                        if prods is None:
                            prods = {f(a, b) for a in range(hull[0][0], hull[0][1] + 1)
                                     for b in range(hull[1][0], hull[1][1] + 1)}
                        ok = v in prods
                    else:
                        o = 1 - i
                        for w in range(hull[o][0], hull[o][1] + 1):
                            a, b = (v, w) if i == 0 else (w, v)
                            r = f(a, b)
                            if r is not None and hull[2][0] <= r <= hull[2][1]:
                                ok = True; break
                    if ok:
                        break
                    cur[i].pop(end); changed = True
                if not cur[i]:
                    break
            if not all(cur):
                break
        hull = None
    return gac, [set(c) for c in cur]


def scan(path):
    doms = {}
    out = dict(times=0, div=0, abs=0, fixed=0, small=0, wide=0, gain=0, gain_ops=0, extra=0, extra_ops=0, cells=0, small_bool=0)
    with open(path, errors="replace") as fh:
        for line in fh:
            if line.startswith("var "):
                m = VAR_RE.match(line)
                if m:
                    doms[m.group(2)] = parse_dom(m.group(1))
                continue
            if not line.startswith("constraint int_"):
                continue
            m = CON_RE.match(line)
            if not m:
                continue
            kind = m.group(1)
            out[kind] += 1
            args = [a.strip() for a in m.group(2).split(",")]
            ds = []
            for a in args:
                if re.fullmatch(r"-?\d+", a):
                    ds.append(("r", int(a), int(a)))
                else:
                    ds.append(doms.get(a))
            ops = ds[:-1]
            if any(d is not None and size(d) == 1 for d in ops):
                out["fixed"] += 1
                continue
            if any(size(d) > CAP for d in ops) or any(d is None for d in ds):
                out["wide"] += 1
                continue
            out["small"] += 1
            if any(size(d) == 2 for d in ops):
                out["small_bool"] += 1
            vals = [values(d) for d in ds]
            out["cells"] += len(vals[0]) * (len(vals[1]) if kind != "abs" else 1)
            gac, bz = gac_and_bz(kind, vals, kind != "abs" and args[0] == args[1])
            eo = sum(len(b - g) for g, b in zip(gac[:-1], bz[:-1]))
            er = len(bz[-1] - gac[-1])
            if eo + er:
                out["gain"] += 1
            if eo:
                out["gain_ops"] += 1
            out["extra"] += eo + er
            out["extra_ops"] += eo
    return out


def main():
    print("id\tfamily\tn_times\tn_div\tn_abs\tfixed\tsmall\twide\tsmall_gain\tsmall_gain_ops\textra_values\textra_ops\tsmall_cells\tsmall_bool")
    for p in sys.argv[1:]:
        ident = p.rsplit("/", 1)[-1].replace(".baguette.fzn", "")
        fam = ident.split("_")[1] if "_" in ident else ident
        o = scan(p)
        if o["times"] + o["div"] + o["abs"] == 0:
            continue
        print("\t".join(str(x) for x in [ident, fam, o["times"], o["div"], o["abs"], o["fixed"],
                                         o["small"], o["wide"], o["gain"], o["gain_ops"], o["extra"],
                                         o["extra_ops"], o["cells"], o["small_bool"]]),
              flush=True)


if __name__ == "__main__":
    main()
