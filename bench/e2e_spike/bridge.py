#!/usr/bin/env python3
"""M14-e2e-verification-T1 spike: re-derive baguette's .opb rows from cake_pb_cp's .opb.

Usage: bridge.py CAKE.opb BAGUETTE.opb BAGUETTE.pbp > BRIDGED.pbp

Only the order arm, and only what the two demo models need: every baguette variable is an
integer `X` whose cake encoding is `i[X][b*]` (+ `i[X][sign]`) with rows `@i[X][lb]`/`@i[X][ub]`.
The prefix, per variable X over [l, u], with B = cake's bit sum and S = sum_{l<v<=u} X_ge_v:

  atoms   red  B + v ~X_ge_v >= v          : X_ge_v -> 0   (X_ge_v -> B >= v)
          red -B + K X_ge_v  >= 1 - v      : X_ge_v -> 1   (B >= v -> X_ge_v)
  T1, T2  sum_{w<=v} ~X_ge_w >= 0 and sum_{w>=v} X_ge_w >= 0, running rows, one pol each
  E1      B - S >= l     by induction on v, one pol per value citing T1 (reified halves, divide)
  E2      S - B >= -l    by induction downwards, citing T2, idem
  ladder  ~X_ge_(v+1) + X_ge_v >= 1, one pol each

Then every cake model row is SUBSTITUTED (B -> l + S, adding E1/E2 scaled by the row's
coefficient) into a row over baguette's atoms, and every baguette .opb row is pinned to its
own label: `ia` when a substituted row implies it syntactically, `rup` otherwise. Baguette's
proof follows unchanged, with only its `f N` replaced by cake's row count. Every line is O(1)
citations, so the prefix is O(w) text per variable (Theta(w) pol lines over Theta(w)-literal rows,
so the CHECK is still Theta(w^2) arithmetic). Atom names follow PROOF-FORMAT section 3
(`x_ge_m1` for -1). D-0174 has the derivation and the measurements.
"""
import re
import sys

TERM = re.compile(r"([+-]?\d+)\s+(~?[^\s;]+)")


def parse_row(line):
    line = line.strip()
    if not line or line.startswith("*"):
        return None
    label = None
    if line.startswith("@"):
        label, line = line.split(None, 1)
        label = label[1:]
    body = line.rstrip(";").strip()
    for op in (">=", "<=", "="):
        if op in body:
            lhs, rhs = body.split(op)
            break
    terms = [(int(c), v) for c, v in TERM.findall(lhs)]
    return label, terms, op, int(rhs)


def to_var_form(terms, op, rhs):
    """sum c*lit OP rhs  ->  dict var->coef, degree, as a >= row (sum c x >= d)."""
    if op == "<=":
        terms = [(-c, v) for c, v in terms]
        rhs = -rhs
    coefs, d = {}, rhs
    for c, lit in terms:
        if lit.startswith("~"):
            var = lit[1:]
            coefs[var] = coefs.get(var, 0) - c
            d -= c
        else:
            coefs[lit] = coefs.get(lit, 0) + c
    return {k: v for k, v in coefs.items() if v != 0}, d


def pv(s):
    return -int(s[1:]) if s.startswith("m") else int(s)


def vn(v):
    return f"m{-v}" if v < 0 else str(v)


def fmt(coefs, d):
    parts = " ".join(f"{'+' if c > 0 else ''}{c} {v}" for v, c in coefs.items())
    return f"{parts} >= {d} ;"


def main(cake_opb, bag_opb, bag_pbp):
    cake = [r for r in (parse_row(l) for l in open(cake_opb)) if r]
    bag = [r for r in (parse_row(l) for l in open(bag_opb)) if r]
    out = []
    emit = out.append

    # integer variables and their bit sums, from cake's bound rows
    ivars = {}
    for label, terms, op, rhs in cake:
        m = re.fullmatch(r"i\[(.+)\]\[(lb|ub)\]", label or "")
        if m:
            ivars.setdefault(m.group(1), {})[m.group(2)] = rhs
            ivars[m.group(1)]["bits"] = {v: c for c, v in terms}
    for x, info in ivars.items():
        l, u, bits = info["lb"], info["ub"], info["bits"]
        bmin = sum(c for c in bits.values() if c < 0)
        bmax = sum(c for c in bits.values() if c > 0)
        S = [f"{x}_ge_{vn(v)}" for v in range(l + 1, u + 1)]
        bsum = " ".join(f"{'+' if c > 0 else ''}{c} {b}" for b, c in bits.items())
        nbsum = " ".join(f"{'+' if -c > 0 else ''}{-c} {b}" for b, c in bits.items())
        emit(f"% bridge: {x} in [{l},{u}], B = {bsum}")
        for v in range(l + 1, u + 1):
            a = f"{x}_ge_{vn(v)}"
            M = v - bmin  # B + M ~a >= v holds whenever a is false
            K = bmax - v + 1  # -B + K a >= 1 - v holds whenever a is true
            emit(f"@A1[{a}] red {bsum} +{M} ~{a} >= {v} : {a} -> 0 ;")
            emit(f"@A2[{a}] red {nbsum} +{K} {a} >= {1 - v} : {a} -> 1 ;")
        # E1: B - S_{<=v} >= l, upwards from the lb row
        prev = f"@i[{x}][lb]"
        for i, v in enumerate(range(l + 1, u + 1)):
            a = f"{x}_ge_{vn(v)}"
            M = v - bmin
            # T1_v = sum_{w<=v} ~w >= 0, a running row cited in O(1) text (the literal
            # sum would make the prefix Theta(w^2) bytes); H1 = prev, H2 = A1 + T1_v
            emit(f"@T1[{a}] pol {'@T1[' + S[i - 1] + '] ' if i else ''}~{a}{' +' if i else ''} ;")
            emit(f"@E1[{a}] pol {prev} {M} * @A1[{a}] + @T1[{a}] + {M + 1} d ;")
            prev = f"@E1[{a}]"
        e1 = prev
        # E2: B - S_{>v} <= v, downwards from the ub row
        prev = f"@i[{x}][ub]"
        for v in range(u, l, -1):
            a = f"{x}_ge_{vn(v)}"
            K = bmax - v + 1
            j = v - l - 1
            emit(f"@T2[{a}] pol {'@T2[' + S[j + 1] + '] ' if j + 1 < len(S) else ''}{a}{' +' if j + 1 < len(S) else ''} ;")
            emit(f"@E2[{a}] pol {prev} {K} * @A2[{a}] + @T2[{a}] + {K + 1} d ;")
            prev = f"@E2[{a}]"
        e2 = prev
        info.update(l=l, S=S, e1=e1, e2=e2)
        for v in range(l + 1, u):
            hi, lo = f"{x}_ge_{vn(v + 1)}", f"{x}_ge_{vn(v)}"
            emit(f"@L[{hi}] pol @A1[{hi}] @A2[{lo}] + s {(bmax - bmin) + 2} d ;")

    # substitute every cake model row B -> l + S
    subst = []
    for label, terms, op, rhs in cake:
        if label.startswith("i["):
            continue
        coefs, d = to_var_form(terms, op, rhs)
        rpn, scale = [f"@{label}"], {}
        for x, info in ivars.items():
            c = info["bits"]
            first = next(iter(c))
            if first in coefs:
                k = coefs[first] // c[first]
                scale[x] = k
        for x, k in scale.items():
            # k*B appears; add k*(S - B >= -l) if k > 0 (E2), |k|*(B - S >= l) if k < 0 (E1)
            info = ivars[x]
            rpn += [info["e2"] if k > 0 else info["e1"], str(abs(k)), "*", "+"]
        lab = f"S[{label}]"
        emit(f"@{lab} pol {' '.join(rpn)} ;")
        new = dict(coefs)
        for x, k in scale.items():
            for b in ivars[x]["bits"]:
                new.pop(b, None)
            for s in ivars[x]["S"]:
                new[s] = new.get(s, 0) + k
            d -= k * ivars[x]["l"]
        subst.append((lab, {k: v for k, v in new.items() if v}, d))

    # pin every baguette .opb row to its own label
    for label, terms, op, rhs in bag:
        coefs, d = to_var_form(terms, op, rhs)
        line = " ".join(f"{'+' if c > 0 else ''}{c} {v}" for c, v in terms) + f" {op} {rhs} ;"
        m = re.fullmatch(r"\+1 ~(\S+)_ge_(m?\d+) \+1 (\S+)_ge_(m?\d+) >= 1 ;", line)
        if m and m.group(1) == m.group(3) and pv(m.group(2)) == pv(m.group(4)) + 1:
            emit(f"@{label} ia {line[:-2]} : @L[{m.group(1)}_ge_{m.group(2)}] ;")
            continue
        hit = next((lab for lab, c2, d2 in subst if c2 == coefs and d2 >= d), None)
        if hit:
            emit(f"@{label} ia {line[:-2]} : @{hit} ;")
        else:
            emit(f"@{label} rup {line}")

    lines = open(bag_pbp).read().splitlines()
    assert lines[0].startswith("pseudo-Boolean proof version")
    assert lines[1].startswith("f ")
    print(lines[0])
    print(f"f {len(cake)} ;")
    print("\n".join(out))
    print("\n".join(lines[2:]))


if __name__ == "__main__":
    main(*sys.argv[1:4])
