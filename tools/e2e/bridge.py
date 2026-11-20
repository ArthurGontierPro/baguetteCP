#!/usr/bin/env python3
"""Re-derive baguette's .opb from cake_pb_cp's, at the head of baguette's proof (M14-e2e-verification).

Usage: python3 -I bridge.py CAKE.opb NAMES BAGUETTE.opb BAGUETTE.pbp > BRIDGED.pbp

CAKE.opb is what the verified encoder wrote for MODEL.scp; NAMES is the translator's
`SCP_NAME FLATZINC_NAME` table (tools/e2e/fzn2scp.py); BAGUETTE.opb/.pbp is baguette's own
run on MODEL.fzn, order arm. The output is a proof over CAKE.opb: a prefix that derives every
row of BAGUETTE.opb under its own label, then baguette's proof unchanged but for its `f N`.

This script is UNTRUSTED. If it writes a wrong line, the checker refuses it; nothing it does
can make a wrong answer verify, because the proof is checked against CAKE.opb, which the
verified encoder wrote. Its only obligation is to be complete on the covered families.

The prefix (D-0174 section 4), per integer X over [l, u], B = cake's bit sum of X, x_ge_v
baguette's order atoms (PROOF-FORMAT section 3), S = sum_{l<v<=u} x_ge_v:

  atoms   @A1  red  B + M ~x_ge_v >= v      : x_ge_v -> 0     (x_ge_v -> B >= v)
          @A2  red -B + K x_ge_v  >= 1 - v  : x_ge_v -> 1     (B >= v -> x_ge_v)
  halves  @E1  B - S >= l, upwards from @i[X][lb], one pol per value (running row @T1)
          @E2  S - B >= -l, downwards from @i[X][ub], idem (@T2)
  ladder  @L   ~x_ge_(v+1) + x_ge_v >= 1, one pol each

Then every cake row is SUBSTITUTED (B -> l + S: the row plus k * @E2, or |k| * @E1, k the
row's coefficient on B), giving @S[...] over baguette's atoms and cake's own auxiliaries.

Disequality selectors (D-0176). baguette's `int_ne`/`int_lin_ne` (and all_different's
constant or repeated pairs) carry a fresh `_neN_ge_1` that cake's file does not have; cake
carries its own flag (`b[c][ne]`, `x[c][i_j]`) for the same two halves. When a baguette row
equals a substituted cake row up to that one literal, the selector is DEFINED as the flag
by a red pair, `~s + F >= 1` and `s + ~F >= 1`, both with witness `s -> F` (s is fresh, so
the pair is a renaming), and the row is the cake row with F swapped for s by one pol.

Pins, in this order: a ladder row is `ia` against its @L; a row a substituted cake row
implies with the same coefficients is `ia` against it; a selector row is `ia` against its
swapped row; anything else is `rup` (all_different's per-value clauses close by unit
propagation over the substituted pair rows and their flags; a hole's clause over cake's
`in` rows and its `i[X][ge/eq]` atoms).
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
    else:
        raise SystemExit(f"bridge: cannot read row {line!r}")
    if op == "=":
        raise SystemExit(f"bridge: an equality row {label} (not produced by either side today)")
    terms = [(int(c), v) for c, v in TERM.findall(lhs)]
    return label, terms, op, int(rhs)


def var_form(terms, op, rhs):
    """sum c*lit OP rhs  ->  ({var: coef}, d) meaning sum coef*var >= d."""
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


def lit_form(coefs, d):
    """({var: coef}, d) -> ({lit: coef > 0}, d'), the normal form two rows are compared in."""
    lits = {}
    for v, c in coefs.items():
        if c > 0:
            lits[v] = c
        else:
            lits["~" + v] = -c
            d += -c
    return lits, d


def neg(lit):
    return lit[1:] if lit.startswith("~") else "~" + lit


def vn(v):
    return f"m{-v}" if v < 0 else str(v)


def pv(s):
    return -int(s[1:]) if s.startswith("m") else int(s)


def row_text(terms, op, rhs):
    return " ".join(f"{'+' if c >= 0 else ''}{c} {v}" for c, v in terms) + f" {op} {rhs}"


def main(cake_opb, names_file, bag_opb, bag_pbp):
    cake = [r for r in (parse_row(l) for l in open(cake_opb)) if r]
    bag_lines = open(bag_opb).read().splitlines()
    bag = [r for r in (parse_row(l) for l in bag_lines) if r]
    # baguette's own renaming of FlatZinc identifiers (`* name q[1] -> q_1_`)
    sanit = {}
    for l in bag_lines:
        m = re.fullmatch(r"\* name (\S+) -> (\S+)", l.strip())
        if m:
            sanit[m.group(1)] = m.group(2)
    fzn_of = dict(l.split() for l in open(names_file) if l.strip())
    out = []
    emit = out.append

    # integer variables, their bit sums, and baguette's name for each
    ivars = {}
    for label, terms, op, rhs in cake:
        m = re.fullmatch(r"i\[(.+)\]\[(lb|ub)\]", label or "")
        if m:
            info = ivars.setdefault(m.group(1), {})
            info[m.group(2)] = rhs
            info["bits"] = {v: c for c, v in terms}
    atoms = set()
    for X, info in ivars.items():
        fz = fzn_of.get(X)
        if fz is None:
            raise SystemExit(f"bridge: cake variable {X} is not in the names table")
        x = sanit.get(fz, fz)
        l, u, bits = info["lb"], info["ub"], info["bits"]
        bmin = sum(c for c in bits.values() if c < 0)
        bmax = sum(c for c in bits.values() if c > 0)
        S = [f"{x}_ge_{vn(v)}" for v in range(l + 1, u + 1)]
        atoms.update(S)
        bsum = " ".join(f"{'+' if c > 0 else ''}{c} {b}" for b, c in bits.items())
        nbsum = " ".join(f"{'+' if -c > 0 else ''}{-c} {b}" for b, c in bits.items())
        emit(f"% bridge: {X} is baguette's {x}, in [{l},{u}]")
        for v in range(l + 1, u + 1):
            a = f"{x}_ge_{vn(v)}"
            M = v - bmin   # B + M ~a >= v holds whenever a is false
            K = bmax - v + 1   # -B + K a >= 1 - v holds whenever a is true
            emit(f"@A1[{a}] red {bsum} +{M} ~{a} >= {v} : {a} -> 0 ;")
            emit(f"@A2[{a}] red {nbsum} +{K} {a} >= {1 - v} : {a} -> 1 ;")
        prev = f"@i[{X}][lb]"
        for i, v in enumerate(range(l + 1, u + 1)):
            a = f"{x}_ge_{vn(v)}"
            M = v - bmin
            # running row T1_v = sum_{w<=v} ~x_ge_w >= 0, cited in O(1) text; E1_v is the
            # previous half (x_ge_v false) and A1 + T1_v (x_ge_v true), divided
            emit(f"@T1[{a}] pol {'@T1[' + S[i - 1] + '] ' if i else ''}~{a}{' +' if i else ''} ;")
            emit(f"@E1[{a}] pol {prev} {M} * @A1[{a}] + @T1[{a}] + {M + 1} d ;")
            prev = f"@E1[{a}]"
        e1 = prev
        prev = f"@i[{X}][ub]"
        for v in range(u, l, -1):
            a = f"{x}_ge_{vn(v)}"
            K = bmax - v + 1
            j = v - l - 1
            more = j + 1 < len(S)
            emit(f"@T2[{a}] pol {'@T2[' + S[j + 1] + '] ' if more else ''}{a}{' +' if more else ''} ;")
            emit(f"@E2[{a}] pol {prev} {K} * @A2[{a}] + @T2[{a}] + {K + 1} d ;")
            prev = f"@E2[{a}]"
        e2 = prev
        info.update(l=l, S=S, e1=e1, e2=e2, x=x)
        for v in range(l + 1, u):
            hi, lo = f"{x}_ge_{vn(v + 1)}", f"{x}_ge_{vn(v)}"
            emit(f"@L[{hi}] pol @A1[{hi}] @A2[{lo}] + s {(bmax - bmin) + 2} d ;")
    owner = {b: X for X, info in ivars.items() for b in info["bits"]}

    # substitute every cake model row, B -> l + S
    subst = []   # (label to cite, {var: coef}, d)
    for label, terms, op, rhs in cake:
        if re.fullmatch(r"i\[.+\]\[(lb|ub)\]", label):
            continue
        coefs, d = var_form(terms, op, rhs)
        scale = {}
        for b, c in coefs.items():
            if b in owner:
                X = owner[b]
                k, r = divmod(c, ivars[X]["bits"][b])
                if r or scale.setdefault(X, k) != k:
                    raise SystemExit(f"bridge: row {label} is not a multiple of {X}'s bit sum")
        if not scale:
            subst.append((f"@{label}", coefs, d))
            continue
        rpn = [f"@{label}"]
        new = dict(coefs)
        for X, k in scale.items():
            info = ivars[X]
            if set(info["bits"]) - set(coefs):
                raise SystemExit(f"bridge: row {label} names only part of {X}'s bits")
            rpn += [info["e2"] if k > 0 else info["e1"], str(abs(k)), "*", "+"]
            for b in info["bits"]:
                new.pop(b)
            for s in info["S"]:
                new[s] = new.get(s, 0) + k
            d -= k * info["l"]
        emit(f"@S[{label}] pol {' '.join(rpn)} ;")
        subst.append((f"@S[{label}]", {k: v for k, v in new.items() if v}, d))

    # selectors: a baguette row that is a substituted cake row up to one literal
    sel_names = {san for orig, san in sanit.items() if orig.startswith("$ne")}
    sel_vars = {f"{s}_ge_1" for s in sel_names}
    canon = [(lab, *lit_form(c, d)) for lab, c, d in subst]
    defined = {}   # selector var -> its flag literal F (s <-> F)

    def selector_match(lits, d):
        """lits has one selector literal; find a cake row with one other literal in its place."""
        sl = next(l for l in lits if l.lstrip("~") in sel_vars)
        rest = {k: v for k, v in lits.items() if k != sl}
        for lab, clits, cd in canon:
            if cd != d or len(clits) != len(lits):
                continue
            extra = [k for k in clits if k not in rest or clits[k] != rest[k]]
            if len(extra) != 1:
                continue
            fl = extra[0]
            if fl.lstrip("~") in atoms or fl.lstrip("~") in owner:
                continue
            if all(clits.get(k) == v for k, v in rest.items()):
                return sl, fl, clits[fl], lab
        return None

    pins = []
    for label, terms, op, rhs in bag:
        coefs, d = var_form(terms, op, rhs)
        line = row_text(terms, op, rhs)
        m = re.fullmatch(r"\+1 ~(\S+)_ge_(m?\d+) \+1 (\S+)_ge_(m?\d+) >= 1", line)
        if m and m.group(1) == m.group(3) and pv(m.group(2)) == pv(m.group(4)) + 1:
            pins.append(f"@{label} ia {line} : @L[{m.group(1)}_ge_{m.group(2)}] ;")
            continue
        hit = next((lab for lab, c2, d2 in subst if c2 == coefs and d2 >= d), None)
        if hit:
            pins.append(f"@{label} ia {line} : {hit} ;")
            continue
        lits, ld = lit_form(coefs, d)
        if any(l.lstrip("~") in sel_vars for l in lits):
            found = selector_match(lits, ld)
            if found:
                sl, fl, mc, lab = found
                s = sl.lstrip("~")
                F = fl if sl == s else neg(fl)   # s <-> F
                if s not in defined:
                    defined[s] = F
                    emit(f"@D1[{s}] red +1 ~{s} +1 {F} >= 1 : {s} -> {F} ;")
                    emit(f"@D2[{s}] red +1 {s} +1 {neg(F)} >= 1 : {s} -> {F} ;")
                if defined[s] == F:
                    # swap fl for sl: add mc * (sl + ~fl >= 1)
                    swap = f"@D2[{s}]" if sl == s else f"@D1[{s}]"
                    emit(f"@P[{label}] pol {lab} {swap} {mc} * + ;")
                    pins.append(f"@{label} ia {line} : @P[{label}] ;")
                    continue
        pins.append(f"@{label} rup {line} ;")
    out.extend(pins)

    lines = open(bag_pbp).read().splitlines()
    if not (lines and lines[0].startswith("pseudo-Boolean proof version") and lines[1].startswith("f ")):
        raise SystemExit("bridge: baguette's proof does not start with its header and `f N`")
    print(lines[0])
    print(f"f {len(cake)} ;")
    print("\n".join(out))
    print("\n".join(lines[2:]))


if __name__ == "__main__":
    if len(sys.argv) != 5:
        print(__doc__.splitlines()[2], file=sys.stderr)
        sys.exit(64)
    main(*sys.argv[1:5])
