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

Atoms and reifications (T4, D-0178). cake writes a Boolean reifier `(b = 1)` as its atom
`i[b][eq1]`, defined over b's bit; after substitution that atom equals baguette's b_ge_1, and
the bridge swaps one for the other through a clause derived by `rup` (@Q), the same for every
atom that equals one baguette literal or a constant. int_eq_reif/int_ne_reif's disequality
half is cake's `lt`/`gt` flags and its clause `lt + gt + eq1 >= 1`: one resolvent eliminates
a flag, and baguette's `_neN` selector is defined as the other by the red pair above. A
candidate whose big-M exceeds baguette's (bit range against declared bounds) is saturated.

The globals (T5, D-0180). cake's element, global_cardinality and inverse rows, and its
encoding of a hole (`in`), name INTERIOR value atoms i[X][eq<v>] (l < v < u), which no single
baguette literal equals; the order encoding's indicator does, [x = v] = x_ge_v - x_ge_(v+1).
The bridge derives the identity as two rows (@Ep by rup, @Em by one pol from two rup clauses
and the rung) and swaps c*eq for c*(x_ge_v - x_ge_(v+1)). A copy baguette makes of a
variable repeated in a global_cardinality (a fresh integer tied by int_eq) has its rungs
DEFINED as the original's by a red pair each (@Y1, @Y2), and a candidate is moved onto the
copy where baguette's row names it. A row that is not a clause and that no candidate implies
is tried once more against candidates that share variables with it: a literal baguette's
row does not have is weakened away (pol's `w`), or resolved against one of baguette's own
binary clauses (@R, rup) when weakening is too weak, then the result is saturated. That is
member's big-M rows, over the intersection of x_k's and y's ranges where cake's is over both
whole ranges, with the end values guarded by separate clauses `b -> x_k >= ..`.

Pins, in this order: a ladder row is `ia` against its @L; a row a substituted cake row
implies with the same coefficients is `ia` against it; a row a swapped, resolved or
saturated candidate implies syntactically is `ia` against that candidate's `pol` line @W;
anything else is `rup` (all_different's per-value clauses close by unit propagation over the
substituted pair rows and their flags; a hole's clause over cake's `in` rows and its
`i[X][ge/eq]` atoms; array_bool_and/or's `r -> a_i` and `a_i -> r` clauses).
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

    # ---- cake's auxiliaries against baguette's literals (T2's selectors, T4's atoms) ----
    #
    # A substituted cake row is over baguette's order atoms plus cake's own auxiliaries:
    #   ATOMS  i[X][ge<v>], i[X][eq<v>] (defined over X's bits, so after substitution over
    #          x's ladder) and n[K][ge<v>]/n[K][eq<v>] (a constant K in a reify tuple, defined
    #          by unit rows). Each atom that equals ONE baguette literal (ge<v> is x_ge_v;
    #          eq<v> is ~x_ge_(l+1) at l and x_ge_u at u, so b_ge_1 for a 0..1 Boolean) or a
    #          constant is replaced by it: c*L becomes c*M by adding c*(~L + M >= 1), a
    #          clause derived by `rup` from the substituted atom definitions (@Q); a FALSE
    #          L by adding c*(~L >= 1), a TRUE L by the literal axiom ~L (weakening).
    #   FLAGS  b[c][...], x[c][...]: constraint-local, with no baguette counterpart. A flag
    #          that stands where baguette has a fresh selector (`_neN_ge_1`) DEFINES that
    #          selector by a red pair (s fresh, so the pair is a renaming), and is replaced
    #          by it the same way (@D1 = ~s + F, @D2 = s + ~F).
    # A candidate is a substituted row, or one RESOLVENT of it with a substituted clause
    # over flags and atoms (int_eq_reif's `lt + gt + eq1 >= 1`: Y - X + 4~lt >= 1 plus
    # 4 times it eliminates lt). A baguette row is pinned by `ia` against the first candidate
    # that, after the replacements, implies it syntactically: sum over its literals of the
    # coefficient it loses (max(0, a - b)) at most its slack over the baguette row's degree.
    # That is where a baguette big-M is larger than cake's, or a guard cake does not have;
    # where cake's big-M is the larger (bit range against declared bounds), the candidate
    # is saturated first.
    ATOM = re.compile(r"(i|n)\[(.+)\]\[(ge|eq)(-?\d+)\]")
    sel_names = {san for orig, san in sanit.items() if orig.startswith("$ne")}
    sel_vars = {f"{s}_ge_1" for s in sel_names}
    bagvars = set(atoms) | sel_vars

    # COPIES (T5, D-0180). baguette's front end copies a variable that occurs twice in a
    # global_cardinality into a fresh integer tied by int_eq (SPEC 2.1), so its .opb has a
    # ladder cake's file has no counterpart for. Each rung Y_ge_v of such a copy whose
    # int_eq rows `~Y_ge_v + X_ge_v >= 1` and `Y_ge_v + ~X_ge_v >= 1` name a known atom
    # X_ge_v is DEFINED as it, by a red pair (Y fresh, so the pair is a renaming):
    #   @Y1[Y]  ~Y + X >= 1 : Y -> X        @Y2[Y]  Y + ~X >= 1 : Y -> X
    # and a candidate is moved onto the copy where baguette's row names it (match below).
    binary = set()
    for _, terms, op, rhs in bag:
        if op == ">=" and rhs == 1 and len(terms) == 2 and all(c == 1 for c, _ in terms):
            binary.add(frozenset(v for _, v in terms))
    alias = {}
    for _, terms, _, _ in bag:
        for _, lit in terms:
            Y = lit.lstrip("~")
            if Y in bagvars or Y in alias or not re.fullmatch(r".+_ge_m?\d+", Y):
                continue
            partners = sorted(next(iter(b - {f"~{Y}"})) for b in binary if f"~{Y}" in b)
            for X in partners:
                if X in atoms and frozenset((Y, f"~{X}")) in binary:
                    alias[Y] = X
                    emit(f"@Y1[{Y}] red +1 ~{Y} +1 {X} >= 1 : {Y} -> {X} ;")
                    emit(f"@Y2[{Y}] red +1 {Y} +1 ~{X} >= 1 : {Y} -> {X} ;")
                    break
    bagvars |= set(alias)

    def var_of(lit):
        return lit.lstrip("~")

    def atom_value(var):
        m = ATOM.fullmatch(var)
        if not m:
            return None
        kind, X, op, v = m.group(1), m.group(2), m.group(3), int(m.group(4))
        if kind == "n":
            K = int(X)
            return "T" if (K >= v if op == "ge" else K == v) else "F"
        info = ivars.get(X)
        if info is None:
            return None
        l, u, x = info["l"], info["ub"], info["x"]
        if op == "ge":
            return "T" if v <= l else "F" if v > u else f"{x}_ge_{vn(v)}"
        if v < l or v > u:
            return "F"
        if l == u:
            return "T"
        if v == l:
            return f"~{x}_ge_{vn(l + 1)}"
        if v == u:
            return f"{x}_ge_{vn(u)}"
        return None

    def lneg(m):
        return {"T": "F", "F": "T"}.get(m) or neg(m)

    def clause(*lits, d=1):
        return var_form([(1, l) for l in lits], ">=", d)

    def add(row, k, other):
        c1, d1 = row
        c2, d2 = other
        out_c = dict(c1)
        for v, c in c2.items():
            out_c[v] = out_c.get(v, 0) + k * c
        return {v: c for v, c in out_c.items() if c}, d1 + k * d2

    deferred = {}   # label -> the line deriving it, emitted on first use
    needs = {}      # label -> the deferred labels its line cites
    done = set()

    def ensure(label):
        if label in deferred and label not in done:
            done.add(label)
            for dep in needs.get(label, ()):
                ensure(dep)
            emit(deferred[label])

    qlab = {}

    def interior_eq(var):
        """(x, v) when var is cake's i[X][eq<v>] with l < v < u: no ONE baguette literal is
        [x = v], but the order encoding's indicator x_ge_v - x_ge_(v+1) is (T5, D-0180)."""
        m = ATOM.fullmatch(var)
        if not m or m.group(1) != "i" or m.group(3) != "eq" or m.group(2) not in ivars:
            return None
        info, v = ivars[m.group(2)], int(m.group(4))
        return (info["x"], v) if info["l"] < v < info["ub"] else None

    def eq_identity(L):
        """Swap an interior eq atom for its indicator. With e = i[X][eq<v>], a = x_ge_v,
        b = x_ge_(v+1):
          @Ep[e]  e + ~a + b >= 1     (rup: a and ~b fix x's ladder, so the substituted
                                      ge/eq definitions propagate e)
          @Em[e]  ~e + a + ~b >= 2    (pol: the two rup clauses ~e + a, ~e + ~b, plus the
                                      rung ~b + a, divided by 2)
        In variable form these are e - a + b >= 0 and -e + a - b >= 0, i.e. e = a - b, so
        c*e is replaced by c*(a - b) exactly: a positive e by adding c*@Em, a negated one
        by adding c*@Ep."""
        e = var_of(L)
        got = interior_eq(e)
        if got is None:
            return None
        x, v = got
        a, b = f"{x}_ge_{vn(v)}", f"{x}_ge_{vn(v + 1)}"
        if L == e:
            lab = f"@Em[{e}]"
            if lab not in deferred:
                q1, q2 = f"@Ea[{e}]", f"@Eb[{e}]"
                deferred[q1] = f"{q1} rup +1 ~{e} +1 {a} >= 1 ;"
                deferred[q2] = f"{q2} rup +1 ~{e} +1 ~{b} >= 1 ;"
                deferred[lab] = f"{lab} pol {q1} {q2} + @L[{b}] + 2 d ;"
                needs[lab] = [q1, q2]
            return lab, clause(neg(e), a, neg(b), d=2), None
        lab = f"@Ep[{e}]"
        deferred.setdefault(lab, f"{lab} rup +1 {e} +1 ~{a} +1 {b} >= 1 ;")
        return lab, clause(e, neg(a), b), None

    def atom_swap(L):
        """(cite, its row, M) to replace literal L (an atom) by M, or None."""
        val = atom_value(var_of(L))
        if val is None:
            return eq_identity(L)
        M = val if L == var_of(L) else lneg(val)
        if M == "T":   # L is false: the literal axiom ~L drops it (weakening)
            return neg(L), clause(neg(L), d=0), None
        if L not in qlab:
            k = len(qlab)
            qlab[L] = f"@Q[{k}]"
            body = f"+1 {neg(L)} >= 1" if M == "F" else f"+1 {neg(L)} +1 {M} >= 1"
            deferred[qlab[L]] = f"{qlab[L]} rup {body} ;"
        row = clause(neg(L)) if M == "F" else clause(neg(L), M)
        return qlab[L], row, (None if M == "F" else M)

    defined = {}   # selector var s -> the flag literal F it was defined as (s <-> F)

    def flag_swap(L):
        for s_, F in defined.items():
            if L == F:   # F -> s: add (~F + s), @D2
                return f"@D2[{s_}]", clause(neg(F), s_)
            if L == neg(F):   # ~F -> ~s: add (F + ~s), @D1
                return f"@D1[{s_}]", clause(F, neg(s_))
        return None

    def replaced(rpn, row, deps, swap):
        rpn, deps = list(rpn), list(deps)
        lits, _ = lit_form(*row)
        for L, c in lits.items():
            got = swap(L)
            if got is None:
                continue
            cite, crow = got[0], got[1]
            rpn += [cite, str(c), "*", "+"]
            if cite.startswith(("@Q", "@E")):
                deps.append(cite)
            row = add(row, c, crow)
        return rpn, row, deps

    # candidates: (rpn, row after the atoms are replaced, deps)
    cands = []
    for lab, c, d in subst:
        if re.fullmatch(r"@S\[[in]\[.+\]\[(ge|eq)-?\d+\]\[[fr]\]\]|@[in]\[.+\]\[(ge|eq)-?\d+\]\[[fr]\]", lab):
            continue   # an atom's own definition
        if all(v in bagvars for v in c):
            continue   # already over baguette's literals: the exact `hit` above covers it
        cands.append(replaced([lab], (c, d), [], atom_swap))

    def is_flag(v):
        return v not in bagvars and v not in owner and not ATOM.fullmatch(v)

    flag_clauses = []
    for rpn, row, deps in cands:
        lits, d = lit_form(*row)
        if d == 1 and all(a == 1 for a in lits.values()) and any(is_flag(var_of(l)) for l in lits):
            flag_clauses.append((rpn, row, deps, lits))
    resolvents = []
    for rpn, row, deps in cands:
        lits, d = lit_form(*row)
        if d == 1 and all(a == 1 for a in lits.values()):
            continue
        for L, c in lits.items():
            if not is_flag(var_of(L)):
                continue
            for crpn, crow, cdeps, clits in flag_clauses:
                if neg(L) in clits:
                    resolvents.append((rpn + crpn + [str(c), "*", "+"], add(row, c, crow),
                                       deps + cdeps))
    cands += resolvents
    cvars = [{var_of(l) for l in lit_form(*row)[0]} & bagvars for _, row, _ in cands]
    nw = [0]

    def implies(rl, rd, bl, bd):
        return rd - sum(max(0, a - bl.get(l, 0)) for l, a in rl.items()) >= bd

    def saturate(rpn, rl, rd):
        """cake's big-M is over the bit range (0..7 for 0..4), baguette's over the declared
        bounds; once the bits are the ladder, saturation brings the first down to the second."""
        if any(a > rd for a in rl.values()):
            return rpn + ["s"], {l: min(a, rd) for l, a in rl.items()}
        return rpn, rl

    rlab = {}

    def tighten(rpn, rl, rd, blits, resolve=False):
        """Weaken away (pol's `w`) every literal baguette's row does not have, then
        saturate: a cake big-M over the variables' whole ranges against baguette's over
        the INTERSECTION of the ranges, whose end values baguette guards by separate
        clauses (member's `b -> x = y`, T5, D-0180)."""
        extra = [l for l in rl if l not in blits]
        if not extra:
            return None
        rl, deps = dict(rl), []
        for L in extra:
            c = rl.pop(L)
            # an extra literal L that one of baguette's own binary clauses ~L + M (M in
            # this row) resolves away keeps the degree: c*L + c*(~L + M >= 1) is c*M + c,
            # and the degree rises by c. That is member's end values: `b -> y <= 5` turns
            # cake's y_ge_6 into baguette's guard ~b (D-0180). Otherwise weaken L away.
            ms = [m for m in blits if frozenset((neg(L), m)) in binary] if resolve else []
            M = max(ms, key=lambda m: (blits[m], m)) if ms else None
            if M is None:
                rpn = rpn + [var_of(L), "w"]
                rd -= c
                continue
            lab = f"@R[{len(rlab)}]"
            rlab.setdefault(frozenset((neg(L), M)), lab)
            lab = rlab[frozenset((neg(L), M))]
            deferred.setdefault(lab, f"{lab} rup +1 {neg(L)} +1 {M} >= 1 ;")
            deps.append(lab)
            rpn = rpn + [lab, str(c), "*", "+"]
            rl[M] = rl.get(M, 0) + c
        rpn, rl = saturate(rpn, rl, rd)
        return rpn, rl, rd, deps

    def onto_copies(rpn, row, bcoefs):
        """Move the coefficient baguette's row puts on a copy Y off its original X: add
        k * @Y2 (X -> Y) for +k on Y, k * @Y1 (Y -> X) for -k."""
        for Y, k in bcoefs.items():
            if Y not in alias or k == 0:
                continue
            X = alias[Y]
            if k > 0:
                rpn, row = rpn + [f"@Y2[{Y}]", str(k), "*", "+"], add(row, k, ({Y: 1, X: -1}, 0))
            else:
                rpn, row = rpn + [f"@Y1[{Y}]", str(-k), "*", "+"], add(row, -k, ({Y: -1, X: 1}, 0))
        return rpn, row

    def match(blits, bd, bcoefs, loose=False):
        """loose: a second pass for a row that is not a clause (rup would not close it),
        trying candidates that share variables with it rather than only those inside it,
        with tighten's weakening as the only way to match."""
        bvars = {var_of(l) for l in blits}
        bvars |= {alias[v] for v in bvars if v in alias}
        undef = [l for l in blits if var_of(l) in sel_vars and var_of(l) not in defined]
        for (rpn, row, deps), cv in zip(cands, cvars):
            if loose and (cv <= bvars or not cv & bvars or undef):
                continue
            if not loose and not cv <= bvars:
                continue
            rpn2, row2, _ = replaced(rpn, row, [], flag_swap)
            rpn2, row2 = onto_copies(rpn2, row2, bcoefs)
            rl, rd = lit_form(*row2)
            if any(not is_flag(var_of(l)) and var_of(l) not in bagvars for l in rl):
                continue   # an atom with no baguette literal of its own
            unk = [l for l in rl if is_flag(var_of(l))]
            if not unk and not undef:
                rpn3, rl3 = saturate(rpn2, rl, rd)
                if implies(rl3, rd, blits, bd):
                    return rpn3, deps, None
                for resolve in (False, True):
                    got = tighten(rpn2, rl, rd, blits, resolve)
                    if got and implies(got[1], got[2], blits, bd):
                        return got[0], deps + got[3], None
                continue
            if len(unk) == 1 and len(undef) == 1:
                F_lit, sl = unk[0], undef[0]
                s_ = var_of(sl)
                F = F_lit if sl == s_ else neg(F_lit)   # s <-> F
                c = rl[F_lit]
                trial = {l: a for l, a in rl.items() if l != F_lit}
                trial[sl] = trial.get(sl, 0) + c
                cite = f"@D2[{s_}]" if sl == s_ else f"@D1[{s_}]"
                rpn3, trial = saturate(rpn2 + [cite, str(c), "*", "+"], trial, rd)
                if implies(trial, rd, blits, bd):
                    return rpn3, deps, (s_, F)
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
        found = match(*lit_form(coefs, d), coefs) if cands else None
        bl, bd = lit_form(coefs, d)
        if not found and cands and not (bd == 1 and all(a == 1 for a in bl.values())):
            found = match(bl, bd, coefs, loose=True)
        if found:
            rpn, deps, new = found
            if new:
                s_, F = new
                defined[s_] = F
                emit(f"@D1[{s_}] red +1 ~{s_} +1 {F} >= 1 : {s_} -> {F} ;")
                emit(f"@D2[{s_}] red +1 {s_} +1 {neg(F)} >= 1 : {s_} -> {F} ;")
            for dep in deps:
                ensure(dep)
            if len(rpn) == 1:
                pins.append(f"@{label} ia {line} : {rpn[0]} ;")
            else:
                nw[0] += 1
                emit(f"@W[{nw[0]}] pol {' '.join(rpn)} ;")
                pins.append(f"@{label} ia {line} : @W[{nw[0]}] ;")
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
