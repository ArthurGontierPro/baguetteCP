#!/usr/bin/env python3
"""Re-derive baguette's .opb from cake_pb_cp's, at the head of baguette's proof (M14-e2e-verification).

Usage: python3 -I bridge.py CAKE.opb NAMES BAGUETTE.opb BAGUETTE.pbp > BRIDGED.pbp

CAKE.opb is what the verified encoder wrote for MODEL.scp; NAMES is the translator's
`SCP_NAME FLATZINC_NAME` table (tools/e2e/fzn2scp.py); BAGUETTE.opb/.pbp is baguette's own
run on MODEL.fzn, order arm. The output is a proof over CAKE.opb: a prefix that derives every
row of BAGUETTE.opb under its own label, then baguette's proof unchanged but for its `f N`.
An optional NAMES.flags beside NAMES (written by the translator for regular) names cake's flag
for each of baguette's state flags. Exit 0 with the bridged proof on stdout; 64 with the usage
line on stderr when there are not four arguments; 1 with a `bridge: ...` message on stderr when
an input has a shape the bridge does not handle (a row it cannot read, a variable missing from
NAMES, an objective on one side only).

This script is UNTRUSTED. If it writes a wrong line, the checker refuses it; nothing it does
can make a wrong answer verify, because the proof is checked against CAKE.opb, which the
verified encoder wrote. Its only obligation is to be complete on the covered families.

The prefix (D-0174 section 4: the record that chose cake_pb_cp as the verified encoder and
this re-derivation, at the head of baguette's proof, as the way to reach it), per integer X
over [l, u], B = cake's bit sum of X, x_ge_v baguette's order atoms (PROOF-FORMAT section 3),
S = sum_{l<v<=u} x_ge_v:

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

The far families (T6, D-0195). regular's state flags, which the translator leaves out of the
.scp, are DEFINED as cake's flags named in NAMES.flags (red pairs, then swapped as selectors);
cumulative's capacity rows are each `ia` against ONE pol of cake's capacity, contribution,
activity and flag rows (@K); int_abs's sign guard, a Boolean cake does not have, is defined as
the ladder literal its int_lin_le_reif row names, and a row true in both signs is derived by
contradiction (`pbc`, the negation plus each of the constraint's guarded rows, saturated).

The bits arm (T7, D-0196). A variable baguette encodes on bits (`--bits-above`) has `x_bit_i`,
the bits of x - l, unsigned, and no ladder. They are DEFINED from cake's two's-complement bits
by a ripple-carry adder whose every relation is one linear row ([bits_prefix]), which gives the
same halves @E1/@E2 of B = l + S with S = sum 2^i x_bit_i, so the substitution is unchanged;
the two bound rows are `ia` against @BL/@BU. A guarded row whose big-M is baguette's (over the
declared bounds) where cake's is over the bit range is derived by contradiction against the
candidate and the bits variables' ub rows ([tight]). A choice selector `_mxN` (array_int_maximum
over bits) is defined as its flag AND no earlier one, as `sol` sets it; an int_abs guard over a
bits variable as cake's own atom.

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
    if not line or line.startswith("*") or line.startswith("min:"):
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


def bits_prefix(X, x, n, l, u, bits, emit):
    """baguette's BITS arm (T7, D-0196): x_bit_i, i < n, are the bits of x - l, unsigned
    (PROOF-FORMAT section 3), against cake's two's-complement bits of x. With h cake's
    magnitude bits and s its sign (when l < 0), U = B + 2^h [s] is unsigned on m = h + [s]
    digits u_j (b_j, and ~s at j = h), and x - l = U - L' with L' = l + 2^h [s] >= 0. The
    digits of x - l are those of U + c, c = (2^m - L') mod 2^m, by a ripple-carry adder
    whose every relation is one LINEAR row: per digit i, with carry k_i (k_0 = 0)

        d_i + 2 k_(i+1) = u_i + c_i + k_i

    k_(i+1) is a constant or u_i while k_i is a constant, else a fresh variable defined by a
    red pair (@BK1: T - 2k >= 0 : k -> 0, @BK2: 2k - T >= -1 : k -> 1, T = u_i + c_i + k_i;
    both goals are tautologies). d_i (x_bit_i for i < n, x_bith_i above) is defined by the
    two halves of the relation, @BP (witness d -> 1, goal @BK2) and @BN (d -> 0, goal @BK1).
    Summed with weights 2^i the relations telescope to S_all + 2^m k_m = U + c; the final
    carry k_m (literal when c > 0) is a unit by rup against @BPs + cake's lb, and each digit
    above n is zero by rup against @BNk, so the two halves of B = l + S follow by one pol
    each. Returns (E1, E2, {x_bit_i: 2^i})."""
    pos = sorted((c, b) for b, c in bits.items() if c > 0)
    neg_ = [b for b, c in bits.items() if c < 0]
    h = len(pos)
    if [c for c, _ in pos] != [1 << j for j in range(h)] or len(neg_) > 1:
        raise SystemExit(f"bridge: {X}'s bits are not a two's-complement bit sum")
    digits = [b for _, b in pos] + [f"~{b}" for b in neg_]
    m = len(digits)
    L = l + (1 << h if neg_ else 0)
    if not 0 <= L < (1 << m) or n > m:
        raise SystemExit(f"bridge: {X} over [{l},{u}] does not fit its {m} digits")
    c = ((1 << m) - L) % (1 << m)

    def row(terms, d):
        coefs, dd = var_form(terms, ">=", d)
        return " ".join(f"{v:+d} {k}" for k, v in coefs.items()) + f" >= {dd}"

    def lneg(t):
        return [(-a, v) for a, v in t]

    k = 0
    for i in range(m):
        ui, ci = digits[i], (c >> i) & 1
        d = f"{x}_bit_{i}" if i < n else f"{x}_bith_{i}"
        if isinstance(k, int):
            sk = ci + k
            kp = 0 if sk == 0 else ui if sk == 1 else 1
            T, tc = [(1, ui)], sk
        else:
            kp = f"{x}_bitc_{i + 1}"
            T, tc = [(1, ui), (1, k)], ci
            emit(f"@BK1[{kp}] red {row(T + [(-2, kp)], -tc)} : {kp} -> 0 ;")
            emit(f"@BK2[{kp}] red {row([(2, kp)] + lneg(T), tc - 1)} : {kp} -> 1 ;")
        kt, kc = ([], 2 * kp) if isinstance(kp, int) else ([(2, kp)], 0)
        emit(f"@BP[{d}] red {row([(1, d)] + kt + lneg(T), tc - kc)} : {d} -> 1 ;")
        emit(f"@BN[{d}] red {row(T + lneg(kt) + [(-1, d)], kc - tc)} : {d} -> 0 ;")
        k = kp
    dig = [f"{x}_bit_{i}" if i < n else f"{x}_bith_{i}" for i in range(m)]

    def wsum(tag):
        return " ".join([f"@{tag}[{dig[0]}]"] + [f"@{tag}[{dig[i]}] {1 << i} * +" for i in range(1, m)])

    emit(f"@BPs[{x}] pol {wsum('BP')} ;")
    emit(f"@BNs[{x}] pol {wsum('BN')} ;")
    lit = not isinstance(k, int)
    if not lit and k != 0:
        raise SystemExit(f"bridge: {X}'s final carry is the constant {k}")
    M = 1 << m
    if lit:
        emit(f"@BPk[{x}] pol @BPs[{x}] @i[{X}][lb] + ;")
        emit(f"@BK[{x}] rup +1 {k} >= 1 ;")
    emit(f"@BNk[{x}] pol @BNs[{x}] @i[{X}][ub] +{f' @BK[{x}] {M} * +' if lit else ''} ;")
    for j in range(n, m):
        emit(f"@BZ[{dig[j]}] rup +1 ~{dig[j]} >= 1 ;")
    e1 = f"@BE1[{x}] pol @BNs[{x}]" + (f" @BK[{x}] {M} * +" if lit else "")
    e1 += "".join(f" {dig[j]} {1 << j} * +" for j in range(n, m))
    e2 = f"@BE2[{x}] pol @BPs[{x}]" + (f" {neg(k)} {M} * +" if lit else "")
    e2 += "".join(f" @BZ[{dig[j]}] {1 << j} * +" for j in range(n, m))
    emit(e1 + " ;")
    emit(e2 + " ;")
    return f"@BE1[{x}]", f"@BE2[{x}]", {f"{x}_bit_{i}": 1 << i for i in range(n)}


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
    # T7 (D-0196): which of baguette's variables are on its BITS arm (`--bits-above`): their
    # `x_bit_i` are in baguette's .opb, and no ladder is
    bag_names = {v.lstrip("~") for _, terms, _, _ in bag for _, v in terms}
    bitvars = set()
    bound_pins = []   # (label, coefs, d): baguette's two bound rows of a bits variable
    for X, info in ivars.items():
        fz = fzn_of.get(X)
        if fz is None:
            raise SystemExit(f"bridge: cake variable {X} is not in the names table")
        x = sanit.get(fz, fz)
        l, u, bits = info["lb"], info["ub"], info["bits"]
        n = 0
        while f"{x}_bit_{n}" in bag_names:
            n += 1
        if n:
            e1, e2, W = bits_prefix(X, x, n, l, u, bits, emit)
            bitvars.update(W)
            info.update(l=l, S=[], W=W, e1=e1, e2=e2, x=x, n=n)
            # baguette's bound rows, S >= 0 and -S >= -(u - l): E2 + cake's lb, E1 + cake's ub
            emit(f"@BL[{x}] pol {e2} @i[{X}][lb] + ;")
            emit(f"@BU[{x}] pol {e1} @i[{X}][ub] + ;")
            bound_pins.append((f"@BL[{x}]", dict(W), 0))
            bound_pins.append((f"@BU[{x}]", {b: -w for b, w in W.items()}, l - u))
            continue
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
            # the running rows and the halves before this one are spent: kept, they hold
            # Theta(w^2) terms, and a width of 15 529 (2015_gfd-schedule) took veripb
            # --elaborate to 30 GB and exhausted cake_pb_cp's 24 GB heap (T8, D-0182)
            if i:
                emit(f"del id @T1[{S[i - 1]}] @E1[{S[i - 1]}] ;")
            prev = f"@E1[{a}]"
        if S:
            emit(f"del id @T1[{S[-1]}] ;")
        e1 = prev
        prev = f"@i[{X}][ub]"
        for v in range(u, l, -1):
            a = f"{x}_ge_{vn(v)}"
            K = bmax - v + 1
            j = v - l - 1
            more = j + 1 < len(S)
            emit(f"@T2[{a}] pol {'@T2[' + S[j + 1] + '] ' if more else ''}{a}{' +' if more else ''} ;")
            emit(f"@E2[{a}] pol {prev} {K} * @A2[{a}] + @T2[{a}] + {K + 1} d ;")
            if more:
                emit(f"del id @T2[{S[j + 1]}] @E2[{S[j + 1]}] ;")
            prev = f"@E2[{a}]"
        if S:
            emit(f"del id @T2[{S[0]}] ;")
        e2 = prev
        info.update(l=l, S=S, W={a: 1 for a in S}, e1=e1, e2=e2, x=x, n=0)
        for v in range(l + 1, u):
            hi, lo = f"{x}_ge_{vn(v + 1)}", f"{x}_ge_{vn(v)}"
            emit(f"@L[{hi}] pol @A1[{hi}] @A2[{lo}] + s {(bmax - bmin) + 2} d ;")
    owner = {b: X for X, info in ivars.items() for b in info["bits"]}

    # the OBJECTIVE (T8, D-0182). cake writes `min: k*B` for (minimize X) (k = 1) and
    # (maximize X) (k = -1), over X's bits and with no constant; baguette writes
    # `min: k*S +k*l`, X's order encoding with its constant (compile.ml, M5-T1). The two
    # are the same function of x, so every objective value, every `soli` bound and the
    # numbers of `conclusion BOUNDS` agree, and only the improving constraint each
    # `soli` adds needs translating: the checker adds `k*B <= v - 1` over cake's bits,
    # where baguette's later lines expect `k*S + k*l <= v - 1` over its ladder. The
    # bridge renames each `@cK soli` to `@O[cK]` and derives @cK from it by the same
    # substitution as a model row (B -> l + S: k * @E1 for k > 0, |k| * @E2 for k < 0).
    obj_fix = objective(cake_opb, bag_lines, ivars, owner)

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
            for s, w in info["W"].items():
                new[s] = new.get(s, 0) + k * w
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
    ABS = re.compile(r"@S\[c\[.+\]\[(posge|posle|negle|negge)\]\]")
    sel_names = {san for orig, san in sanit.items() if orig.startswith(("$ne", "$mx"))}
    sel_vars = {f"{s}_ge_1" for s in sel_names}
    bagvars = set(atoms) | sel_vars | bitvars

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
    bin_partners = {}   # literal a -> every b with the binary clause a + b >= 1 in baguette's .opb
    for ab in binary:
        a, b = tuple(ab)
        bin_partners.setdefault(a, set()).add(b)
        bin_partners.setdefault(b, set()).add(a)
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
    # D-0262: a copy over a domain of more than one rung is tied by int_eq's two LINEAR
    # rows, sum_v Y_ge_v - sum_v X_ge_v >= 0 and its mirror (a binary clause per rung only
    # where the ladder has one rung), so the clause test above never sees it and its rungs
    # were cited (@L) undefined. Recognised from the two rows over the same values; each
    # rung is defined by the same red pair, the copy's ladder rungs @L derived from the
    # original's, and the two rows pinned as the sums of the pairs (copy_eq).
    copy_eq = {}
    ladder = {}
    for a in atoms:
        base, v = a.rsplit("_ge_", 1)
        ladder.setdefault(base, {})[pv(v)] = a
    for _, terms, op, rhs in bag:
        coefs, d = var_form(terms, op, rhs)
        if d != 0 or not coefs or set(coefs.values()) != {1, -1}:
            continue
        pos = {v for v, c in coefs.items() if c == 1}
        negs = {v for v, c in coefs.items() if c == -1}
        for ys, xs in ((pos, negs), (negs, pos)):
            if any(Y in bagvars or Y in alias or not re.fullmatch(r".+_ge_m?\d+", Y) for Y in ys):
                continue
            ybases = {Y.rsplit("_ge_", 1)[0] for Y in ys}
            xbases = {X.rsplit("_ge_", 1)[0] for X in xs}
            if len(ybases) != 1 or len(xbases) != 1 or not xs <= atoms:
                continue
            yb, xb = ybases.pop(), xbases.pop()
            vals = sorted(pv(Y.rsplit("_ge_", 1)[1]) for Y in ys)
            if sorted(ladder.get(xb, {})) != vals:
                continue
            for v in vals:
                Y, X = f"{yb}_ge_{vn(v)}", f"{xb}_ge_{vn(v)}"
                alias[Y] = X
                emit(f"@Y1[{Y}] red +1 ~{Y} +1 {X} >= 1 : {Y} -> {X} ;")
                emit(f"@Y2[{Y}] red +1 {Y} +1 ~{X} >= 1 : {Y} -> {X} ;")
            for v, w in zip(vals[1:], vals):
                hi, lo = f"{yb}_ge_{vn(v)}", f"{yb}_ge_{vn(w)}"
                emit(f"@L[{hi}] pol @Y1[{hi}] @L[{alias[hi]}] + @Y2[{lo}] + ;")
            for k, sign in (("@Y2", 1), ("@Y1", -1)):
                key = frozenset({**{f"{yb}_ge_{vn(v)}": sign for v in vals},
                                 **{f"{xb}_ge_{vn(v)}": -sign for v in vals}}.items())
                rpn = " ".join(f"{k}[{yb}_ge_{vn(v)}]" + (" +" if i else "")
                               for i, v in enumerate(vals))
                copy_eq[key] = rpn
            break
    bagvars |= set(alias)

    # REGULAR'S STATE FLAGS (T6, D-0195). The translator leaves mznlib's flags out of the .scp
    # (they are existential) and names, in NAMES.flags, cake's own flag for each one: s(i,q) is
    # x[cK][<i>_<pi(q)>][st]. baguette's flag (fresh in the proof: cake's file has no such
    # variable) is DEFINED as it by a red pair, the selectors' @D1/@D2 below, and the matcher
    # then sees cake's regular rows over baguette's flags: ALO, AMO, START and ACCEPT are
    # `ia`, a forward clause over a symbol run is `rup` through the transition clauses and the
    # letters' eq atoms. A wrong hint is a refused line, never a verified answer.
    reg_defs = []
    import os
    if os.path.exists(names_file + ".flags"):
        for l in open(names_file + ".flags"):
            if l.strip():
                fz, F = l.split()
                s_ = f"{sanit.get(fz, fz)}_ge_1"
                reg_defs.append((s_, F))
                bagvars.add(s_)

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
        if info is None or info["n"]:
            return None   # a bits variable's atoms are not in the prefix (T7)
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
        if ivars[m.group(2)]["n"]:
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
    by_flag = {}   # flag literal -> the selector defined as it (or as its negation)

    def define(s_, F):
        defined[s_] = F
        if F not in ("F", "T"):
            by_flag.setdefault(F, s_)
            by_flag.setdefault(neg(F), s_)

    def undefine(s_):
        F = defined.pop(s_)
        for G in (F, neg(F)) if F not in ("F", "T") else ():
            if by_flag.get(G) == s_:
                del by_flag[G]

    # T7 (D-0196): array_int_maximum/minimum over a bits variable is baguette's CHOICE GROUP,
    # selectors `_mxN` (PROOF-FORMAT section 3), whose `sol` sets the FIRST operand attaining
    # m and no other; cake's array_max flag i is x_i >= m both ways (`[f]` and `[r]`), so at a
    # tie two flags hold. A selector is then defined as its flag AND no earlier one:
    #   @C1[s]  red (i+1) ~s + F_i + sum_{j<i} ~F_j >= i+1 : s -> 0
    #   @C2[s]  red s + ~F_i + sum_{j<i} F_j >= 1         : s -> 1
    # and @D1[s] = ~s + F_i (C1 weakened) still swaps ~F_i for ~s; the at-least-one over the
    # selectors closes by rup through @C2 and cake's al1. The binary max/min's flags have
    # no `[f]` (one direction only), and stay renamings.
    al1_flags = {}
    for label, terms, op, rhs in cake:
        mm = re.fullmatch(r"c\[(.+)\]\[al1\]", label or "")
        if mm and all(re.fullmatch(r"x\[" + re.escape(mm.group(1)) + r"\]\[\d+\]", v) for _, v in terms):
            al1_flags[mm.group(1)] = [v for _, v in terms]
    mx_vars = {f"{san}_ge_1" for orig, san in sanit.items() if orig.startswith("$mx")}
    conj = {}   # selector -> (F_i, the earlier flags)

    def conj_of(s_, F):
        mm = re.fullmatch(r"x\[(.+)\]\[\d+\]", F)
        if s_ not in mx_vars or not mm or F not in al1_flags.get(mm.group(1), ()):
            return None
        fl = al1_flags[mm.group(1)]
        return (F, fl[: fl.index(F)]) if fl.index(F) else None

    def flag_swap(L):
        s_ = by_flag.get(L)
        if s_ is None:
            return None
        F = defined[s_]
        if L == F and s_ in conj:
            return None
        if L == F:   # F -> s: add (~F + s), @D2
            return f"@D2[{s_}]", clause(neg(F), s_)
        return f"@D1[{s_}]", clause(F, neg(s_))   # ~F -> ~s: add (F + ~s), @D1

    for s_, F in reg_defs:
        define(s_, F)
        emit(f"@D1[{s_}] red +1 ~{s_} +1 {F} >= 1 : {s_} -> {F} ;")
        emit(f"@D2[{s_}] red +1 {s_} +1 {neg(F)} >= 1 : {s_} -> {F} ;")

    # ARITH GUARDS (T6, D-0195). int_abs's sign guard S <-> x >= 0 is a model Boolean
    # (X_INTRODUCED_arith_N, D-0060) that cake's file does not have. Its int_lin_le_reif row
    # `g -> sum_v x_ge_v >= k` (or `g -> sum_v ~x_ge_v >= k`) over ONE integer's whole ladder
    # says which literal it is: x_ge_(l+k) (resp. ~x_ge_(u-k+1)). g is DEFINED as that literal
    # by a red pair (g fresh, so the pair is a renaming), and its two rows then close by rup.
    # Only a variable cake does not know and that no other mechanism defined is read so.
    cake_labels = {label for label, _, _, _ in cake}
    ladder_of = {}
    for X, info in ivars.items():
        if info["S"]:
            ladder_of[frozenset(info["S"])] = info
    guards = {}
    for _, terms, op, rhs in bag:
        coefs, d = var_form(terms, op, rhs)
        unk = [v for v in coefs if v not in bagvars and v not in guards]
        if len(unk) != 1 or coefs[unk[0]] >= 0:
            continue
        g = unk[0]
        rest = {v: c for v, c in coefs.items() if v != g}
        # T7 (D-0196): over a BITS variable, g is cake's own atom at that threshold (x's
        # order atoms are not in the prefix), swapped in for it as a selector
        bx = next((X for X, info in ivars.items() if info["n"] and
                   set(rest) == {f"{info['x']}_bit_{i}" for i in range(info["n"])}), None)
        if bx is not None:
            info = ivars[bx]
            c = rest[f"{info['x']}_bit_0"]
            if c in (1, -1) and all(rest[f"{info['x']}_bit_{i}"] == c << i for i in range(info["n"])):
                k = d - coefs[g]
                v = info["l"] + k if c == 1 else info["l"] - k + 1
                if f"i[{bx}][ge{v}][f]" in cake_labels:
                    guards[g] = f"i[{bx}][ge{v}]" if c == 1 else f"~i[{bx}][ge{v}]"
                    define(g, guards[g])
            continue
        info = ladder_of.get(frozenset(rest))
        if info is None or len(set(rest.values())) != 1:
            continue
        c, k = next(iter(rest.values())), d - coefs[g]   # the degree when g holds
        if c == 1 and info["l"] < info["l"] + k <= info["ub"]:
            guards[g] = f"{info['x']}_ge_{vn(info['l'] + k)}"
        elif c == -1 and info["l"] < info["l"] - k + 1 <= info["ub"]:
            guards[g] = f"~{info['x']}_ge_{vn(info['l'] - k + 1)}"
    for g, F in guards.items():
        emit(f"@D1[{g}] red +1 ~{g} +1 {F} >= 1 : {g} -> {F} ;")
        emit(f"@D2[{g}] red +1 {g} +1 {neg(F)} >= 1 : {g} -> {F} ;")
    bagvars |= set(guards)

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
        am = re.fullmatch(r"@S\[[in]\[(.+)\]\[(ge|eq)-?\d+\]\[[fr]\]\]|@[in]\[(.+)\]\[(ge|eq)-?\d+\]\[[fr]\]", lab)
        if am and not ivars.get(am.group(1) or am.group(3), {}).get("n"):
            continue   # an atom's own definition (a bits variable's is a guard's candidate, T7)
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
        # a CLAUSE is resolved too (T8, D-0182): int_eq_reif(x, u, b) at x's upper bound u
        # makes cake's `lt` row the clause `lt -> x <= u - 1` once the bits are the ladder
        for L, c in lits.items():
            if not is_flag(var_of(L)):
                continue
            for crpn, crow, cdeps, clits in flag_clauses:
                if neg(L) in clits:
                    resolvents.append((rpn + crpn + [str(c), "*", "+"], add(row, c, crow),
                                       deps + cdeps))
    cands += resolvents

    # CUMULATIVE (T6, D-0195). cake writes, per task i covering time t, flags cb (s_i <= t),
    # ca (s_i + d_i >= t + 1) and act = cb /\ ca, contribution bits equal to r_i when act,
    # and per t the row cap_t: minus every contribution >= -cap. baguette's row at t is
    # sum_i r_i (s_i_ge_(t+1-d_i) - s_i_ge_(t+1)) <= cap - folded. ONE pol derives it:
    #   cap_t + sum_i ( cge_(i,t) + r_i actc_(i,t) + r_i [cb's clause] + r_i [ca's clause] )
    # cge cancels the contribution bits against cap_t (sum r_i ~act_i >= sum r_i - cap),
    # actc (act \/ ~cb \/ ~ca) turns ~act into ~cb + ~ca, and each flag's clause swaps it for
    # baguette's literal: `cb \/ s_ge_(t+1)` and `ca \/ ~s_ge_(t+1-d)`, each one pol of the
    # flag's own definition row and the atom's @A2 (resp. @A1) at that threshold, saturated;
    # at a clipped end the bound row instead, which leaves the flag's unit. The result is a
    # candidate like any other (`ia` against it, after saturation).
    cake_row = {label: (terms, op, rhs) for label, terms, op, rhs in cake}

    def flag_clause(flab):
        """The flag's [f] row (the flag positive: ~flag -> a bound on one integer) linearised
        at its threshold: (label of a deferred pol, var-form row), or None."""
        got = cake_row.get(flab)
        if got is None:
            return None
        coefs, d = var_form(*got)
        flag = [v for v in coefs if v not in owner]
        Xs = {owner[v] for v in coefs if v in owner}
        if len(flag) != 1 or len(Xs) > 1:
            return None
        F, M = flag[0], coefs[flag[0]]
        lab = f"@K[{flab}]"
        if not Xs:
            if M <= 0 or d <= 0:
                return None
            deferred.setdefault(lab, f"{lab} pol @{flab} s ;")
            return lab, clause(F)
        X = Xs.pop()
        info = ivars[X]
        k = {coefs[b] // c for b, c in info["bits"].items() if b in coefs}
        if len(k) != 1 or set(info["bits"]) - set(coefs) or M <= 0:
            return None
        k = k.pop()
        if k == 1:      # ~F -> B >= d : F \/ x_ge_d
            v = d
            if v <= info["l"]:
                return None
            if v > info["ub"]:
                deferred.setdefault(lab, f"{lab} pol @{flab} @i[{X}][ub] + s ;")
                return lab, clause(F)
            a = f"{info['x']}_ge_{vn(v)}"
            deferred.setdefault(lab, f"{lab} pol @{flab} @A2[{a}] + s ;")
            return lab, clause(F, a)
        if k == -1:     # ~F -> B <= -d : F \/ ~x_ge_(1-d)
            v = 1 - d
            if v > info["ub"]:
                return None
            if v <= info["l"]:
                deferred.setdefault(lab, f"{lab} pol @{flab} @i[{X}][lb] + s ;")
                return lab, clause(F)
            a = f"{info['x']}_ge_{vn(v)}"
            deferred.setdefault(lab, f"{lab} pol @{flab} @A1[{a}] + s ;")
            return lab, clause(F, neg(a))
        return None

    CAP = re.compile(r"c\[(.+)\]\[cap_(-?\d+)\]")
    for label, terms, op, rhs in cake:
        m = CAP.fullmatch(label or "")
        if not m:
            continue
        N, t = m.group(1), m.group(2)
        row = var_form(terms, op, rhs)
        rpn, deps, ok = [f"@{label}"], [], True
        ntasks = 0
        for lab2 in cake_row:
            mm = re.fullmatch(rf"c\[{re.escape(N)}\]\[(\d+)_{re.escape(t)}_cge\]", lab2)
            if not mm:
                continue
            ntasks += 1
            j = mm.group(1)
            cge = var_form(*cake_row[lab2])
            act = f"v[{N}][{j}_{t}][cact]"
            r = -cge[0].get(act, 0)   # cge: r ~act + bits >= r, var form -r act + bits >= 0
            row = add(row, 1, cge)
            rpn += [f"@{lab2}", "+"]
            if r == 0:
                continue
            row = add(row, r, var_form(*cake_row[f"c[{N}][{j}_{t}_actcal1]"]))
            rpn += [f"@c[{N}][{j}_{t}_actcal1]", str(r), "*", "+"]
            for fl in ("cb", "ca"):
                got = flag_clause(f"v[{N}][{j}_{t}][{fl}][f]")
                if got is None:
                    ok = False
                    break
                row = add(row, r, got[1])
                rpn += [got[0], str(r), "*", "+"]
                deps.append(got[0])
            if not ok:
                break
        if not ok or not ntasks:
            continue
        coefs, d = row
        if any(v not in bagvars for v in coefs):
            continue
        klab = f"@K[{label}]"
        deferred[klab] = f"{klab} pol {' '.join(rpn)} ;"
        needs[klab] = deps
        cands.append(([klab], (coefs, d), [klab]))
    cvars = [{var_of(l) for l in lit_form(*row)[0]} & bagvars for _, row, _ in cands]
    # an index from each baguette variable to the candidates that name it, so that a row is
    # tried only against candidates it could match (both passes need a shared variable or,
    # for the first, none at all): the matcher was quadratic in the model (T8, D-0182)
    by_var, no_var = {}, []
    for i, cv in enumerate(cvars):
        for v in cv:
            by_var.setdefault(v, []).append(i)
        if not cv:
            no_var.append(i)
    nw = [0]

    def implies(rl, rd, bl, bd):
        return rd - sum(max(0, a - bl.get(l, 0)) for l, a in rl.items()) >= bd

    ub_of = {}   # a bits variable's x_bit_0 -> (its @BU label, n, l - u)
    for X, info in ivars.items():
        if info["n"]:
            ub_of[f"{info['x']}_bit_0"] = (f"@BU[{info['x']}]", info["n"], info["l"] - info["ub"])

    def lsum(rows):
        acc, dd = {}, 0
        for k, (lits, d) in rows:
            cf, d2 = var_form(list((a, l) for l, a in lits.items()), ">=", d)
            for v, a in cf.items():
                acc[v] = acc.get(v, 0) + k * a
            dd += k * d2
        return lit_form({v: a for v, a in acc.items() if a}, dd)

    def tight(rl, rd, blits, bd):
        """T7 (D-0196): a candidate whose big-M on a guard is cake's, over the BIT range of a
        bits variable, where baguette's row has its own, over the declared bounds. No
        weakening reaches it: the guard false makes the row a bound of the bits, true only
        under baguette's ub row. By contradiction: the negation plus the candidate, saturated,
        forces the guard; the negation plus each negated bits variable's ub row (@BU) then
        has no room for it, and unit propagation closes. The rpn of that second sum, or None."""
        if not any(var_of(l) in bitvars for l in blits):
            return None
        if any(var_of(l) not in {var_of(m) for m in blits} for l in rl):
            # D-0262: a literal the row does not have (another constraint's selector) is free
            # to satisfy the candidate, which the simulation below does not see: it claimed a
            # close that unit propagation did not make (int_eq_reif's row against int_lin_ne's
            # candidate over the same two variables)
            return None
        sa = sum(blits.values())
        nt = ({neg(l): a for l, a in blits.items()}, sa - bd + 1)
        r1l, r1d = lsum([(1, nt), (1, (rl, rd))])
        if r1d < 1:
            return None
        r1l = {l: min(a, r1d) for l, a in r1l.items()}
        rows, rpn = [(1, nt)], []
        for b0, (lab, n, dlu) in ub_of.items():
            if f"~{b0}" not in blits:
                continue
            a = blits[f"~{b0}"]
            x = b0[: -len("_bit_0")]
            if any(blits.get(f"~{x}_bit_{i}") != a << i for i in range(n)):
                return None
            rows.append((a, ({f"{x}_bit_{i}": -(1 << i) for i in range(n)}, dlu)))
            rpn += [lab] + ([str(a), "*"] if a > 1 else []) + (["+"] if rpn else [])
        if not rpn:
            return None
        r2l, r2d = lsum([(k, (lits, d)) for k, (lits, d) in rows])
        # unit propagation closes when what one sum forces leaves the other no room
        def forced(ls, d):
            tot = sum(ls.values())
            return {l for l, a in ls.items() if tot - a < d}

        def room(ls, f):
            return sum(a for l, a in ls.items() if neg(l) not in f)

        if room(r2l, forced(r1l, r1d)) < r2d or room(r1l, forced(r2l, r2d)) < r1d:
            return rpn
        return None

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
            ms = [m for m in bin_partners.get(neg(L), ()) if m in blits] if resolve else []
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

    flags_of = [[L for L in lit_form(*row)[0] if is_flag(var_of(L))] for _, row, _ in cands]
    swap_cache = {}

    def swapped(i):
        """Candidate i with the defined selectors swapped in, in literal form, or None when
        an atom has no baguette literal: cached while no flag of i changes its selector."""
        # the selector AND the flag it is defined as: a selector tried as F, then as ~F
        # (T7, D-0196: both orientations of int_lin_ne's flag over a bits sum) has the same
        # name in by_flag both times, and a cache keyed on the name alone served the first
        sig = tuple((by_flag.get(L), defined.get(by_flag.get(L)), by_flag.get(L) in conj)
                    for L in flags_of[i])
        got = swap_cache.get(i)
        if got and got[0] == sig:
            return got[1]
        rpn, row, _ = cands[i]
        rpn2, row2, _ = replaced(rpn, row, [], flag_swap)
        rl, rd = lit_form(*row2)
        res = None if any(not is_flag(var_of(l)) and var_of(l) not in bagvars for l in rl) \
            else (rpn2, rl, rd)
        swap_cache[i] = (sig, res)
        return res

    def match(blits, bd, bcoefs, loose=False):
        return next(matches(blits, bd, bcoefs, loose), None)

    def matches(blits, bd, bcoefs, loose=False):
        """Every way a candidate implies the row, in the order tried (a generator: the
        selector pre-pass below wants each PROPOSED definition, not only the first).
        loose: a second pass for a row that is not a clause (rup would not close it),
        trying candidates that share variables with it rather than only those inside it,
        with tighten's weakening as the only way to match."""
        bvars = {var_of(l) for l in blits}
        bvars |= {alias[v] for v in bvars if v in alias}
        undef = [l for l in blits if var_of(l) in sel_vars and var_of(l) not in defined]
        near = set(no_var) if not loose else set()
        for v in bvars:
            near.update(by_var.get(v, ()))
        order = [(i, cands[i], cvars[i]) for i in sorted(near)]
        if undef:
            # A row that will DEFINE a selector takes the candidate sharing the most of its
            # variables first (T8, D-0182). Found on 2014_amaze: int_eq_reif(x, y, b)'s first
            # selector row, guarded by b, is also implied (by weakening) by the flag row of
            # ANOTHER constraint over x and y that does not name b; defining _neN as that
            # flag left the selector's second row underivable. The flag of the constraint
            # that names b too is the one both rows follow from.
            order.sort(key=lambda t: -len(t[2] & bvars))
        for i, (rpn, row, deps), cv in order:
            if loose and (cv <= bvars or not cv & bvars or undef):
                continue
            if not loose and not cv <= bvars:
                continue
            if any(Y in alias for Y in bcoefs):
                rpn2, row2, _ = replaced(rpn, row, [], flag_swap)
                rpn2, row2 = onto_copies(rpn2, row2, bcoefs)
                rl, rd = lit_form(*row2)
                if any(not is_flag(var_of(l)) and var_of(l) not in bagvars for l in rl):
                    continue   # an atom with no baguette literal of its own
            else:
                got = swapped(i)
                if got is None:
                    continue
                rpn2, rl, rd = got
            unk = [l for l in rl if is_flag(var_of(l))]
            if not unk and not undef:
                rpn3, rl3 = saturate(rpn2, rl, rd)
                if implies(rl3, rd, blits, bd):
                    yield rpn3, deps, None, None
                    continue
                tw = tight(rl3, rd, blits, bd)
                if tw:
                    yield rpn3, deps, None, tw
                    continue
                for resolve in (False, True):
                    got = tighten(rpn2, rl, rd, blits, resolve)
                    if got and implies(got[1], got[2], blits, bd):
                        yield got[0], deps + got[3], None, None
                        break
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
                    yield rpn3, deps, (s_, F), None
                else:
                    tw = tight(trial, rd, blits, bd)
                    if tw:
                        yield rpn3, deps, (s_, F), tw

    def const_pin(bl, bd):
        """A row a selector defined as a CONSTANT implies by itself: c * lit with lit the
        selector's true literal and c >= the degree (T8, D-0182). The pin is `ia` against
        `pol @D0 c *` (c * lit >= c), since `lit >= 1` alone does not imply the row
        syntactically when c > 1. Returns the rpn, or None."""
        for L, c in bl.items():
            v = var_of(L)
            if defined.get(v) in ("F", "T") and c >= bd:
                if (defined[v] == "F") == L.startswith("~"):
                    return [f"@D0[{v}]"] + ([str(c), "*"] if c > 1 else [])
        return None

    def find(coefs, d):
        bl, bd = lit_form(coefs, d)
        found = match(bl, bd, coefs) if cands else None
        if not found and cands and not (bd == 1 and all(a == 1 for a in bl.values())):
            found = match(bl, bd, coefs, loose=True)
        return found

    # CHOICE GROUPS BY POSITION (D-0262). baguette mints one `_mxN` per operand, in operand
    # order, and its clause over them in that order; the k-th is cake's k-th flag. Guessing it
    # from the first flag that derives the selector's rows (below) took a constant operand's
    # flag, which cake forces, for another operand's selector (array_int_maximum over
    # [x1, x0, -1]: _mx0 := x[c1][2], then _mx2's row and the clause had no derivation). The
    # group's cake constraint is the one whose choice rows, operand by operand, name the same
    # variables as baguette's selector rows (the result, and the operand unless a constant).
    base_to_cake = {info["x"]: X for X, info in ivars.items()}

    def cake_vars_bag(coefs):
        out = set()
        for v in coefs:
            mm = re.fullmatch(r"(.+)_(?:ge_m?\d+|bit_\d+)", v)
            if mm and mm.group(1) in base_to_cake:
                out.add(base_to_cake[mm.group(1)])
        return out

    cake_rows_by_label = {lab: (terms, op, rhs) for lab, terms, op, rhs in cake if lab}
    choice_groups = {}   # cake constraint -> its flags, in operand order
    for lab in cake_rows_by_label:
        mm = re.fullmatch(r"c\[(.+)\]\[al1\]", lab)
        if mm:
            fl = [v for _, v in cake_rows_by_label[lab][0]]
            if all(f"{F}[r]" in cake_rows_by_label for F in fl):
                choice_groups[mm.group(1)] = fl
    sel_row = {}
    for _, terms, op, rhs in bag:
        coefs, d = var_form(terms, op, rhs)
        mxs = [v for v in coefs if v in mx_vars]
        if len(mxs) == 1 and mxs[0] not in sel_row:
            sel_row[mxs[0]] = cake_vars_bag(coefs)
    used = set()
    for _, terms, op, rhs in bag:
        coefs, d = var_form(terms, op, rhs)
        group = [v for _, v in terms]
        if not (d == 1 and len(group) > 1 and all(c == 1 for c in coefs.values())
                and all(v in mx_vars for v in group) and all(v in sel_row for v in group)):
            continue
        for cK, fl in choice_groups.items():
            if cK in used or len(fl) != len(group):
                continue
            if all(sel_row[g] == {owner.get(v.lstrip("~"), None) for _, v in cake_rows_by_label[f"{F}[r]"][0]} - {None}
                   for g, F in zip(group, fl)):
                used.add(cK)
                for s_, F in zip(group, fl):
                    define(s_, F)
                    cj = conj_of(s_, F)
                    if cj:
                        conj[s_] = cj
                        k = len(cj[1])
                        emit(f"@C1[{s_}] red +{k + 1} ~{s_} +1 {F} {' '.join('+1 ~' + g for g in cj[1])} >= {k + 1} : {s_} -> 0 ;")
                        emit(f"@C2[{s_}] red +1 {s_} +1 ~{F} {' '.join('+1 ' + g for g in cj[1])} >= 1 : {s_} -> 1 ;")
                        emit(f"@D1[{s_}] pol @C1[{s_}] {' '.join(g + ' w' for g in cj[1])} s ;")
                    else:
                        emit(f"@D1[{s_}] red +1 ~{s_} +1 {F} >= 1 : {s_} -> {F} ;")
                        emit(f"@D2[{s_}] red +1 {s_} +1 {neg(F)} >= 1 : {s_} -> {F} ;")
                break

    # SELECTORS, each defined once against ALL its rows (T8, D-0182). A `_neN` selector
    # stands in two rows of baguette's .opb (A and B of one disequality). The first row
    # alone can be implied, by weakening, by the flag of ANOTHER constraint over the same
    # variables, and a definition chosen from it leaves the second row underivable (found
    # on 2014_amaze, int_eq_reif). So a definition is tried against every row of the
    # selector before it is kept: the flag the first row's match proposes, then the
    # constants (int_eq_reif(x, u, b) with u x's upper bound: baguette's `x > u` half is
    # impossible, cake writes no flag for it, and `_neN := 0` is the definition, a red
    # unit `~s >= 1 : s -> 0`), and only then the old greedy rule.
    groups = {}
    for _, terms, op, rhs in bag:
        coefs, d = var_form(terms, op, rhs)
        for v in coefs:
            if v in sel_vars:
                groups.setdefault(v, []).append((coefs, d))
    for s_, rows in groups.items():
        if s_ in defined:
            continue
        # every flag the first row proposes (on 2011_fillomino, int_ne(x, 12)'s own flag came
        # after another constraint's over x that fitted the first row only), then constants
        tries = []
        # D-0262: the proposals come from the selector's first row that is not TRUE outright
        # (degree <= 0 in literal form): a constant term or an impossible half makes one, any
        # candidate implies it, and the first flag met was another constraint's (int_lin_ne
        # beside an int_eq_reif over the same two variables: `_ne0 := b[c4][lt]`)
        rows = sorted(rows, key=lambda r: lit_form(*r)[1] <= 0)
        bl0, bd0 = lit_form(*rows[0])
        for loose in (False, True):
            for got in matches(bl0, bd0, rows[0][0], loose):
                if got[2] and got[2][1] not in tries:
                    tries.append(got[2][1])
                if len(tries) >= 64:
                    break
        tries += ["F", "T"]
        for F in tries:
            define(s_, F)
            cj = conj_of(s_, F) if F not in ("F", "T") else None
            if cj:
                conj[s_] = cj

            def sel_clause(c, d):
                return cj and d == 1 and all(v in mx_vars and a == 1 for v, a in c.items())

            if all(const_pin(*lit_form(c, d)) or sel_clause(c, d) or find(c, d) for c, d in rows):
                if F in ("F", "T"):
                    emit(f"@D0[{s_}] red +1 {'~' if F == 'F' else ''}{s_} >= 1 : {s_} -> {0 if F == 'F' else 1} ;")
                elif cj:
                    k = len(cj[1])
                    emit(f"@C1[{s_}] red +{k + 1} ~{s_} +1 {F} {' '.join('+1 ~' + g for g in cj[1])} >= {k + 1} : {s_} -> 0 ;")
                    emit(f"@C2[{s_}] red +1 {s_} +1 ~{F} {' '.join('+1 ' + g for g in cj[1])} >= 1 : {s_} -> 1 ;")
                    emit(f"@D1[{s_}] pol @C1[{s_}] {' '.join(g + ' w' for g in cj[1])} s ;")
                else:
                    emit(f"@D1[{s_}] red +1 ~{s_} +1 {F} >= 1 : {s_} -> {F} ;")
                    emit(f"@D2[{s_}] red +1 {s_} +1 {neg(F)} >= 1 : {s_} -> {F} ;")
                break
            conj.pop(s_, None)
            undefine(s_)

    by_coefs = {}   # a substituted row's coefficients -> (label, degree), for the exact pin
    for lab, c2, d2 in bound_pins + subst:   # a bits bound row against its own @BL/@BU first
        by_coefs.setdefault(frozenset(c2.items()), []).append((lab, d2))

    pins = []
    for label, terms, op, rhs in bag:
        coefs, d = var_form(terms, op, rhs)
        line = row_text(terms, op, rhs)
        cp = const_pin(*lit_form(coefs, d))
        if cp:
            if len(cp) == 1:
                pins.append(f"@{label} ia {line} : {cp[0]} ;")
            else:
                nw[0] += 1
                emit(f"@W[{nw[0]}] pol {' '.join(cp)} ;")
                pins.append(f"@{label} ia {line} : @W[{nw[0]}] ;")
            continue
        m = re.fullmatch(r"\+1 ~(\S+)_ge_(m?\d+) \+1 (\S+)_ge_(m?\d+) >= 1", line)
        if m and m.group(1) == m.group(3) and pv(m.group(2)) == pv(m.group(4)) + 1:
            pins.append(f"@{label} ia {line} : @L[{m.group(1)}_ge_{m.group(2)}] ;")
            continue
        if d == 0 and frozenset(coefs.items()) in copy_eq:
            nw[0] += 1
            emit(f"@W[{nw[0]}] pol {copy_eq[frozenset(coefs.items())]} ;")
            pins.append(f"@{label} ia {line} : @W[{nw[0]}] ;")
            continue
        hit = next((lab for lab, d2 in by_coefs.get(frozenset(coefs.items()), ()) if d2 >= d), None)
        if hit:
            pins.append(f"@{label} ia {line} : {hit} ;")
            continue
        found = match(*lit_form(coefs, d), coefs) if cands else None
        bl, bd = lit_form(coefs, d)
        if not found and cands and not (bd == 1 and all(a == 1 for a in bl.values())):
            found = match(bl, bd, coefs, loose=True)
        if found:
            rpn, deps, new, tw = found
            if new:
                s_, F = new
                define(s_, F)
                emit(f"@D1[{s_}] red +1 ~{s_} +1 {F} >= 1 : {s_} -> {F} ;")
                emit(f"@D2[{s_}] red +1 {s_} +1 {neg(F)} >= 1 : {s_} -> {F} ;")
            for dep in deps:
                ensure(dep)
            if tw:
                # T7 (D-0196): the big-M over the bits' declared bounds, by contradiction
                pins.append(f"@{label} pbc {line} : subproof\n    pol -1 {' '.join(rpn)} + s ;\n"
                            f"    pol -2 {' '.join(tw)} + ;\n    rup >= 1 ;\nqed ;")
                continue
            if len(rpn) == 1:
                pins.append(f"@{label} ia {line} : {rpn[0]} ;")
            else:
                nw[0] += 1
                emit(f"@W[{nw[0]}] pol {' '.join(rpn)} ;")
                pins.append(f"@{label} ia {line} : @W[{nw[0]}] ;")
            continue
        if not (bd == 1 and all(a == 1 for a in bl.values())):
            # a row that holds in both signs of an int_abs (z >= x, z >= -x, the hull rows):
            # by contradiction (D-0195 2.3). The negation plus each of the constraint's
            # guarded rows, saturated, is a unit on the guard or nothing, and rup closes
            bvars = {var_of(l) for l in bl}
            sums = []
            for rpn, row, deps in cands:
                if not ABS.fullmatch(rpn[0]):
                    continue
                if not {var_of(l) for l in lit_form(*row)[0]} & bvars:
                    continue
                for dep in deps:
                    ensure(dep)
                sums.append(rpn)
            if sums:
                body = [f"@{label} pbc {line} : subproof"]
                for k, rpn in enumerate(sums):
                    body.append(f"    pol -{k + 1} {' '.join(rpn)} + s ;")
                body += ["    rup >= 1 ;", "qed ;"]
                pins.append("\n".join(body))
                continue
        pins.append(f"@{label} rup {line} ;")
    out.extend(pins)

    # baguette's proof is STREAMED (a search proof can be gigabytes, T8)
    pbp = open(bag_pbp)
    head = [pbp.readline().rstrip("\n"), pbp.readline().rstrip("\n")]
    if not (head[0].startswith("pseudo-Boolean proof version") and head[1].startswith("f ")):
        raise SystemExit("bridge: baguette's proof does not start with its header and `f N`")
    w = sys.stdout.write
    w(head[0] + "\n")
    w(f"f {len(cake)} ;\n")
    w("\n".join(out) + "\n")
    for line in pbp:
        if "soli" not in line:
            w(line)
            continue
        line = line.rstrip("\n")
        m = re.match(r"(@\S+ )?soli\b(.*)$", line)
        if not m:
            w(line + "\n")
            continue
        if obj_fix is None:
            raise SystemExit("bridge: a `soli` line, and no objective on both sides")
        if not m.group(1):
            raise SystemExit("bridge: an unlabelled `soli` line")
        lab = m.group(1).strip()
        half, k = obj_fix
        w(f"@O[{lab[1:]}] soli{m.group(2)}\n")
        w(f"{lab} pol @O[{lab[1:]}] {half} {k} * + ;\n" if k else f"{lab} pol @O[{lab[1:]}] ;\n")


def objective(cake_opb, bag_lines, ivars, owner):
    """(the half to add, its multiplier) for each soli, or None without an objective."""
    def terms_of(lines):
        got = [l.strip() for l in lines if l.strip().startswith("min:")]
        if not got:
            return None
        body = got[0][4:].rstrip(";")
        terms = TERM.findall(body)
        rest = TERM.sub("", body).split()
        if len(rest) > 1 or (rest and not re.fullmatch(r"[+-]?\d+", rest[0])):
            raise SystemExit(f"bridge: cannot read the objective {got[0]!r}")
        return {v: int(c) for c, v in terms}, int(rest[0]) if rest else 0
    cobj = terms_of(open(cake_opb).read().splitlines())
    bobj = terms_of(bag_lines)
    if cobj is None and bobj is None:
        return None
    if cobj is None or bobj is None:
        raise SystemExit("bridge: an objective on one side only")
    (ct, cc), (bt, bc) = cobj, bobj
    if not ct and not bt and cc == 0 and bc == 0:
        # D-0262: an objective over a FIXED variable (`var 0..0`), empty on both sides; every
        # `soli`'s improving constraint is then the same row on both, carried over unchanged
        return ("", 0)
    Xs = {owner.get(b) for b in ct}
    if len(Xs) != 1 or None in Xs or cc != 0:
        raise SystemExit("bridge: cake's objective is not one variable's bit sum")
    X = Xs.pop()
    info = ivars[X]
    if set(ct) != set(info["bits"]):
        raise SystemExit(f"bridge: cake's objective names only part of {X}'s bits")
    ks = {ct[b] // info["bits"][b] for b in ct if ct[b] % info["bits"][b] == 0}
    if len(ks) != 1 or len(ct) != sum(1 for b in ct if ct[b] % info["bits"][b] == 0):
        raise SystemExit("bridge: cake's objective is not a multiple of one bit sum")
    k = ks.pop()
    want = {s: k * w for s, w in info["W"].items()}
    if bt != want or bc != k * info["l"]:
        raise SystemExit(f"bridge: baguette's objective is not {k} * {info['x']}")
    return (info["e1"], k) if k > 0 else (info["e2"], -k)


if __name__ == "__main__":
    if len(sys.argv) != 5:
        print(__doc__.splitlines()[2], file=sys.stderr)
        sys.exit(64)
    main(*sys.argv[1:5])
