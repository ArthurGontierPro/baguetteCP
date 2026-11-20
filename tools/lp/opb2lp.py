#!/usr/bin/env python3
"""opb2lp.py -- the root LP relaxation of a baguette .opb, and what it would fix (M13-codes-leads-T1, D-0183).

A STUDY instrument, not part of the solver. It reads the PB model baguette writes (PROOF-FORMAT §3:
order literals `x_ge_v`, bits `x_bit_i`, plain Booleans, the ladder rows, every model row as `>=`,
the objective as a `min:` line over the objective's order literals), relaxes every Boolean to
0 <= x <= 1, solves the LP with HiGHS (highspy), and reports:

  - the PB bound propagation fixpoint of the same rows (a stand-in for the solver's root
    propagation over its PB model) and the objective lower bound it gives;
  - LP0, the pure relaxation (box [0,1]): its bound, or its infeasibility (a Farkas ray, which
    would be a root UNSAT proof);
  - LP1, the relaxation with the propagated literals fixed: its bound, and the share of the gap
    between the propagation bound and the incumbent UB (--ub) it closes;
  - with the cutoff `obj <= UB - 1`: what propagation already fixes, whether the LP then proves
    UB optimal, else the reduced-cost fixings and what propagation draws from them (rc_fixings);
  - with --cert K: for the bound and for K reduced-cost fixings of LP0, the `pol` that derives
    each, with the duals made exact (see `certificate`), every coefficient verified in integers
    before anything is written.

usage: opb2lp.py MODEL.opb [--ub UB] [--lp-out F.lp] [--cert K --cutoff @label --cert-out F]
                           [--name NAME] [--time-limit S]
prints one JSON object on stdout.
"""
import sys, os, time, json, argparse, math
from bisect import bisect_right
from fractions import Fraction
import numpy as np
import highspy


# ------------------------------------------------------------------------------------------ parse
def parse_opb(path):
    """Rows in x-space: sum a_j x_j >= b with x_j in {0,1}; a literal ~x is 1 - x."""
    names, index = [], {}
    rows, labels = [], []
    obj, obj_k0, obj_lits, obj_c0 = {}, 0, [], 0

    def var(n):
        j = index.get(n)
        if j is None:
            j = index[n] = len(names)
            names.append(n)
        return j

    def terms(toks):
        coef, k = {}, 0
        lits = []
        for i in range(0, len(toks), 2):
            a = int(toks[i]); lit = toks[i + 1]
            lits.append((a, lit))
            if lit[0] == '~':
                j = var(lit[1:]); coef[j] = coef.get(j, 0) - a; k += a
            else:
                j = var(lit); coef[j] = coef.get(j, 0) + a
        return coef, k, lits

    with open(path) as f:
        for line in f:
            if not line or line[0] == '*':
                continue
            line = line.strip()
            if not line:
                continue
            if line.startswith('min:'):
                toks = line[4:].rstrip(';').split()
                if len(toks) % 2:                # a trailing constant: the objective's lower bound
                    obj_c0 = int(toks[-1]); toks = toks[:-1]
                obj, obj_k0, obj_lits = terms(toks)
                obj_k0 += obj_c0
                continue
            toks = line.rstrip(';').split()
            label = None
            if toks[0].startswith('@'):
                label = toks[0]; toks = toks[1:]
            op, rhs = toks[-2], int(toks[-1])
            coef, k, _ = terms(toks[:-2])
            if op == '>=':
                rows.append((coef, rhs - k)); labels.append(label)
            elif op == '=':
                rows.append((coef, rhs - k)); labels.append(label)
                rows.append(({j: -a for j, a in coef.items()}, -(rhs - k))); labels.append(label + '~' if label else None)
            else:
                raise ValueError(f"unsupported relation {op!r}")
    return names, rows, labels, obj, obj_k0, obj_lits, obj_c0


# ------------------------------------------------------------------------------------ propagation
class Prop:
    """Bounds propagation over the .opb rows AT THE INTEGER LEVEL, a stand-in for the solver's
    root propagation of the same rows. A literal `X_ge_v` is read back as (X, v) (PROOF-FORMAT §3:
    the order encoding; a name without `_ge_` is a 0..1 variable of its own). A row's terms on X
    are the step function f_X(x) = sum of c_v over v <= x; a row is sum_X f_X(X) >= b and each X is
    narrowed to the values where f_X reaches b minus the others' maximum. Plain literal-level PB
    propagation sees nothing on an order-encoded linear row (every literal has the same
    coefficient), which is why this reads the ladder back into intervals."""

    def __init__(self, names, rows):
        self.ivar, self.lit = {}, []
        lmin, lmax = [], []
        for nm in names:
            if '_ge_' in nm:
                x, v = nm.rsplit('_ge_', 1)
                try:
                    v = int(v)
                except ValueError:
                    x, v = nm, 1
            else:
                x, v = nm, 1
            X = self.ivar.get(x)
            if X is None:
                X = self.ivar[x] = len(lmin); lmin.append(v); lmax.append(v)
            lmin[X] = min(lmin[X], v); lmax[X] = max(lmax[X], v)
            self.lit.append((X, v))
        self.l = [m - 1 for m in lmin]; self.u = lmax
        self.cnt = [0] * len(lmin)
        for X, v in self.lit:
            self.cnt[X] += 1
        self.rows, self.occ = [], [[] for _ in lmin]
        for coef, b in rows:
            self.add_row(coef, b)

    def add_row(self, coef, b):
        g = {}
        for j, a in coef.items():
            X, v = self.lit[j]
            g.setdefault(X, []).append((v, a))
        ent = []
        for X, lst in g.items():
            lst.sort()
            vs = [v for v, _ in lst]
            P = [0]
            for _, c in lst:
                P.append(P[-1] + c)
            c0 = lst[0][1]
            uni = (len(lst) == self.u[X] - self.l[X] and all(c == c0 for _, c in lst))
            ent.append((X, vs, P, c0 if uni else None))
            self.occ[X].append(len(self.rows))
        self.rows.append((ent, b))

    def pop_row(self):
        ent, _ = self.rows.pop()
        for X, *_ in ent:
            self.occ[X].pop()

    def box(self):
        return self.l[:], self.u[:]

    @staticmethod
    def segs(e, lo, hi, l):
        X, vs, P, c = e
        i0 = bisect_right(vs, lo); i1 = bisect_right(vs, hi)
        out = [(lo, vs[i0] - 1 if i0 < i1 else hi, P[i0])]
        for i in range(i0, i1):
            out.append((vs[i], vs[i + 1] - 1 if i + 1 < i1 else hi, P[i + 1]))
        return out

    def fmax(self, e, lo, hi):
        X, vs, P, c = e
        if c is not None:
            return c * ((hi if c > 0 else lo) - self.l[X])
        return max(v for _, _, v in self.segs(e, lo, hi, self.l[X]))

    def run(self, LO, HI, queue=None):
        """Mutates LO/HI. Returns (ok, number of order literals newly fixed)."""
        inq = bytearray(len(self.rows))
        queue = list(range(len(self.rows))) if queue is None else list(queue)
        for r in queue:
            inq[r] = 1
        nfix = 0
        while queue:
            r = queue.pop(); inq[r] = 0
            ent, b = self.rows[r]
            mx = [self.fmax(e, LO[e[0]], HI[e[0]]) for e in ent]
            slack = sum(mx) - b
            if slack < 0:
                return False, nfix
            for e, m in zip(ent, mx):
                X, vs, P, c = e
                lo, hi = LO[X], HI[X]
                if lo == hi:
                    continue
                need = m - slack
                if c is not None:
                    l = self.l[X]
                    if c > 0:
                        nlo, nhi = max(lo, l + -((-need) // c)), hi
                    else:
                        nlo, nhi = lo, min(hi, l + need // c)
                else:
                    if m - min(v for _, _, v in self.segs(e, lo, hi, 0)) <= slack:
                        continue
                    ok = [(s0, s1) for s0, s1, v in self.segs(e, lo, hi, 0) if v >= need]
                    nlo, nhi = ok[0][0], ok[-1][1]
                if nlo > nhi:
                    return False, nfix
                if nlo != lo or nhi != hi:
                    nfix += (nlo - lo) + (hi - nhi)
                    LO[X], HI[X] = nlo, nhi
                    for r2 in self.occ[X]:
                        if not inq[r2]:
                            inq[r2] = 1; queue.append(r2)
        return True, nfix

    def lit_box(self, LO, HI):
        lo = [1 if v <= LO[X] else 0 for X, v in self.lit]
        hi = [0 if v > HI[X] else 1 for X, v in self.lit]
        return lo, hi


def obj_min(obj, lo, hi):
    return sum(a * (lo[j] if a > 0 else hi[j]) for j, a in obj.items())


# ---------------------------------------------------------------------------------------------- LP
def build_lp(n, rows, obj, lo, hi):
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('threads', 1)
    lp = highspy.HighsLp()
    lp.num_col_ = n
    lp.num_row_ = len(rows)
    c = np.zeros(n)
    for j, a in obj.items():
        c[j] = a
    lp.col_cost_ = c
    lp.col_lower_ = np.array(lo, dtype=float)
    lp.col_upper_ = np.array(hi, dtype=float)
    lp.row_lower_ = np.array([b for _, b in rows], dtype=float)
    lp.row_upper_ = np.full(len(rows), highspy.kHighsInf)
    start, idx, val = [0], [], []
    for coef, _ in rows:
        for j, a in coef.items():
            idx.append(j); val.append(a)
        start.append(len(idx))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = np.array(start, dtype=np.int32)
    lp.a_matrix_.index_ = np.array(idx, dtype=np.int32)
    lp.a_matrix_.value_ = np.array(val, dtype=float)
    lp.a_matrix_.num_col_ = n
    lp.a_matrix_.num_row_ = len(rows)
    h.passModel(lp)
    return h


def solve(h, time_limit):
    h.setOptionValue('time_limit', float(time_limit))
    t = time.time()
    h.run()
    dt = time.time() - t
    st = h.modelStatusToString(h.getModelStatus())
    return st, dt


# ------------------------------------------------------------------------------------- certificate
def exact_multipliers(y, denom):
    """Duals made exact: each y_i >= 0 is rationalised to a fraction of denominator <= denom, the
    multipliers are the numerators over the lcm D. Soundness does not depend on how good the
    rounding is (any nonnegative combination of valid rows is valid); strength is checked after."""
    fr = {}
    for i, v in enumerate(y):
        if v > 1e-12:
            q = Fraction(float(v)).limit_denominator(denom)
            if q > 0:
                fr[i] = q
    D = 1
    for q in fr.values():
        D = D * q.denominator // math.gcd(D, q.denominator)
        if D > 10 ** 12:
            break
    if D > 10 ** 12:                      # fall back to a fixed scale, floor: still nonnegative
        D = denom
        m = {i: int(q * D) for i, q in fr.items() if int(q * D) > 0}
    else:
        m = {i: int(q * D) for i, q in fr.items()}
    return m, D


def combine(rows, m, n):
    C = {}
    R = 0
    for i, k in m.items():
        coef, b = rows[i]
        R += k * b
        for j, a in coef.items():
            C[j] = C.get(j, 0) + k * a
    return C, R


def lit(names, j, positive):
    return names[j] if positive else '~' + names[j]


def rpn_rows(labels, m):
    out = []
    first = True
    for i, k in sorted(m.items()):
        lab = labels[i]
        if lab.endswith('~'):
            raise ValueError('certificate through an = row is not written by this study')
        out.append(lab if k == 1 else f'{lab} {k} *')
        if not first:
            out.append('+')
        first = False
    return out


def cert_bound(names, rows, labels, obj, obj_k0, obj_lits, obj_c0, y, denom):
    """pol deriving  objective >= ceil(z): sum m_i row_i + literal axioms to reach D*c, divide by D."""
    n = len(names)
    m, D = exact_multipliers(y, denom)
    C, R = combine(rows, m, n)
    toks = rpn_rows(labels, m)
    # bring every coefficient to exactly D*c_j with literal axioms (x >= 0 adds, ~x >= 0 subtracts)
    for j in set(C) | set(obj):
        e = D * obj.get(j, 0) - C.get(j, 0)
        if e > 0:
            toks += [names[j], str(e), '*', '+']
        elif e < 0:
            toks += ['~' + names[j], str(-e), '*', '+']; R += e
    # now  D * c.x >= R  exactly (x-space); in literal space  sum c_t l_t >= R/D + k0 - c0
    bound_x = -((-R) // D)               # ceil(R / D)
    toks += [str(D), 'd']
    claim = ' '.join(f'{a:+d} {l}' for a, l in obj_lits) + f' >= {bound_x + obj_k0 - obj_c0}'
    return dict(D=D, support=len(m), tokens=len(toks), pol=' '.join(toks), claim=claim,
                bound=bound_x + obj_k0, bound_float=R / D + obj_k0)


def cert_fix(names, rows, labels, obj, obj_k0, y, denom, j, value, cutoff_label, ub):
    """pol deriving the reduced-cost fixing x_j = value from the rows, the cutoff obj <= UB-1, and
    literal axioms, then a division. Returns None when the rounded duals no longer imply it."""
    n = len(names)
    m, D = exact_multipliers(y, denom)
    C, R = combine(rows, m, n)
    # + D * cutoff:  -c.x >= k0 - UB + 1  (x-space)
    for k, a in obj.items():
        C[k] = C.get(k, 0) - D * a
    R += D * (obj_k0 - ub + 1)
    toks = rpn_rows(labels, m) + [cutoff_label, str(D), '*', '+']
    for k in list(C):
        if k == j:
            continue
        e = C[k]
        if e > 0:            # e x_k <= e: add e ~x_k (axiom) -> constant e, rhs - e
            toks += ['~' + names[k], str(e), '*', '+']; R -= e
        elif e < 0:          # -|e| x_k: add |e| x_k -> 0
            toks += [names[k], str(-e), '*', '+']
    if j is None:            # every term weakened away: 0 >= R, a contradiction when R > 0
        if R > 0:
            return dict(D=D, support=len(m) + 1, tokens=len(toks), pol=' '.join(toks), claim='>= 1')
        return None
    a = C.get(j, 0)
    # a x_j >= R. value 0 needs a < 0 and R > a (then ~x_j forced); value 1 needs a > 0 and R > 0
    if value == 0 and a < 0 and R > a:
        toks += [str(-a), 'd']
        return dict(D=D, support=len(m) + 1, tokens=len(toks), pol=' '.join(toks), claim=f'+1 ~{names[j]} >= 1')
    if value == 1 and a > 0 and R > 0:
        toks += [str(a), 'd']
        return dict(D=D, support=len(m) + 1, tokens=len(toks), pol=' '.join(toks), claim=f'+1 {names[j]} >= 1')
    return None


# -------------------------------------------------------------------------------------- RC fixing
def rc_fixings(R, sfx, ub, names, rows, obj, obj_k0, PR, LO, HI, time_limit):
    """What the cutoff obj <= ub - 1 (integer objective) adds at the root, in three steps:
      1. bounds propagation of the model rows plus the cutoff row, from the root fixpoint
         (what the solver already gets once it holds the incumbent; a conflict proves ub optimal);
      2. the LP over those bounds: infeasible, or z > ub - 1, proves ub optimal at the root;
      3. otherwise reduced-cost fixing: a free literal at its lower bound with d_j > (ub-1) - z
         cannot be 1 in an improving solution, symmetrically at its upper bound; then bounds
         propagation again, to count what the fixings imply.
    Only step 3's literals (and what they imply) are counted as the LP's fixings."""
    n = len(names)
    cut = ({j: -a for j, a in obj.items()}, obj_k0 - ub + 1)        # -c.x >= k0 - ub + 1
    PR.add_row(*cut)
    try:
        LO1, HI1 = LO[:], HI[:]
        ok, nf = PR.run(LO1, HI1, queue=[len(PR.rows) - 1])
        R.update({'ub' + sfx: ub, 'cut_prop_fixed' + sfx: nf})
        if not ok:
            R['proved_opt' + sfx] = 'prop'
            return
        lo1, hi1 = PR.lit_box(LO1, HI1)
        h = build_lp(n, rows, obj, lo1, hi1)
        st, dt = solve(h, time_limit)
        R.update({'lpc_status' + sfx: st, 'lpc_s' + sfx: round(dt, 2)})
        if st == 'Infeasible':
            R['proved_opt' + sfx] = 'lp'
            return
        if st != 'Optimal':
            return
        z = h.getInfo().objective_function_value + obj_k0
        R['lpc_bound' + sfx] = z
        gap = (ub - 1) - z
        R['rc_gap' + sfx] = gap
        if gap < -1e-6:
            R['proved_opt' + sfx] = 'lp'
            return
        d = h.getSolution().col_dual
        LO2, HI2 = LO1[:], HI1[:]
        fixed = 0
        touched = set()
        for j in range(n):
            if lo1[j] == hi1[j]:
                continue
            X, v = PR.lit[j]
            if d[j] > gap + 1e-6:
                HI2[X] = min(HI2[X], v - 1)
            elif -d[j] > gap + 1e-6:
                LO2[X] = max(LO2[X], v)
            else:
                continue
            fixed += 1; touched.add(X)
        narrow = sum((LO2[X] - LO1[X]) + (HI1[X] - HI2[X]) for X in touched)
        R.update({'free_after_cut' + sfx: sum(1 for j in range(n) if lo1[j] != hi1[j]),
                  'rc_fixed' + sfx: fixed, 'rc_narrow' + sfx: narrow, 'rc_intvars' + sfx: len(touched)})
        if any(LO2[X] > HI2[X] for X in touched):
            R['proved_opt' + sfx] = 'lp+rc'
            return
        if fixed:
            qs = sorted({r for X in touched for r in PR.occ[X]})
            ok2, more = PR.run(LO2, HI2, queue=qs)
            R.update({'rc_prop_more' + sfx: more})
            if not ok2:
                R['proved_opt' + sfx] = 'lp+rc+prop'
    finally:
        PR.pop_row()


def mip_root(R, a, n, rows, obj, obj_k0):
    """For comparison only: HiGHS's own root, with its presolve, cuts and heuristics, no branching."""
    hm = build_lp(n, rows, obj, [0] * n, [1] * n)
    hm.changeColsIntegrality(n, np.arange(n, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * n))
    hm.setOptionValue('mip_max_nodes', 1)
    stm, dtm = solve(hm, a.mip_root)
    inf = hm.getInfo()
    R.update(mip_root_status=stm, mip_root_s=round(dtm, 2),
             mip_root_bound=inf.mip_dual_bound + obj_k0 if obj else None,
             mip_root_primal=(inf.objective_function_value + obj_k0) if obj and inf.primal_solution_status else None)


def mip_solution(R, a, names, rows, obj, obj_k0):
    """An incumbent for the certificate check: HiGHS MIP on the .opb, its best 0/1 point written as
    `@lpsol soli <every literal>` (the checker re-verifies it against every row)."""
    n = len(names)
    hm = build_lp(n, rows, obj, [0] * n, [1] * n)
    hm.changeColsIntegrality(n, np.arange(n, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * n))
    st, dt = solve(hm, a.time_limit)
    inf = hm.getInfo()
    R.update(sol_status=st, sol_s=round(dt, 2))
    if not inf.primal_solution_status:
        return
    x = hm.getSolution().col_value
    val = sum(a_ * round(x[j]) for j, a_ in obj.items()) + obj_k0
    R.update(sol_value=val, sol_dual_bound=inf.mip_dual_bound + obj_k0)
    with open(a.sol_out, 'w') as f:
        f.write('@lpsol soli ' + ' '.join(names[j] if x[j] > 0.5 else '~' + names[j] for j in range(n)) + ' ;\n')


# -------------------------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('opb')
    ap.add_argument('--ub', type=int, default=None, help='incumbent objective value (cutoff obj <= UB-1)')
    ap.add_argument('--ub2', type=int, default=None, help='a second cutoff, e.g. the best known value')
    ap.add_argument('--lp-out', default=None)
    ap.add_argument('--name', default=None)
    ap.add_argument('--time-limit', type=float, default=600)
    ap.add_argument('--cert', type=int, default=0)
    ap.add_argument('--cutoff', default=None, help='proof label of the objective-improving constraint obj <= UB-1')
    ap.add_argument('--cert-out', default=None)
    ap.add_argument('--denom', type=int, default=10 ** 6)
    ap.add_argument('--mip-root', type=float, default=0,
                    help='also run HiGHS MIP at the root only (mip_max_nodes=1) for S seconds: the bound after its cuts')
    ap.add_argument('--sol-out', default=None,
                    help='solve the MIP for --time-limit seconds and write its best solution as a `soli` line')
    ap.add_argument('--mip-only', action='store_true', help='parse, then only the --mip-root run (a crash there loses nothing else)')
    a = ap.parse_args()

    R = dict(name=a.name or os.path.basename(a.opb), opb_bytes=os.path.getsize(a.opb))
    t = time.time()
    names, rows, labels, obj, obj_k0, obj_lits, obj_c0 = parse_opb(a.opb)
    n = len(names)
    R.update(parse_s=round(time.time() - t, 2), nvars=n, nrows=len(rows),
             nnz=sum(len(c) for c, _ in rows), has_obj=bool(obj))
    R['triv_bound'] = obj_min(obj, [0] * n, [1] * n) + obj_k0 if obj else None
    if a.sol_out:
        mip_solution(R, a, names, rows, obj, obj_k0)
        print(json.dumps(R))
        return
    if a.mip_only:
        mip_root(R, a, n, rows, obj, obj_k0)
        print(json.dumps(R))
        return

    t = time.time()
    PR = Prop(names, rows)
    LO, HI = PR.box()
    ok, nfix = PR.run(LO, HI)
    R.update(prop_s=round(time.time() - t, 2), prop_ok=ok, prop_fixed=nfix, nintvars=len(LO))
    lo, hi = PR.lit_box(LO, HI) if ok else ([0] * n, [1] * n)
    if ok and obj:
        R['prop_bound'] = obj_min(obj, lo, hi) + obj_k0

    # LP0: the pure relaxation of the model rows
    h0 = build_lp(n, rows, obj, [0] * n, [1] * n)
    if a.lp_out:
        h0.writeModel(a.lp_out)
    st0, dt0 = solve(h0, a.time_limit)
    R.update(lp0_status=st0, lp0_s=round(dt0, 2))
    if st0 == 'Optimal':
        R['lp0_bound'] = h0.getInfo().objective_function_value + obj_k0
    elif st0 == 'Infeasible':
        R['lp0_farkas'] = True

    # LP1: with the propagated literals fixed, and its reduced-cost fixings
    if ok:
        h1 = build_lp(n, rows, obj, lo, hi)
        st1, dt1 = solve(h1, a.time_limit)
        R.update(lp1_status=st1, lp1_s=round(dt1, 2))
        if st1 == 'Optimal' and obj:
            z = h1.getInfo().objective_function_value
            R['lp1_bound'] = z + obj_k0
            if R.get('prop_bound') is not None and a.ub is not None and a.ub > R['prop_bound']:
                R['gap_closed'] = round((R['lp1_bound'] - R['prop_bound']) / (a.ub - R['prop_bound']), 4)
            for ub, sfx in ((a.ub, ''), (a.ub2, '2')):
                if ub is not None and not (sfx == '2' and ub == a.ub):
                    rc_fixings(R, sfx, ub, names, rows, obj, obj_k0, PR, LO, HI, a.time_limit)
        elif st1 == 'Infeasible':
            R['lp1_farkas'] = True

    if a.mip_root > 0:
        mip_root(R, a, n, rows, obj, obj_k0)

    # certificates over LP0 (model rows + literal axioms + cutoff only)
    if a.cert and st0 == 'Optimal' and obj:
        sol = h0.getSolution()
        y = np.maximum(np.array(sol.row_dual), 0.0)
        out = []
        cb = cert_bound(names, rows, labels, obj, obj_k0, obj_lits, obj_c0, y, a.denom)
        R.update(cert_bound=cb['bound'], cert_bound_float=cb['bound_float'], cert_D=cb['D'],
                 cert_support=cb['support'], cert_tokens=cb['tokens'])
        out.append(f"@lpbound pol {cb['pol']} ;")
        out.append(f"ia {cb['claim']} : @lpbound ;")
        if a.ub is not None and a.cutoff:
            z0 = R['lp0_bound']; gap0 = (a.ub - 1) - z0
            d = sol.col_dual
            if gap0 < -1e-6:         # the LP alone proves the incumbent optimal: derive 0 >= 1
                co = cert_fix(names, rows, labels, obj, obj_k0, y, a.denom, None, None, a.cutoff, a.ub)
                R['cert_opt'] = co is not None
                if co is not None:
                    out.append(f"@lpopt pol {co['pol']} ;")
                    out.append(f"ia {co['claim']} : @lpopt ;")
                    R['cert_opt_tokens'] = co['tokens']; R['cert_opt_support'] = co['support']
            cand = [j for j in range(n) if gap0 >= -1e-6 and abs(d[j]) > gap0 + 1e-6]
            R['rc0_fixed'] = len(cand)
            ncert = 0
            for j in cand:
                cf = cert_fix(names, rows, labels, obj, obj_k0, y, a.denom, j, 0 if d[j] > 0 else 1, a.cutoff, a.ub)
                if cf is None:
                    continue
                out.append(f"@lpfix{ncert} pol {cf['pol']} ;")
                out.append(f"ia {cf['claim']} : @lpfix{ncert} ;")
                R.setdefault('cert_fix_tokens', []).append(cf['tokens'])
                ncert += 1
                if ncert >= a.cert:
                    break
            R['cert_fix'] = ncert
        if a.cert_out:
            with open(a.cert_out, 'w') as f:
                f.write('\n'.join(out) + '\n')
    print(json.dumps(R))


if __name__ == '__main__':
    main()
