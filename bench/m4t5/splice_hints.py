#!/usr/bin/env python3
"""splice.py ORIG.pbp ELAB.pbp OUT.pbp [mode]
Give ORIG's n-th top-level `rup` the hint list of ELAB's n-th top-level `rup`
(VeriPB's elaboration = the checker's own propagation trail, d5644ca4).
Elaboration RENUMBERS (a `red` grows a subproof and takes 2 ids), so elab ids are
mapped back to ORIG's labels through the deletion lines, which align position by
position (I-X2: every derived id is deleted), plus the conclusion.  Ids <= f N are
formula ids, the same in both.  Claims must match term for term, else abort.
mode: 'full' | 'drop1:<k>' drop the last non-~ hint of rup #k (corruption lane)."""
import sys, re
orig, elab, out = sys.argv[1:4]
mode = sys.argv[4] if len(sys.argv) > 4 else 'full'
drop_k = int(mode.split(':')[1]) if mode.startswith('drop1:') else None
def terms(body):
    lhs, rhs = body.split('>=')
    t = lhs.split()
    return sorted((int(t[i].lstrip('+')), t[i+1]) for i in range(0, len(t), 2)), int(rhs)
lab = re.compile(r'^(@\S+\s+)?rup\s')
# pass 1: ORIG deletions, conclusion, f
odel = []; oconc = None; nf = None; olabels = []
for line in open(orig):
    if line.startswith('@'): olabels.append(line.split()[0])
    if line.startswith('del id '):
        odel += line[7:].rstrip().rstrip(';').split()
    elif line.startswith('del range '):
        a, b = line[10:].rstrip().rstrip(';').split()
        odel += ['@c%d' % k for k in range(int(a[2:]), int(b[2:]))]
    elif line.startswith('del '):
        sys.exit('unhandled del form: ' + line)
    elif line.startswith('conclusion') and ':' in line:
        oconc = line.split(':')[1].strip().rstrip(';').split()[0]
    elif line.startswith('f '):
        nf = int(line.split()[1])
# pass 2: ELAB top-level rups, deletions
erups = []; edel = []; econc = None; depth = 0; eids = []; ctr = None
for line in open(elab):
    s = line.strip()
    if s.startswith('f '): ctr = int(s[2:].rstrip(';'))
    if depth == 0:
        kw = s.split(' ', 1)[0]
        if kw == 'red' and s.endswith(': subproof'): ctr += 2; eids.append(str(ctr))
        elif kw in ('rup', 'pol', 'ia', 'soli', 'red', 'a'): ctr += 1; eids.append(str(ctr))
        elif kw in ('pbc',): sys.exit('pbc not handled')
    if depth == 0 and s.startswith('rup '):
        body, _, hint = s[4:].rstrip(';').partition(' : ')
        erups.append((terms(body), hint.split()))
    elif depth == 0 and s.startswith('deld '):
        edel += s[5:].rstrip(';').split()
    elif depth == 0 and s.startswith('del'):
        sys.exit('unhandled elab del form: ' + s)
    elif depth == 0 and s.startswith('conclusion') and ':' in s:
        econc = s.split(':')[1].strip().rstrip(';').split()[0]
    if s.endswith(': subproof') or s.startswith('subproof') or (s.startswith('proofgoal')):
        depth += 1
    if s.startswith('qed') or s.startswith('end subproof'):
        depth -= 1
if len(odel) != len(edel): sys.exit(f'deletion lengths differ {len(odel)} {len(edel)}')
m = dict(zip(edel, odel))
if econc and oconc: m[econc] = oconc
if len(eids) != len(olabels): sys.exit(f'creating-line counts differ {len(eids)} {len(olabels)}')
m2 = dict(zip(eids, olabels))
for k, v in m.items():
    if m2.get(k) != v: sys.exit(f'numbering check failed: elab {k} -> del says {v}, sequence says {m2.get(k)}')
m = m2
def mapid(x):
    if x == '~': return x
    if int(x) <= nf: return x
    if x not in m: raise KeyError(x)
    return m[x]
n = added = 0; unmapped = 0
with open(orig) as f, open(out, 'w') as g:
    for line in f:
        if lab.match(line):
            s = line.rstrip('\n'); pre, _, rest = s.partition('rup ')
            body = rest.rstrip(); assert body.endswith(';'), s
            body = body[:-1].rstrip(); assert ' : ' not in body, s
            et, h = erups[n]; n += 1
            if terms(body) != et: sys.exit(f'claim mismatch at rup #{n}: {s!r} vs {et}')
            try: h = [mapid(x) for x in h]
            except KeyError as e: sys.exit(f'unmapped elab id {e} at rup #{n}')
            if drop_k == n:
                i = max(j for j, x in enumerate(h) if x != '~')
                print('dropped', h[i], 'from rup', n, file=sys.stderr); del h[i]
            new = f'{pre}rup {body} : {" ".join(h)} ;\n'
            added += len(new) - len(line); g.write(new)
        else:
            g.write(line)
if n != len(erups): sys.exit(f'rup count differs {n} {len(erups)}')
print(f'rups={n} hint_bytes={added}')
