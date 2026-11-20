#!/usr/bin/env python3
"""table.py OUTDIR... -- one TSV row per instance from opb2lp.py results (M13-codes-leads-T1, D-0183).

A later OUTDIR overrides an earlier one for the same name (a rerun); NAME.mip (HiGHS's root, run in
a process of its own by run_lp.sh) is merged into its row. The bounds are in the .opb's sense (a
maximisation is negated). gap_closed = (lp1 - prop) / (ub - prop): the share of the root gap,
between bounds propagation of the same rows and the incumbent, that the LP closes; gap_closed2 the
same against the best known value ub2."""
import sys, json, glob, os

COLS = ['name', 'nvars', 'nintvars', 'nrows', 'nnz', 'triv_bound', 'prop_bound', 'lp0_status', 'lp0_bound',
        'lp1_bound', 'ub', 'gap_closed', 'cut_prop_fixed', 'rc_fixed', 'rc_narrow', 'rc_prop_more', 'proved_opt',
        'ub2', 'gap_closed2', 'rc_fixed2', 'rc_narrow2', 'rc_prop_more2', 'proved_opt2',
        'mip_root_status', 'mip_root_bound', 'mip_root_primal', 'lp0_s', 'lp1_s', 'parse_s', 'prop_s', 'rc']


def last_json(path):
    try:
        return json.loads(open(path).read().strip().splitlines()[-1])
    except Exception:
        return None


rows = {}
for d in sys.argv[1:]:
    for f in sorted(glob.glob(os.path.join(d, '*.json'))):
        name = os.path.basename(f)[:-5]
        r = last_json(f) or {'name': name}
        r['name'] = name
        if r.get('failed') or 'lp0_status' not in r:
            r['lp0_status'] = 'FAILED'
        err = f[:-5] + '.err'
        if os.path.exists(err):
            tail = open(err).read().strip().splitlines()
            r['rc'] = tail[-1][3:] if tail and tail[-1].startswith('rc=') else '?'
        m = f[:-5] + '.mip'
        if os.path.exists(m):
            r.update({k: v for k, v in (last_json(m) or {'mip_root_status': 'crashed'}).items()
                      if k.startswith('mip_root')})
        if r.get('ub2') is not None and r.get('lp1_bound') is not None and r.get('prop_bound') is not None \
                and r['ub2'] > r['prop_bound']:
            r['gap_closed2'] = round((r['lp1_bound'] - r['prop_bound']) / (r['ub2'] - r['prop_bound']), 4)
        rows[name] = r

print('\t'.join(COLS))
for name in sorted(rows):
    r = rows[name]
    print('\t'.join('-' if r.get(c) is None else (f"{r[c]:.6g}" if isinstance(r[c], float) else str(r[c]))
                    for c in COLS))
