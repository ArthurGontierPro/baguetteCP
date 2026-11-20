#!/usr/bin/env python3
"""table.py OUTDIR... -- one TSV row per opb2lp.py result (M13-codes-leads-T1, D-0183)."""
import sys, json, glob, os
COLS = ['name', 'nvars', 'nrows', 'nnz', 'prop_fixed', 'triv_bound', 'prop_bound', 'lp0_status', 'lp0_bound',
        'lp1_status', 'lp1_bound', 'ub', 'gap_closed', 'rc_fixed', 'rc_intvars', 'free_after_prop',
        'rc_prop_more', 'rc_prop_bound', 'lp0_s', 'lp1_s', 'parse_s', 'prop_s']
print('\t'.join(COLS))
for d in sys.argv[1:]:
    for f in sorted(glob.glob(os.path.join(d, '*.json'))):
        try:
            r = json.loads(open(f).read().strip().splitlines()[-1])
        except Exception:
            r = {'name': os.path.basename(f)[:-5], 'lp0_status': 'NO-RESULT'}
        if r.get('failed'):
            r['lp0_status'] = 'FAILED'
        print('\t'.join('-' if r.get(c) is None else (f"{r[c]:.6g}" if isinstance(r[c], float) else str(r[c])) for c in COLS))
