#!/usr/bin/env python3
"""M18-coverage-T9 (D-0265): one row per instance of the population, joining
  the series (D-0227) arms B and D, today's reruns B and D (parse_logs.py), the wide order
  variables (wide_all.sh), the census (census.py), the order-encoding arm (Dorder), the
  no-budget arm (Dnolim) and GCS/Chuffed (gcs_table.sh).
usage: join.py W > instances.tsv   (W holds population.tsv, series_BD.tsv, now_B.tsv, now_D.tsv,
  wide_D.tsv, census_PB.tsv, now_Dorder.tsv, now_Dnolim.tsv, gcs.tsv; missing ones are skipped)
"""
import csv, os, sys
W = sys.argv[1]

def table(name, key='id', arm=None):
    p = os.path.join(W, name)
    if not os.path.exists(p):
        return {}
    rows = {}
    with open(p) as f:
        for r in csv.DictReader(f, delimiter='\t'):
            if arm and r.get('arm') != arm:
                continue
            rows[r[key]] = r
    return rows

pop = [l.rstrip('\n').split('\t') for l in open(os.path.join(W, 'population.tsv'))]
sB, sD = table('series_BD.tsv', arm='B'), table('series_BD.tsv', arm='D')
nB, nD = table('now_B.tsv'), table('now_D.tsv')
wide = table('wide_D.tsv')
cen = table('census_PB.tsv')
order = table('now_Dorder.tsv')
nolim = table('now_Dnolim.tsv')
gcs = table('gcs.tsv')

def st(r):
    if not r:
        return '-'
    a = r.get('answer', '-')
    e = r.get('end', '-')
    m = r.get('moment', '-')
    if a in ('SOLUTION', 'COMPLETE', 'UNSAT'):
        return a.lower() + ('/' + e if e not in ('ok', '-') else '')
    if e in ('heap', 'estimate'):
        return 'REFUSED:' + m
    if e in ('time', 'signal'):
        return 'timeout:' + m
    return e

cols = ['id', 'why', 'series_B', 'series_D', 'now_B', 'now_D', 'B_nodes', 'D_nodes', 'ladder', 'opb_lines',
        'held', 'n_wide', 'wide_width', 'sparse_values', 'census_live_MB', 'model%', 'trail%', 'learned%',
        'proof%', 'other%', 'top_families', 'touch_order', 'decl_order', 'Dorder', 'Dnolim', 'Dnolim_rss_MB',
        'gcs', 'gcs_obj', 'gcs_rss_MB', 'chuffed']
print('\t'.join(cols))
for p in pop:
    i = p[0]
    b, d, w, c = nB.get(i, {}), nD.get(i, {}), wide.get(i, {}), cen.get(i, {})
    g = gcs.get(i, {})
    nl = nolim.get(i, {})
    row = [i, p[1], st(sB.get(i)), st(sD.get(i)), st(b), st(d), b.get('nodes', '-'), d.get('nodes', '-'),
           (b.get('ladder') if b.get('ladder', '-') != '-' else d.get('ladder', '-')) or '-',
           (b.get('opb') if b.get('opb', '-') != '-' else d.get('opb', '-')) or '-',
           (b.get('held') if b.get('held', '-') != '-' else d.get('held', '-')) or '-',
           w.get('n_wide', '-'), w.get('sum_width', '-'), w.get('elem_res_distinct', '-'),
           c.get('live_MB', '-'), c.get('model', '-'), c.get('trail', '-'), c.get('learned', '-'),
           c.get('proof', '-'), c.get('other', '-'), c.get('top_families', '-'),
           c.get('touch.order_atoms', '-'), c.get('decl.order_atoms', '-'),
           st(order.get(i)), st(nl), nl.get('rss_mb', '-'),
           g.get('gcs_status', '-'), g.get('gcs_obj', '-'), g.get('gcs_rss_mb', '-'), g.get('chuffed_status', '-')]
    print('\t'.join(x if x else '-' for x in row))
