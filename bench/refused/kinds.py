#!/usr/bin/env python3
"""M18-coverage-T9 (D-0265): the dominant kind per instance, from instances.tsv (join.py) and
census_PB.tsv (census.py). One row per instance: id, kind, what the census says, refused today
in B, in D, and the live MB at the probe that stands for the refusal.

Kinds, decided in this order (the first that applies):
  gap        a wide (>= 10 000) order variable that a constant array bounds to a few values
             (array_int_element result, baguette_table column: wide_holders.py), and the
             census says the trail or the proof holds the heap: the domain-consistent global
             prunes the declared gap VALUE BY VALUE at the root, one trail entry each
  alldiff    prop.all_different_int is the largest kind (the pairwise row table, n^2 x w ids),
             or an all_different over n vars of shared width w with n^2 w / 2 > 10^8 rows
             whose run never got past the compile probe
  arith      prop.int_times + prop.int_div + prop.int_abs is the largest model kind
  model      the model group (instances, subscriptions, encoding records, front end) > 50 %
  trail      store.* > 50 % (outside the gap kind): trail entries of kilobytes in the search
  proof      writer.* + justify + expl.hashcons + search.trace > 50 %, or the largest group
  learned    search.retention + learned.* > 50 %
  none       no completed probe
Then the reading of the census by hand, in OVERRIDE below (each with its reason): the trail
kind is split by what the entries hold, and the instances refused only with the proof go to the
proof kind.
usage: kinds.py W > kinds.tsv
"""
import csv, os, sys
W = sys.argv[1]
inst = {r['id']: r for r in csv.DictReader(open(os.path.join(W, 'instances.tsv')), delimiter='\t')}
cen = {r['id']: r for r in csv.DictReader(open(os.path.join(W, 'census_PB.tsv')), delimiter='\t')}
AD_ROWS = {}
p = os.path.join(W, 'alldiff_rows.tsv')
if os.path.exists(p):
    for l in open(p):
        f = l.split()
        if len(f) == 4:
            AD_ROWS[f[0]] = int(f[3])

def kmb(kinds, prefix):
    s = 0.0
    for part in kinds.split(','):
        if ':' in part:
            k, v = part.rsplit(':', 1)
            if any(k.startswith(x) for x in prefix):
                try:
                    s += float(v)
                except ValueError:
                    pass
    return s

def num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None

OVERRIDE = {
    # 400 k element results of width about 250 bounded to 3.7 M values in all (elemres): the gap
    # pruning of narrow variables, whose proof side (writer.live 5 GB of live ids at the root)
    # is what the census sees
    '2023_table-layout_p2000_m16_r1000_c200': 'gap',
    # store.trail of 4.6 to 190 KB per entry: deferred reasons holding explanation trees
    # (D-0223's mechanism: Element's wrapper keeps the tree its release lets go of)
    '2026_tdtsp_inst_20_56_00': 'reasons', '2015_tdtsp_inst_20_25_00': 'reasons',
    '2026_warehouse_oly20': 'reasons', '2026_warehouse_wlp02': 'reasons',
    '2026_warehouse_wlp22': 'reasons', '2025_ihtc-2024-marte_i11': 'reasons',
    '2019_nside_HARD_2000_500': 'reasons', '2026_nside_MEDIUM_2000_500': 'reasons',
    # refused with the proof only, at 8 nodes, live 1.6 to 2.5 GB under an 8 GiB heap: the
    # proof's trace and writer plus the GC's free space (D-0218 fix 3)
    '2013_nmseq_395': 'proof', '2013_nmseq_478': 'proof', '2015_nmseq_393': 'proof',
    '2013_nmseq_143': 'search', '2013_nmseq_202': 'search', '2015_nmseq_176': 'search',
    '2015_nmseq_207': 'search', '2015_nmseq_269': 'search',
    # 426 MB at 345 nodes, a time-out: not memory
    '2026_multiple-constant-multiplication_CHEN99_28B': 'search',
    '2024_yumi-dynamic_p_5_GSS_SG_yumi_grid_setup_3_4_zones': 'search',
    # the front end refuses `fplen` (var int, no domain): not memory
    '2021_MZNC_connect_connect__0086_02': 'front-end',
}
print('\t'.join(['id', 'kind', 'live_MB', 'model%', 'trail%', 'learned%', 'proof%', 'top_kinds',
                 'now_B', 'now_D', 'Dnolim', 'Dnolim_rss_MB', 'gcs', 'gcs_rss_MB']))
for i, r in inst.items():
    c = cen.get(i, {})
    live = num(c.get('live_MB'))
    model, trail, learned, proof = (num(c.get(k)) or 0 for k in ('model', 'trail', 'learned', 'proof'))
    tk = c.get('top_kinds', '-') or '-'
    fam = c.get('top_families', '-') or '-'
    wide = num(r.get('wide_width')) or 0
    sparse = num(r.get('sparse_values')) or 0
    ad = kmb(tk, ('prop.all_different_int',))
    ar = kmb(fam, ('int_times', 'int_div', 'int_abs'))
    if wide >= 10000 and sparse and sparse < wide / 10:
        kind = 'gap'
    elif live and ad >= 0.3 * live:
        kind = 'alldiff'
    elif (not live or live < 100) and AD_ROWS.get(i, 0) > 1e8:
        kind = 'alldiff'
    elif not live:
        kind = 'none'
    elif ar >= 0.3 * live:
        kind = 'arith'
    elif model > 50:
        kind = 'model'
    elif trail > 50:
        kind = 'trail'
    elif learned > 50:
        kind = 'learned'
    elif proof >= max(model, trail, learned):
        kind = 'proof'
    else:
        kind = 'model'
    kind = OVERRIDE.get(i, kind)
    print('\t'.join([i, kind, c.get('live_MB', '-'), c.get('model', '-'), c.get('trail', '-'),
                     c.get('learned', '-'), c.get('proof', '-'), tk[:120], r['now_B'], r['now_D'],
                     r['Dnolim'], r['Dnolim_rss_MB'], r['gcs'], r['gcs_rss_MB']]))
