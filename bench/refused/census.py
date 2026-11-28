#!/usr/bin/env python3
"""M18-coverage-T9 (D-0265): the census of D-0218's method on today's main.

For each <id>.probe.tsv (bench/refused/memprobe.patch on main 00c42b51: D-0218s probe
plus the touched-atom counters of D-0265), take the probe that
stands for the refusal: the LAST probe whose live data is known (the 8 GiB crossing when the
run got there, else the exit or the last node probe), and group the kinds:

  model      frontend.model, encoding.*, compile.rest, store.domains/names, engine.*, prop.*
             (the propagator instances by family): what the encoding and the decompositions keep
  trail      store.trail, store.reasons, store.bound_hist, store.rest
  learned    search.retention, learned.engine
  proof      writer.*, justify.ctx, expl.hashcons, search.trace
  other      search.stats, unattributed

usage: census.py PROBEDIR > census.tsv
columns: id probe nodes conflicts live_MB heap_MB model trail learned proof other (shares of
live, %) top_families (the three largest prop.* with MB) touch/decl counters
"""
import collections, glob, os, sys

GROUPS = [('model', ('frontend.', 'encoding.', 'compile.', 'store.domains', 'store.names',
                     'engine.', 'prop.')),
          ('trail', ('store.trail', 'store.reasons', 'store.bound_hist', 'store.rest')),
          ('learned', ('search.retention', 'learned.')),
          ('proof', ('writer.', 'justify.', 'expl.', 'search.trace')),
          ('other', ('search.stats', 'unattributed'))]

def group(k):
    for g, pre in GROUPS:
        if any(k.startswith(p) for p in pre):
            return g
    return 'other'

def load(f):
    tags = []
    kind = collections.defaultdict(dict); gc = collections.defaultdict(dict)
    cnt = collections.defaultdict(dict); meta = {}; done = set()
    for line in open(f, errors='replace'):
        p = line.rstrip('\n').split('\t')
        if len(p) < 5:
            continue
        tag = p[1]
        if p[0] in ('gc', 'kind', 'count') and tag not in tags:
            tags.append(tag)
        if p[0] == 'probe_seconds':
            done.add(tag)   # a probe whose walk finished (a run killed mid-walk has none)
        meta.setdefault(tag, (p[2], p[3]))
        try:
            if p[0] == 'gc' and len(p) > 5:
                gc[tag][p[4]] = int(p[5])
            elif p[0] == 'kind':
                kind[tag][p[4]] = int(p[5])
            elif p[0] == 'count':
                cnt[tag][p[4]] = int(p[5])
        except ValueError:
            pass
    return tags, kind, gc, cnt, meta, done

CNT = ['enc.ladder_clauses', 'enc.bits_vars', 'enc.direct_values', 'trail_len', 'learned.n_live',
       'touch.order_atoms', 'decl.order_atoms', 'touch.wide_order_atoms', 'decl.wide_order_atoms',
       'touch.wide_order_vars', 'decl.wide_order_vars', 'touch.bits_atoms', 'decl.bits_atoms',
       'enc.n_atoms', 'search.nodes', 'search.conflicts']

def main():
    print('\t'.join(['id', 'probe', 'live_MB', 'heap_MB'] + [g for g, _ in GROUPS]
                    + ['top_families', 'top_kinds'] + CNT))
    for f in sorted(glob.glob(os.path.join(sys.argv[1], '*.probe.tsv'))):
        ident = os.path.basename(f)[:-len('.probe.tsv')]
        tags, kind, gc, cnt, meta, done = load(f)
        ok = [t for t in tags if t in done and kind[t] and gc[t].get('live_words', 0) > 0]
        if not ok:
            print('\t'.join([ident, 'none'] + ['-'] * (2 + len(GROUPS) + 2 + len(CNT))))
            continue
        t = ok[-1]
        live = gc[t]['live_words']
        heap = gc[t].get('heap_words', 0)
        g = collections.Counter()
        for k, w in kind[t].items():
            g[group(k)] += w
        fams = sorted(((w, k) for k, w in kind[t].items() if k.startswith('prop.')), reverse=True)[:3]
        kinds = sorted(((w, k) for k, w in kind[t].items()), reverse=True)[:4]
        # counters: the latest value seen up to this probe (counters are written at each probe)
        c = {}
        for tt in tags[:tags.index(t) + 1]:
            c.update(cnt[tt])
        row = [ident, t, '%.0f' % (live * 8 / 1e6), '%.0f' % (heap * 8 / 1e6)]
        row += ['%.0f' % (100.0 * g[gname] / live) for gname, _ in GROUPS]
        row.append(','.join('%s:%.0f' % (k[5:], w * 8 / 1e6) for w, k in fams) or '-')
        row.append(','.join('%s:%.0f' % (k, w * 8 / 1e6) for w, k in kinds) or '-')
        row += [str(c.get(k, '-')) for k in CNT]
        print('\t'.join(row))

main()
