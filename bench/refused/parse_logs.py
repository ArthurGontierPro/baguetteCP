#!/usr/bin/env python3
"""M18-coverage-T9 (D-0265): one row per (instance, arm) from a run's stderr.

usage: parse_logs.py POPULATION.tsv LOGROOT ARM... > table.tsv
LOGROOT/<ARM>/<year>/log/<id>.baguette.err (the series layout) or LOGROOT/<ARM>/<id>.err.

Columns: id arm end phase wall nodes conflicts ladder opb direct widest bits held choices
heap_mb reserve_struct
  end    heap (the M7-T8 guard), estimate (D-0263's Encoding.reserve, before allocation),
         time (`limit: reached`), signal (`limit: killed signal=...` other than heap),
         ok (no limit line), other
  phase  the `phase=` / `at=` of the limit line, or `estimate` / `-`
"""
import os, re, sys

def find(root, arm, ident):
    y = ident.split('_')[0]
    for p in (f"{root}/{arm}/{y}/log/{ident}.baguette.err", f"{root}/{arm}/{ident}.err"):
        if os.path.exists(p):
            return p
    return None

def stat(txt, key):
    m = re.search(r'^stats: %s\s+(\S+)' % key, txt, re.M)
    return m.group(1) if m else '-'

def answer(path):
    out = path[:-4] + '.out'
    if not os.path.exists(out):
        return '-'
    o = open(out, errors='replace').read()
    if '=====UNSATISFIABLE=====' in o:
        return 'UNSAT'
    if '==========' in o:
        return 'COMPLETE'
    if '----------' in o:
        return 'SOLUTION'
    return 'none'

def parse(path):
    txt = open(path, errors='replace').read()
    r = {'answer': answer(path)}
    tf = path[:-4] + '.time'
    m = re.search(r'Maximum resident set size \(kbytes\): (\d+)', open(tf).read()) if os.path.exists(tf) else None
    r['rss_mb'] = str(int(m.group(1)) // 1024) if m else '-'
    lim = re.findall(r'^limit: .*$', txt, re.M)
    lim = lim[-1] if lim else ''
    if 'signal=heap-budget' in lim or ('heap budget is exhausted' in txt and not lim):
        r['end'] = 'heap'
    elif 'refused before it is allocated' in txt:
        r['end'] = 'estimate'
    elif lim.startswith('limit: reached'):
        r['end'] = 'time'
    elif lim.startswith('limit: killed'):
        r['end'] = 'signal'
    elif lim:
        r['end'] = 'other'
    elif not txt.strip():
        r['end'] = 'silent'   # killed with nothing on stderr (the series' empty logs)
    else:
        r['end'] = 'ok' if 'error' not in txt.lower() else 'other'
    m = re.search(r'(?:phase|at)=(\S+)', lim)
    r['phase'] = m.group(1) if m else ('estimate' if r['end'] == 'estimate' else '-')
    # the moment: compile (no encoding-cost stats yet: parse, compile, .opb), proofopen
    # (stats printed, no limit line: start_proof and the direct encodings), root (node 1 or
    # less), early (<= 1000 nodes), search
    has_stats = re.search(r'^stats: ladder', txt, re.M) is not None
    m2 = re.search(r'\bnodes=(\d+)', lim)
    n = int(m2.group(1)) if m2 else None
    if r['end'] in ('ok', 'other', 'silent'):
        r['moment'] = '-'
    elif r['end'] == 'estimate':
        r['moment'] = 'compile'
    elif r['phase'] in ('compile', 'opb', 'parse'):
        r['moment'] = 'compile'
    elif r['phase'] in ('proofopen',):
        r['moment'] = 'proofopen'
    elif not lim:
        r['moment'] = 'proofopen' if has_stats else 'compile'
    elif n is not None and n <= 1:
        r['moment'] = 'root'
    elif n is not None and n <= 1000:
        r['moment'] = 'early'
    else:
        r['moment'] = 'search'
    for k in ('wall', 'nodes', 'conflicts'):
        m = re.search(r'\b%s=([\d.]+)' % k, lim)
        r[k] = m.group(1) if m else '-'
    r['ladder'] = stat(txt, 'ladder')
    r['opb'] = stat(txt, 'opb')
    r['direct'] = stat(txt, 'direct')
    m = re.search(r'^stats: widest\s+(\d+) wide\s+`([^`]*)`', txt, re.M)
    r['widest'] = (m.group(1) + ':' + m.group(2)) if m else '-'
    r['bits'] = stat(txt, 'bits')
    m = re.search(r'^stats: bits .*held back: (.*)$', txt, re.M)
    r['held'] = m.group(1).strip().replace(' ', '') if m else '-'
    r['choices'] = stat(txt, 'choices')
    m = re.search(r'heap has reached (\d+) MB', txt)
    r['heap_mb'] = m.group(1) if m else '-'
    m = re.search(r'structure[: ]+([a-z_ /-]+)', txt)
    r['reserve_struct'] = m.group(1).strip() if (m and r['end'] == 'estimate') else '-'
    return r

COLS = ['answer', 'rss_mb', 'end', 'moment', 'phase', 'wall', 'nodes', 'conflicts', 'ladder', 'opb', 'direct', 'widest',
        'bits', 'held', 'choices', 'heap_mb', 'reserve_struct']

def main():
    pop, root, arms = sys.argv[1], sys.argv[2], sys.argv[3:]
    ids = [l.rstrip('\n').split('\t')[0] for l in open(pop) if l.strip()]
    print('\t'.join(['id', 'arm'] + COLS))
    for i in ids:
        for a in arms:
            p = find(root, a, i)
            if not p:
                print('\t'.join([i, a] + ['missing'] + ['-'] * (len(COLS) - 1)))
                continue
            r = parse(p)
            print('\t'.join([i, a] + [r[c] for c in COLS]))

main()
