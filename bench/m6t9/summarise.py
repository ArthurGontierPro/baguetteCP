# M6-T9 (D-0080): summarise corpus_run.sh results.tsv files -- buckets, nodes/s, RSS, phase sums.
import sys,re,statistics as st,collections
def load(p):
    rows=[l.rstrip('\n').split('\t') for l in open(p)]
    done=[r for r in rows if r[0].startswith('DONE')]
    rows=[r for r in rows if not r[0].startswith('DONE')]
    return rows,done
def kv(d): return dict(re.findall(r'(\S+?)=(\S+)',d))
for p in sys.argv[1:]:
    rows,done=load(p)
    c=collections.Counter(r[1] for r in rows)
    nps=[];rss=[];comp=0;srch=0;emit=0;cpu=0;killed=collections.Counter()
    for r in rows:
        k=kv(r[4] if len(r)>4 else '')
        try:
            n=int(k['n']); t=float(k['cpu'].rstrip('s'))
            if t>0 and r[1] in('UNKNOWN-LIMIT','UNKNOWN-NOPROOF'): nps.append(n/t)
        except: pass
        if 'rss' in k: rss.append(int(k['rss']))
        for a,b in (('compile','comp'),('search','srch'),('emit','emit')):
            if a in k:
                v=float(k[a])
                if a=='compile': comp+=v
                elif a=='search': srch+=v
                else: emit+=v
        if 'killed-in' in k: killed[k['killed-in']]+=1
    q=lambda xs,f: (round(f(xs),2) if xs else None)
    print(f"== {p}  {'COMPLETE '+done[-1][0] if done else 'PARTIAL'}  rows={len(rows)}")
    print("   ", dict(c))
    if nps:
        xs=sorted(nps); print(f"    nodes/s over stopped runs (n={len(xs)}): min={xs[0]:.2f} p25={xs[len(xs)//4]:.2f} median={st.median(xs):.2f} p75={xs[3*len(xs)//4]:.2f} max={xs[-1]:.1f}")
    if rss: print(f"    rss MB: median={st.median(rss)} max={max(rss)} over {len(rss)} rows")
    print(f"    summed compile={comp:.0f}s search={srch:.0f}s emit={emit:.0f}s (emit/search={emit/srch if srch else 0:.3f})  killed-in={dict(killed)}")
