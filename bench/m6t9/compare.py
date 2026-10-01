# M6-T9 (D-0080): compare two corpus_run.sh results.tsv files instance by instance.
import sys,re,statistics as st
def load(p):
    d={}
    for l in open(p):
        r=l.rstrip('\n').split('\t')
        if r[0].startswith('DONE'): continue
        k=dict(re.findall(r'(\S+?)=(\S+)',r[4] if len(r)>4 else ''))
        d[r[0]]=(r[1],k)
    return d
A=load(sys.argv[1]); B=load(sys.argv[2])
both=[i for i in A if i in B and A[i][0]=='OK-PROOF-VERIFIED' and B[i][0]=='OK-PROOF-VERIFIED']
ta=sum(float(A[i][1].get('search',0)) for i in both); tb=sum(float(B[i][1].get('search',0)) for i in both)
print(f"OK in both: {len(both)}; summed search {ta:.1f}s -> {tb:.1f}s")
big=[(float(A[i][1].get('search',0)),float(B[i][1].get('search',0)),i) for i in both if float(A[i][1].get('search',0))>=1]
for a,b,i in sorted(big,reverse=True)[:8]: print(f"   {i[:45]:45} {a:7.1f}s -> {b:7.1f}s  x{a/max(b,0.05):.1f}")
newok=[i for i in B if B[i][0]=='OK-PROOF-VERIFIED' and A.get(i,('',))[0]!='OK-PROOF-VERIFIED']
lost=[i for i in A if A[i][0]=='OK-PROOF-VERIFIED' and B.get(i,('',))[0]!='OK-PROOF-VERIFIED']
print("newly OK:",len(newok),[ (i[:30],A[i][0][:8]) for i in newok])
print("lost OK:",[(i,B[i][0]) for i in lost])
# nodes/s per instance stopped in both
r=[]
for i in A:
    if i in B and A[i][0]=='UNKNOWN-LIMIT' and B[i][0] in ('UNKNOWN-LIMIT',):
        try:
            na=int(A[i][1]['n'])/float(A[i][1]['cpu'].rstrip('s')); nb=int(B[i][1]['n'])/float(B[i][1]['cpu'].rstrip('s'))
            if na>0: r.append(nb/na)
        except: pass
if r: print(f"per-instance nodes/s ratio (stopped in both, n={len(r)}): min={min(r):.2f} median={st.median(r):.2f} max={max(r):.1f}")
