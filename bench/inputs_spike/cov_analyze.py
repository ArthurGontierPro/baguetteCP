import json,collections as C,re
S="/tmp/claude-1000/-home-arthur-gla-baguette/f6e2f843-c576-49a5-b885-a07276e2306c/scratchpad"
R=[json.loads(l) for l in open(S+"/cov.jsonl")]
print(len(R),"gcs flat",sum(r.get("gcs_flat")=="ok" for r in R),"bag flat",sum(r.get("bag_flat")=="ok" for r in R),"both",sum(r.get("bag_flat")=="ok" and r.get("gcs_flat")=="ok" for r in R))
X=[r for r in R if "scp" in r]
for r in X: r["scp"].pop("enumerate",None); print("scp written",len(X),"parse",C.Counter(r["parse"] for r in X))
print(C.Counter(re.sub(r"\d+","N",r.get("perr",""))[-90:] for r in X if r["parse"]).most_common(8))
N=[r for r in R if "noscp" in r]; print("noscp",len(N),C.Counter((r["noscp"][0],re.sub(r"\d+","N",r["noscp"][1])[-110:]) for r in N).most_common(14))
kw=C.Counter(); tot=C.Counter()
for r in X:
    for k,v in r["scp"].items(): kw[k]+=1; tot[k]+=v
print("scp keywords by model"); print(kw.most_common())
g=C.Counter(k for r in R for k in r.get("gcs_fzn",{})); print("GCS fzn builtins"); print(g.most_common())
b=C.Counter(k for r in R for k in r.get("bag_fzn",{})); print("BAG builtins"); print(b.most_common())
print("bag_scp",C.Counter((re.sub(r"\d+","N",r["bag_scp"]))[:70] for r in R if "bag_scp" in r).most_common(12))
CAKE=set("abs all_different_except all_different all_equal among and arg_sort array_max array_min at_most_one_smart_table at_most_one boundsglobalcardinalityclosed boundsglobalcardinality circuit count cumulative decreasing disjunctive2d_strict disjunctive2d disjunctive_strict disjunctive divide element_2d element gacglobalcardinalityclosed gacglobalcardinality increasing inverse in knapsack lex_smart_table max minus min modulus multiply negative_table neg nvalue or parity plus regular seq_precede_chain smart_table sort strictly_decreasing strictly_increasing symmetric_all_different table value_precede notin".split())
def cake(k): 
    return k in CAKE or re.sub(r"_(if|iff)$","",k) in {"equals","not_equals","less_equal","less_than","greater_equal","greater_than","lin_equals","lin_not_equals","lin_less_equal","lin_less_than","lin_greater_equal","lin_greater_than"} or k.startswith("lex_")
notcake=C.Counter(k for r in X for k in r["scp"] if not cake(k)); print("GCS keywords cake lacks, by model",notcake)
print("models all-cake",sum(all(cake(k) for k in r["scp"]) for r in X),"and parse ok",sum(all(cake(k) for k in r["scp"]) and r["parse"]==0 for r in X))
E2E=set("lin_less_equal lin_equals lin_not_equals less_equal less_than equals not_equals all_different or and less_equal_iff equals_iff not_equals_iff lin_less_equal_iff element gacglobalcardinality array_max array_min max min inverse abs cumulative regular in".split())
MIR=E2E|set("greater_equal greater_than lin_greater_equal lin_greater_than lin_less_than greater_equal_iff greater_than_iff lin_greater_equal_iff less_than_iff lin_equals_iff lin_not_equals_iff plus minus".split())
IF=MIR|set("less_equal_if less_than_if greater_equal_if greater_than_if equals_if not_equals_if lin_equals_if lin_not_equals_if lin_less_equal_if lin_greater_equal_if boundsglobalcardinality".split())
for nm,s in (("E2E today",E2E),("+mirrors/plus",MIR),("+_if,bounds gcc",IF)):
    print(nm,sum(set(r["scp"])<=s for r in X))
# greedy
cur=set(IF); order=[]
for _ in range(22):
    best=None
    cand=set(k for r in X for k in r["scp"])-cur
    for k in cand:
        n=sum(set(r["scp"])<=cur|{k} for r in X); m=sum(k in r["scp"] for r in X)
        if best is None or (n,m)>best[:2]: best=(n,m,k)
    if not best: break
    cur.add(best[2]); order.append((best[2],best[0],best[1],"cake" if cake(best[2]) else "NOCAKE"))
print(order)
