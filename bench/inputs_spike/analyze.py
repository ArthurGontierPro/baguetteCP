import sys,json,re,collections as C
CAKE=set("alldifferent alldifferent_except_n allequal circuit inverse table short_table negative_table regular xor cumulative no_overlap precedence gcc increasing decreasing strictly_increasing strictly_decreasing lex_less lex_lesseq min max abs mul div mod element count among nvalue indomain".split())
BAGN=set("alldifferent circuit inverse table regular cumulative no_overlap gcc min max abs mul div element indomain count among nd_element".split())
R=[json.loads(l) for l in open(sys.argv[1])]
print(len(R))
fam=lambda r:re.split(r'[-_]',r["f"].split("/")[-1])[0]
err=[r for r in R if "err" in r]; print("err",len(err)); print(C.Counter(re.sub(r'\d+','N',r["err"])[:90] for r in err).most_common(12))
print("loaded but failed after", sum(1 for r in err if "top" in r))
ok=[r for r in R if "cake" in r]; print("ok",len(ok),"families all",len({fam(r) for r in R}),"ok fam",len({fam(r) for r in ok}))
good=[r for r in ok if not r["cake"]["bad"]]; print("all flat forms in scp:",len(good),len({fam(r) for r in good}))
print("bad forms",C.Counter(k for r in ok for k in r["cake"]["bad"]).most_common(20))
L=[r for r in R if "top" in r]; print("loaded",len(L))
tn=C.Counter(); nn=C.Counter()
for r in L:
    for k in r["top"]: tn[k]+=1
    for k in r["nested"]: nn[k]+=1
print("native globals by instance",tn.most_common()); print("nested(reified)",nn.most_common())
nogap=[r for r in L if set(r["top"])<=CAKE and not r["nested"]]; print("no global lost for cake:",len(nogap))
lost=C.Counter(k for r in L for k in set(r["top"])-CAKE); print("lost for cake",lost)
print("ratio of vars after flattening"); import statistics as s
q=sorted(r["cake"]["nv"]/max(1,r["nv"]) for r in good); print([round(q[int(len(q)*p)],2) for p in(.1,.5,.9,.99)], "max",q[-1])
print("maxdom >10^6:",sum(r["maxdom"]>10**6 for r in L),">10^4",sum(r["maxdom"]>10**4 for r in L), "ncons>1e6",sum(r["cake"]["ncons"]>10**6 for r in ok))
b=[r for r in good if set(r["cake"]["native"])<=BAGN|{"lin","cmp","lit","and","or","->","==","reif:var","reif:sum","reif:wsum","reif:and","reif:or","gcc"}]; print("native keys within baguette:",len(b))
print(C.Counter(k for r in good for k in r["cake"]["native"] if k not in BAGN).most_common(30))
print("-----")
bad=[r for r in ok if r["cake"]["bad"]]; print(C.Counter(fam(r) for r in bad))
big=[r for r in good if r["cake"]["nv"]/max(1,r["nv"])>10]; print(len(big)); 
for f,n in C.Counter(fam(r) for r in big).most_common(): 
    x=[r for r in big if fam(r)==f][0]; print(f,n,x["nv"],x["cake"]["nv"],x["top"],x["nested"],x["cake"]["native"])
for r in bad[:1]+[r for r in bad if fam(r)!=fam(bad[0])][:1]: print(r)
print("small ratio <=2:",sum(r["cake"]["nv"]/max(1,r["nv"])<=2 for r in good))
print("ncons<=2000 & maxdom<=1000 & good",sum(r["cake"]["ncons"]<=2000 and r["maxdom"]<=1000 for r in good))
need=C.Counter()
for r in good:
    miss={k for k in r["cake"]["native"]}-(BAGN|{"lin","cmp","lit","and","or","->","==","reif:var","reif:sum","reif:wsum","reif:and","reif:or"})
    need[tuple(sorted(miss))]+=1
print(need.most_common(12))
print("native mul/div/mod instances",sum(bool({"mul","div","mod"}&set(r["cake"]["native"])) for r in good))
