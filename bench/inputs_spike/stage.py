import json,re,sys
from collections import Counter
R=[json.loads(l) for l in open(sys.argv[1])]; X=[r for r in R if "shapes" in r]
def isv(a): return a.startswith("[?")                       # a view
def toks(k):
    p=re.findall(r"\[[^\]]*\]|\S+",k); return p[0],p[1:]
B={"equals","not_equals","less_equal","less_than","greater_equal","greater_than"}
def s1(k):
    """a shape E2e.spec covers today (conditions (b = 0/1) only, views in comparisons written as linear)"""
    op,a=toks(k)
    if op in {"less_equal","less_than","equals","not_equals"}: return True
    if op in {"lin_less_equal","lin_equals","lin_not_equals"}: return True
    if op in {"less_equal_iff","equals_iff","not_equals_iff","lin_less_equal_iff"}: return a[0]=="cond=01" and not any(isv(x) for x in a)
    if op in {"and","or"}: return all(x in("[cond=01]","cond=01") for x in a)
    if op=="element": return a[0]=="[c]"
    if op in {"all_different","array_max","array_min","inverse","abs","regular"}: return True
    if op=="cumulative": return a[1]=="[c]" and a[2]=="[c]" and a[3]=="c"
    if op=="gacglobalcardinality": return True
    if op=="in": return a[0]=="[c]"
    return False
def s1b(k):  # + cake literals of every operator, other conditions, the _iff of lin_equals, boundsgcc
    op,a=toks(k)
    if s1(k): return True
    return op in {"and","or","equals_iff","less_equal_iff","less_than_iff","lin_equals_iff","lin_less_equal_iff","lin_not_equals_iff","not_equals_iff","boundsglobalcardinality","increasing","strictly_increasing"}
def s2(k):   # + every family baguette propagates itself: table, circuit, multiply, divide, closed gcc, count of a constant value, in
    op,a=toks(k)
    return s1b(k) or op in {"table","multiply","divide","boundsglobalcardinalityclosed","in"} or (op=="circuit") or (op=="count" and a[1]=="c")
def s3(k):   # + what mznlib or std decomposes today: written in Lower
    op,a=toks(k)
    return s2(k) or op in {"element","cumulative","count","disjunctive","disjunctive_strict","disjunctive2d","disjunctive2d_strict","lex_less_equal","lex_less_than","modulus","all_equal","all_different_except","parity","binpacking","value_precede","seq_precede_chain","nvalue","knapsack"}
for nm,s in(("1a E2e.spec today",s1),("1b + literals and _iff",s1b),("2 + native families",s2),("3 + decompositions",s3)):
    print(nm,sum(all(s(k) for k in r["shapes"]) for r in X),"of",len(X))
print("left",Counter(toks(k)[0] for r in X for k in r["shapes"] if not s3(k)))
for nm,s in(("1a",s1),("1b",s1b),("2",s2)):
    c=Counter()
    for r in X:
        for o in {toks(k)[0] for k in r["shapes"] if not s(k)}: c[o]+=1
    print(nm,"blocked by",c.most_common(14))
def view(k):
    op,a=toks(k)
    return any(x.startswith("[?+") for x in a) or (op in("circuit","subcircuit","binpacking") and "list" in a[0]) or "?+" in k
NV=[r for r in X if not any(view(k) for k in r["shapes"])]
print("no view:",len(NV),"of",len(X))
for nm,s in(("1a",s1),("1b",s1b),("2",s2),("3",s3)): print("no view and",nm,sum(all(s(k) for k in r["shapes"]) for r in NV))
