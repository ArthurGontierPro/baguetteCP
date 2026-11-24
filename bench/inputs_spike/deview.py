# deview.py IN.scp OUT.scp : write a comparison over views (+-X + k) as a linear constraint; nothing else changes
import sys,re
T=r"(-?[A-Za-z0-9_]+|\(-?[A-Za-z0-9_]+ \+ -?\d+\))"
def term(t):
    m=re.fullmatch(r"\((-?)([A-Za-z0-9_]+) \+ (-?\d+)\)",t)
    if m: return (-1 if m.group(1) else 1, m.group(2), int(m.group(3)))
    if re.fullmatch(r"-?\d+",t): return (0,None,int(t))
    return (1,t,0)
def rw(m):
    n,op,cond,a,b=m.group(1),m.group(2),m.group(3) or "",m.group(4),m.group(5)
    if "(" not in a+b: return m.group(0)
    (ca,va,ka),(cb,vb,kb)=term(a),term(b)
    ts=[]
    if va: ts.append(f"{ca} {va}")
    if vb: ts.append(f"{-cb} {vb}")
    return f"({n} lin_{op} {cond}({' '.join(ts)}) {kb-ka})"
s=open(sys.argv[1]).read()
s=re.sub(r"\((\S+) ((?:less_equal|less_than|equals|not_equals)(?:_iff|_if)?) (\([^()]*(?:=|<|>)[^()]*\) )?"+T+" "+T+r"\)",rw,s)
open(sys.argv[2],"w").write(s)
