# probe.py FILE.xml.lzma : is the instance expressible in cake's .scp through CPMpy's flattening?
import sys, lzma, time, json, resource, warnings; warnings.filterwarnings("ignore")
resource.setrlimit(resource.RLIMIT_AS,(8<<30,8<<30))
f=sys.argv[1]; r={"f":f}
import cpmpy as cp
from cpmpy.tools.io.xcsp3 import load_xcsp3
from cpmpy.expressions.globalconstraints import GlobalConstraint
from cpmpy.expressions.globalfunctions import GlobalFunction
from cpmpy.expressions.core import Comparison, Operator, BoolVal, Expression
from cpmpy.expressions.variables import _BoolVarImpl,_NumVarImpl
from cpmpy.transformations.normalize import toplevel_list
from cpmpy.transformations.safening import no_partial_functions
from cpmpy.transformations.negation import push_down_negation
from cpmpy.transformations.decompose_global import decompose_in_tree
from cpmpy.transformations.flatten_model import flatten_constraint, flatten_objective
from cpmpy.transformations.reification import reify_rewrite, only_bv_reifies
from cpmpy.transformations.comparison import only_numexpr_equality
from cpmpy.transformations.cse import CSEMap
from cpmpy.transformations.get_variables import get_variables
CAKE=frozenset("alldifferent alldifferent_except_n allequal circuit inverse table short_table negative_table regular xor cumulative no_overlap precedence gcc increasing decreasing strictly_increasing strictly_decreasing lex_less lex_lesseq min max abs mul div mod element count among nvalue indomain".split())
BAG=frozenset("alldifferent circuit inverse table regular cumulative no_overlap gcc min max abs mul div element indomain".split())
t0=time.time()
try:
    m=load_xcsp3(f, open=lambda p,*a,**k: lzma.open(p,"rt"))
    r["load"]=round(time.time()-t0,1)
    cons=toplevel_list(m.constraints)
    top={}; nested={}
    def walk(e,root):
        st=[(e,root)]
        while st:
            e,root=st.pop()
            if isinstance(e,(list,tuple)):
                st.extend((a,False) for a in e); continue
            if not isinstance(e,Expression): continue
            if isinstance(e,GlobalConstraint):
                d=top if root else nested; d[e.name]=d.get(e.name,0)+1
            elif isinstance(e,GlobalFunction):
                top[e.name]=top.get(e.name,0)+1
            if hasattr(e,"args") and not isinstance(e,(_NumVarImpl,)):
                if getattr(e,"name","") in ("table","short_table","negative_table","regular","mdd"): st.append((e.args[0],False))
                else: st.extend((a,False) for a in e.args)
    for c in cons: walk(c,True)
    if m.objective_ is not None: walk(m.objective_,False)
    r["top"]=top; r["nested"]=nested; uv=get_variables(cons); r["nv"]=len(uv)
    r["maxdom"]=max([int(v.ub)-int(v.lb)+1 for v in uv] or [0])
    pass
    for tag,sup in (("cake",CAKE),):
        cs=CSEMap()
        c=no_partial_functions(cons); c=push_down_negation(c)
        c=decompose_in_tree(c,supported=sup,supported_reified=frozenset(),csemap=cs)
        c=flatten_constraint(c,csemap=cs)
        c=reify_rewrite(c,supported=frozenset(["==","sum","wsum"]),csemap=cs)
        c=only_numexpr_equality(c,supported=frozenset(["sum","wsum"]),csemap=cs)
        c=only_bv_reifies(c,csemap=cs)
        if m.objective_ is not None:
            o,oc=flatten_objective(m.objective_,csemap=cs); c=c+oc
        bad={}; native={}
        def lin(e): return isinstance(e,_NumVarImpl) or getattr(e,"name","") in ("sum","wsum","mul","sub","-")
        for k in c:
            n=k.name if hasattr(k,"name") else "?"
            ok=False; key=n
            if isinstance(k,(_BoolVarImpl,BoolVal)): ok=True; key="lit"
            elif isinstance(k,GlobalConstraint): ok=n in sup
            elif isinstance(k,Operator) and n in("and","or","->") or (n=="==" and isinstance(k.args[0],_BoolVarImpl) and not isinstance(k.args[1],_NumVarImpl)):
                b=k.args[-1] if n in("->","==") else None
                if b is None: ok=True
                elif isinstance(b,_BoolVarImpl) or (isinstance(b,Operator) and b.name in("and","or")): ok=True
                elif isinstance(b,Comparison):
                    ok=lin(b.args[0]); key="reif:"+(b.args[0].name if not isinstance(b.args[0],_NumVarImpl) else "var")
                else: key="reif:"+str(getattr(b,"name",type(b).__name__))
            elif isinstance(k,Comparison):
                l=k.args[0]
                if lin(l): ok=True; key="lin" if not isinstance(l,_NumVarImpl) else "cmp"
                else: key=l.name; ok=(k.name=="==") and l.name in sup
            native[key]=native.get(key,0)+1
            if not ok: bad[key]=bad.get(key,0)+1
        r[tag]={"bad":bad,"native":native,"ncons":len(c),"nv":len(get_variables(c))}
    r["t"]=round(time.time()-t0,1)
except SystemExit: pass
except BaseException as e:
    r["err"]=type(e).__name__+": "+str(e)[:160]
print(json.dumps(r),flush=True)
