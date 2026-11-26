# shape.py MODEL_DIR : write the GCS .scp of the smallest instance, keep it, list argument shapes
import sys,os,subprocess,json,glob,re,shutil,resource,gzip
d=sys.argv[1].rstrip("/"); D="/scratch/arthur/scp-gcs-20261124"; name="_".join(d.split("/")[-2:]); w=f"{D}/cov/{name}"; os.makedirs(w,exist_ok=True); os.makedirs(D+"/corpus",exist_ok=True)
MZ="/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc"; G=D+"/buildfzn/fzn-glasgow"
def lim(): resource.setrlimit(resource.RLIMIT_AS,(16<<30,16<<30)); resource.setrlimit(resource.RLIMIT_FSIZE,(3<<30,3<<30))
def run(a,t):
    try: return subprocess.run(a,cwd=w,capture_output=True,timeout=t,preexec_fn=lim).returncode
    except subprocess.TimeoutExpired: return 124
mz=sorted(glob.glob(d+"/*.mzn"),key=os.path.getsize); dz=sorted(glob.glob(d+"/*.dzn")+glob.glob(d+"/*.json"),key=os.path.getsize)
main=next((m for m in mz if re.search(r"\bsolve\b",open(m,errors="replace").read())),None)
r={"m":name}
if main and run([MZ,"-c","--solver",D+"/glasgow-cov.msc","--fzn",w+"/g.json","--ozn",w+"/g.ozn",main]+dz[:1],200)==0:
    run([G,"--prove","--proof-files-basename",w+"/g",w+"/g.json"],30)
    f=w+"/g.scp"
    if os.path.exists(f) and os.path.getsize(f):
        s=open(f).read(); shutil.move(f,f"{D}/corpus/{name}.scp"); r["size"]=len(s)
        sys.setrecursionlimit(10000)
        st=[[]]
        for t in re.finditer(r"[()]|[^\s()]+",s):
            t=t.group()
            if t=="(": st.append([])
            elif t==")": x=st.pop(); st[-1].append(x)
            else: st[-1].append(t)
        top=st[0][0]; vs={v[0]:(int(v[1]),int(v[2])) for v in top[1][1:]}
        isi=lambda a: isinstance(a,str) and re.fullmatch(r"-?\d+",a) is not None
        sh={}; 
        def add(k): sh[k]=sh.get(k,0)+1
        def kind(a):
            if isinstance(a,list): 
                if len(a)==3 and a[1] in("=","!=",">=","<",">","<="): return "cond"+a[1]+("01" if a[2] in("0","1") else "N")
                return "list"
            return "c" if isi(a) else ("v" if a in vs else "?"+a[:12])
        for c in top[2][1:]:
            k=c[1]; a=c[2:]
            parts=[]
            for x in a:
                if kind(x)=="list":
                    ks=sorted({kind(y) for y in x}); parts.append("["+",".join(ks[:6])+"]")
                else: parts.append(kind(x))
            add(k+" "+" ".join(parts))
        r["shapes"]=sh; r["nv"]=len(vs); r["nc"]=len(top[2])-1; r["maxw"]=max([b-a+1 for a,b in vs.values()] or [0]); r["prob"]=top[3][1] if isinstance(top[3][1],str) else top[3][1][0]
        r["anon"]=sum(v.startswith("_") for v in vs)
shutil.rmtree(w,ignore_errors=True); print(json.dumps(r),flush=True)
