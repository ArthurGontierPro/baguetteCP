# cov.py MODEL_DIR : flatten the smallest instance for GCS, take the .scp GCS writes, list keywords; one JSON line
import sys,os,subprocess,json,glob,re,shutil,resource
d=sys.argv[1].rstrip("/"); D="/scratch/arthur/scp-gcs-20261124"; name="_".join(d.split("/")[-2:]); w=f"{D}/cov/{name}"; os.makedirs(w,exist_ok=True)
MZ="/scratch/arthur/mzn/MiniZincIDE-2.10.1-x86_64-linux-gnu/bin/minizinc"; G=D+"/buildfzn/fzn-glasgow"
r={"m":name}
mz=sorted(glob.glob(d+"/*.mzn"),key=os.path.getsize); dz=sorted(glob.glob(d+"/*.dzn")+glob.glob(d+"/*.json"),key=os.path.getsize)
def lim(): resource.setrlimit(resource.RLIMIT_AS,(16<<30,16<<30)); resource.setrlimit(resource.RLIMIT_FSIZE,(3<<30,3<<30))
def run(a,t):
    try:
        p=subprocess.run(a,cwd=w,capture_output=True,text=True,timeout=t,preexec_fn=lim); return p.returncode,(p.stdout[-300:]+p.stderr[-400:])
    except subprocess.TimeoutExpired: return 124,"timeout"
main=None
# several .mzn without data: smallest is an instance; with data: the .mzn that has a solve item
for m in mz:
    if re.search(r"\bsolve\b",open(m,errors="replace").read()): main=m; break
if not main: r["err"]="no solve item"; print(json.dumps(r)); sys.exit()
for tag,msc,ext in (("gcs",D+"/glasgow-cov.msc","json"),("bag","/scratch/arthur/scp-gcs-20261124/baguette-cov.msc","fzn")):
    data=dz[:1]
    rc,o=run([MZ,"-c","--solver",msc,"--fzn",f"{w}/{tag}.{ext}","--ozn",f"{w}/{tag}.ozn",main]+data,200)
    if rc!=0: r[tag+"_flat"]=o[-200:].replace("\n"," "); continue
    r[tag+"_flat"]="ok"
if r.get("gcs_flat")=="ok":
    js=json.load(open(w+"/gcs.json")); c={}
    for k in js["constraints"]: c[k["id"]]=c.get(k["id"],0)+1
    r["gcs_fzn"]=c
    rc,o=run([G,"--prove","--proof-files-basename",w+"/g",w+"/gcs.json"],60)
    f=w+"/g.scp"
    if os.path.exists(f) and os.path.getsize(f)>0:
        s=open(f).read(); kw={}; i=s.index("(constraints")
        for l in s[i:].split("\n")[1:]:
            m=re.match(r"\s*\(\S+ ([a-z_0-9]+)[ )]",l)
            if m: kw[m.group(1)]=kw.get(m.group(1),0)+1
        r["scp"]=kw; r["views"]=len(re.findall(r"\(-?\S+ \+ -?\d+\)|\(-\S+\)",s[i:])); r["size"]=len(s)
        rc2,o2=run([D+"/build/glasgow_scp_solver","--parse-only",f],60); r["parse"]=rc2; 
        if rc2: r["perr"]=o2.strip()[-160:]
    else: r["noscp"]=(rc,o.strip()[-200:])
if r.get("bag_flat")=="ok":
    c={}
    for l in open(w+"/bag.fzn"):
        m=re.match(r"\s*constraint\s+([A-Za-z_0-9]+)",l)
        if m: c[m.group(1)]=c.get(m.group(1),0)+1
    r["bag_fzn"]=c
    rc,o=run(["python3","-I","/scratch/arthur/baguette-gate-20261124h/tools/e2e/fzn2scp.py",w+"/bag.fzn",w+"/b.scp",w+"/b.names"],120); r["bag_scp"]="ok" if rc==0 else o.strip()[-120:]
shutil.rmtree(w,ignore_errors=True)
print(json.dumps(r),flush=True)
