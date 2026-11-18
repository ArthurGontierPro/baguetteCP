import sys, re, subprocess, collections
# M11-T1: from a dwarf perf.data, (1) attribute each sample's self symbol to the NEAREST
# Baguette frame above it (so List.mem / caml_compare / GC land on their caller), and
# (2) inclusive share of every Baguette function (counted once per sample).
# usage: callers47.py perf.data [ntop] [focus-regex]
ntop = int(sys.argv[2]) if len(sys.argv) > 2 else 40
focus = re.compile(sys.argv[3]) if len(sys.argv) > 3 else None
p = subprocess.run(["perf", "script", "-i", sys.argv[1], "-F", "ip,sym"],
                   capture_output=True, text=True)
samples = []; cur = []
for line in p.stdout.splitlines():
    s = line.strip()
    if not s:
        if cur: samples.append(cur); cur = []
        continue
    parts = s.split(None, 1)
    cur.append(parts[1] if len(parts) > 1 else "?")
if cur: samples.append(cur)
def clean(sym):
    sym = re.sub(r"\+0x[0-9a-f]+$", "", sym)
    return re.sub(r"_\d+$", "", sym)
user = [st for st in samples if st and not st[0].startswith(("ctx_", "perf_", "entry_", "do_syscall", "__x64"))]
N = len(user)
attr = collections.Counter(); incl = collections.Counter(); pair = collections.Counter()
for st in user:
    st = [clean(x) for x in st]
    leaf = st[0]
    owner = next((f for f in st if f.startswith("Baguette_")), "(no baguette frame)")
    attr[owner] += 1
    if not leaf.startswith("Baguette_"): pair[(leaf, owner)] += 1
    for f in set(st):
        if f.startswith("Baguette_"): incl[f] += 1
print("user samples:", N)
print("-- self time attributed to nearest Baguette frame (%)")
for k, v in attr.most_common(ntop): print("%6.2f%%  %s" % (100.0 * v / N, k))
print("-- non-Baguette leaf -> nearest Baguette caller (%)")
for (l, o), v in pair.most_common(ntop): print("%6.2f%%  %s  <-  %s" % (100.0 * v / N, l, o))
print("-- inclusive (%)")
items = [(k, v) for k, v in incl.items() if (focus is None or focus.search(k))]
for k, v in sorted(items, key=lambda kv: -kv[1])[:ntop]: print("%6.2f%%  %s" % (100.0 * v / N, k))
