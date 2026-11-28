#!/usr/bin/env python3
# M18-coverage-T9 (D-0265): the .opb rows Encoding.add_all_different writes for a .fzn, one per
# (unordered pair of an all_different_int scope, shared declared value), and the scope sizes.
# usage: alldiff_rows.py FZN  ->  n_alldiff max_scope rows
import re,sys
dom={}; varr={}; rows=0; n_ad=0; maxn=0
for line in open(sys.argv[1]):
    if line.startswith('var '):
        m=re.match(r'var (-?\d+)\.\.(-?\d+): (\w+)',line)
        if m: dom[m.group(3)]=(int(m.group(1)),int(m.group(2)))
        else:
            m=re.match(r'var \{([-\d, ]+)\}: (\w+)',line)
            if m:
                v=[int(x) for x in m.group(1).split(',')]; dom[m.group(2)]=(min(v),max(v))
    elif line.startswith('array') and 'of var int' in line:
        m=re.match(r'array \[[^\]]*\] of var int: (\w+)[^=]*= \[(.*)\];',line)
        if m: varr[m.group(1)]=[x.strip() for x in m.group(2).split(',')]
    elif line.startswith('constraint all_different_int('):
        a=line[len('constraint all_different_int('):].split(')')[0].strip()
        xs=varr.get(a) or [x.strip() for x in a.strip('[]').split(',')]
        xs=[x for x in xs if x in dom]
        n_ad+=1; maxn=max(maxn,len(xs))
        for i in range(len(xs)):
            for j in range(i+1,len(xs)):
                lo=max(dom[xs[i]][0],dom[xs[j]][0]); hi=min(dom[xs[i]][1],dom[xs[j]][1])
                rows+=max(0,hi-lo+1)
print(n_ad, maxn, rows)
