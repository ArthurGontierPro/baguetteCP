#!/usr/bin/env python3
"""M18-coverage-T9 (D-0265): which constraints hold the WIDE order-encoded variables.

The wide order variables are the ones baguette warns about (`warning: variable `x` is declared
over lo..hi`, the width warning fires on an ORDER declaration only, default width 10 000), read
from a run's stderr. For each, the .fzn says which constraints name it (directly or through a
named array), and for the result of an array_int_element over a constant array, how many
DISTINCT values that array has (what a sparse ladder over the occurring values would keep).

usage: wide_holders.py ERR FZN > one line per instance (tab-separated):
  id n_wide sum_width families(width per family, a variable charged to every family naming it)
  n_sparse sparse_width sparse_values other_width: the wide variables that are the result of an
  array_int_element over a constant array or a column of a baguette_table, their declared
  width, and the values they can take by those constraints alone (the intersection over every
  such constraint naming them), which is what a sparse ladder would keep
"""
import collections, os, re, sys

err, fzn = sys.argv[1], sys.argv[2]
ident = os.path.basename(err).rsplit('.', 1)[0]
wide = {}
for m in re.finditer(r"warning: variable `([^`]+)` is declared over (-?\d+)\.\.(-?\d+)", open(err, errors='replace').read()):
    wide[m.group(1)] = int(m.group(3)) - int(m.group(2))

const_arr = {}   # name -> list of ints
var_arr = {}     # name -> list of names
fam = collections.defaultdict(set)      # var -> families
elem_res = {}    # var -> distinct values of its array
tok = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')

def ints(s):
    return [int(x) for x in re.findall(r'-?\d+', s)]

with open(fzn, errors='replace') as f:
    for line in f:
        if line.startswith('array'):
            m = re.match(r'array \[[^\]]*\] of (var )?int: (\w+)[^=]*= \[(.*)\];', line)
            if m:
                if m.group(1):
                    names = [t for t in tok.findall(m.group(3))]
                    if any(n in wide for n in names):
                        var_arr[m.group(2)] = names
                elif len(m.group(3)) < 50_000_000:
                    const_arr[m.group(2)] = m.group(3)
            continue
        if not line.startswith('constraint'):
            continue
        m = re.match(r'constraint (\w+)\((.*)\)', line)
        if not m:
            continue
        name = m.group(1)
        # the arguments without the annotations: up to the ')' that precedes '::' or ';'
        rest = line[line.index('(') + 1:]
        cut = rest.find(')::')
        if cut < 0:
            cut = rest.find(') ::')
        if cut < 0:
            cut = rest.rfind(')')
        args_nos = rest[:cut]
        names = set(tok.findall(args_nos))
        hit = set()
        for n in names:
            if n in wide:
                hit.add(n)
            elif n in var_arr:
                hit.update(x for x in var_arr[n] if x in wide)
        for v in hit:
            fam[v].add(name)
        if name in ('array_int_element', 'array_var_int_element') and hit:
            parts = [p.strip() for p in re.split(r',(?![^\[]*\])', args_nos)]
            if len(parts) == 3 and parts[2] in wide:
                a = parts[1]
                vals = ints(const_arr.get(a, a)) if (a in const_arr or a.startswith('[')) else None
                if vals is not None:
                    sv = set(vals)
                    elem_res[parts[2]] = sv if parts[2] not in elem_res else (elem_res[parts[2]] & sv)
        if name == 'baguette_table' and hit:
            parts = [p.strip() for p in re.split(r',(?![^\[]*\])', args_nos)]
            if len(parts) >= 2:
                xs = var_arr.get(parts[0]) or tok.findall(parts[0])
                t = parts[1]
                vals = ints(const_arr.get(t, t)) if (t in const_arr or t.startswith('[')) else None
                k = len(xs)
                if vals is not None and k > 0:
                    for j, x in enumerate(xs):
                        if x in wide:
                            sv = set(vals[j::k])
                            elem_res[x] = sv if x not in elem_res else (elem_res[x] & sv)

if os.environ.get("WH_DEBUG"):
    for v in wide:
        if v not in elem_res: print("#", v, wide[v], sorted(fam.get(v, [])), file=sys.stderr)
per_fam = collections.Counter()
for v, w in wide.items():
    fs = fam.get(v) or {'(none)'}
    for x in fs:
        per_fam[x] += w
er_w = sum(wide[v] for v in elem_res)
er_d = sum(len(x) for x in elem_res.values())
print('\t'.join([ident, str(len(wide)), str(sum(wide.values())),
                 ','.join('%s:%d' % (k, w) for k, w in per_fam.most_common(6)) or '-',
                 str(len(elem_res)), str(er_w), str(er_d),
                 str(sum(wide.values()) - er_w)]))
