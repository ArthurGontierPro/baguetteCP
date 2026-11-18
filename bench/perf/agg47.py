"""M11-complexity-T1 (D-0140): self-time profile by OWNER and by FUNCTION, from perf.data.

usage:
  agg47.py A.data [ntop]          the profile of one run
  agg47.py A.data B.data [ntop]   the MARGINAL profile of the segment between two runs of the
                                  same instance and mode at two node budgets (A < B): per
                                  symbol, samples(B) - samples(A), as a share of the segment's
                                  samples. The setup and the first A nodes cancel, so a cost that
                                  grows with the run shows as a share that grows.

Samples come from `perf record -F 499` (cycles, user and kernel), so a share is a share of
cycles. Owners: the OCaml module for Baguette symbols, `Stdlib.<Module>`, and coarse buckets for
the runtime (GC/alloc, polymorphic compare and hash, closure calls, strings/IO, other C).
"""
import collections
import re
import subprocess
import sys


def counts(path):
    out = subprocess.run(
        ["perf", "report", "-i", path, "--no-children", "--stdio", "-n",
         "--sort", "symbol", "-g", "none"],
        capture_output=True, text=True).stdout
    c = collections.Counter()
    for line in out.splitlines():
        m = re.match(r"\s*[0-9.]+%\s+(\d+)\s+\[[.k]\]\s+(\S+)", line)
        if m:
            c[re.sub(r"_\d+$", "", m.group(2))] += int(m.group(1))
    return c


def owner(sym):
    mm = re.match(r"Baguette_(core|proof|flatzinc)\.([A-Za-z_]+)\.", sym)
    if mm:
        return mm.group(2)
    if sym.startswith("Stdlib."):
        return "Stdlib." + sym.split(".")[1]
    if sym.startswith("Dune__exe") or sym.startswith("Main"):
        return "Main"
    if re.match(r"caml_(apply|curry|tuplify)", sym):
        return "closure calls"
    if re.search(r"marking|sweep|oldify|darken|minor|major|caml_alloc|try_alloc|"
                 r"caml_initialize|caml_modify|mark_|pool_|caml_make_vect|caml_gc|ephe|"
                 r"finalis|caml_empty_minor|caml_call_gc|caml_garbage|realloc|malloc|free", sym):
        return "GC/alloc"
    if "compare" in sym:
        return "polymorphic compare"
    if "hash" in sym:
        return "polymorphic hash"
    if re.search(r"printf|memmove|memcpy|write|caml_ml_|flush|buffer|caml_string|caml_blit|"
                 r"caml_create_bytes|caml_fill|format", sym, re.I):
        return "strings/IO"
    return "other C/kernel"


def main():
    args = sys.argv[1:]
    ntop = 30
    if args and args[-1].isdigit():
        ntop = int(args.pop())
    if len(args) == 1:
        d = counts(args[0])
        title = args[0]
    else:
        a, b = counts(args[0]), counts(args[1])
        d = collections.Counter({k: b[k] - a.get(k, 0) for k in b})
        title = "%s minus %s" % (args[1], args[0])
    total = sum(v for v in d.values())
    if total <= 0:
        print("no samples")
        return
    by_owner = collections.Counter()
    for k, v in d.items():
        by_owner[owner(k)] += v
    print("profile:", title)
    print("samples:", total)
    print("-- by owner (share of self samples)")
    for k, v in by_owner.most_common(24):
        print("%6.2f%%  %s" % (100.0 * v / total, k))
    print("-- by function (top %d)" % ntop)
    for k, v in d.most_common(ntop):
        print("%6.2f%%  %s" % (100.0 * v / total, k))


main()
