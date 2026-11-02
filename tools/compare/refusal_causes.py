#!/usr/bin/env python3
"""Why baguette refused each Challenge instance, from the run directories themselves.

D-0121 counted 388 "width" refusals and 145 "heap" refusals. That split came from the
`detail` column of results.tsv, which keeps the first 180 characters of stderr -- and the
width WARNING is printed first, so any later death inherited the word "width". This script
reads the whole stderr instead and classifies by what actually ended the run (D-0123):

  exit 5, "heap budget is exhausted"   the --max-heap-mb guard (M7-T8), split three ways
                                       by its own message:
     A  0 clauses minted             -> died before the first declare_int (front end)
     B  >0 clauses, no variable named -> the asynchronous Gc alarm, after the encoding
                                          (rows, propagator set-up, or the search)
     C  "most recently for `x`"        -> the synchronous check inside a ladder loop
  everything else                      the first error line of stderr

Usage: python3 -I tools/compare/refusal_causes.py /scratch/arthur/m7t26 [--widths]
  <runs> holds one directory per edition (2011 .. 2026), each with results.tsv, log/, work/.
  --widths also sums the DECLARED widths of each refused model's `var lo..hi` lines, and says
  what share the objective is; it needs the work/*.fzn files, which only refused runs keep.
Standard library only; read-only over the run directories.
"""
import glob, os, re, sys

R_ENC = re.compile(r"encoding built so far is (\d+) clauses and values(, most recently for `([^`]*)`)?")
R_HEAP = re.compile(r"heap has reached (\d+) MB")
R_WARN = re.compile(r"warning: variable `([^`]*)` is declared over (-?\d+)\.\.(-?\d+)")
R_DECL = re.compile(r"^var\s+(-?\d+)\s*\.\.\s*(-?\d+)\s*:\s*(\w+)")
R_RC = re.compile(r"rc=(\d+)")


def pct(v, p):
    v = sorted(v)
    return v[min(len(v) - 1, int(p * len(v)))] if v else None


def refused_rows(root):
    for y in sorted(glob.glob(os.path.join(root, "20??"))):
        tsv = os.path.join(y, "results.tsv")
        if not os.path.exists(tsv):
            continue
        for line in open(tsv, errors="replace"):
            f = line.rstrip("\n").split("\t")
            if len(f) >= 12 and f[1] == "baguette" and f[2] == "REFUSED":
                yield y, f[0], f[-1]


def first_error(err):
    for l in err.splitlines():
        if l.startswith(" ") or l.startswith("baguette: warning") or not l.strip():
            continue
        m = re.search(r"error: [^:]{0,60}|budget is exhausted|Fatal[^.]{0,60}|exceeds[^.]{0,60}", l)
        if m:
            return re.sub(r"`[^`]*`", "`X`", m.group(0))
    return "<no error line>"


def declared_widths(fzn, objective):
    tot, top, objw = 0, 0, None
    for l in open(fzn, errors="replace"):
        m = R_DECL.match(l)
        if m:
            w = int(m[2]) - int(m[1])
            tot += w
            top = max(top, w)
            if m[3] == objective:
                objw = w
    return tot, top, objw


def main():
    root = sys.argv[1]
    widths = "--widths" in sys.argv
    causes, fam = {}, {"A": [], "B": [], "C": []}
    wrows = []
    for y, ident, detail in refused_rows(root):
        errf = os.path.join(y, "log", ident + ".baguette.err")
        err = open(errf, errors="replace").read() if os.path.exists(errf) else ""
        rc = R_RC.search(detail)
        key = ("rc=" + rc[1] if rc else "rc=?") + " | " + first_error(err)
        causes[key] = causes.get(key, 0) + 1
        if "heap budget is exhausted" not in err:
            continue
        c = R_ENC.search(err)
        clauses = int(c[1]) if c else -1
        who = (c[3] or "") if c else ""
        h = R_HEAP.search(err)
        warned = {m[1]: int(m[3]) - int(m[2]) for m in R_WARN.finditer(err)}
        rec = (clauses, who, int(h[1]) if h else -1, len(warned))
        fam["A" if clauses == 0 else ("C" if who else "B")].append(rec)
        if widths:
            fzn = os.path.join(y, "work", ident + ".baguette.fzn")
            if os.path.exists(fzn):
                obj = None
                for l in open(fzn, errors="replace"):
                    if l.startswith("solve"):
                        mm = re.search(r"(minimize|maximize)\s+(\w+)", l)
                        obj = mm[2] if mm else None
                wrows.append(declared_widths(fzn, obj))
    print("## what ended each refused run (rc | first error line)")
    for k, n in sorted(causes.items(), key=lambda kv: -kv[1]):
        print(f"{n:5d}  {k}")
    print("\n## the heap-budget deaths, by the guard's own message")
    for k, label in (("A", "0 clauses minted: before the first declaration (front end)"),
                     ("B", ">0 clauses, no variable named: after the encoding (Gc alarm)"),
                     ("C", "a variable named: inside a ladder loop")):
        v = fam[k]
        if not v:
            print(f"{k}: 0")
            continue
        cl = [r[0] for r in v]
        print(f"{k}: {len(v):4d}  {label}")
        print(f"      clauses minted at death p10/p50/p90 = {pct(cl,.1)} / {pct(cl,.5)} / {pct(cl,.9)};"
              f" with a width warning: {sum(1 for r in v if r[3] > 0)};"
              f" named variable is `objective`: {sum(1 for r in v if r[1] == 'objective')}")
    if widths and wrows:
        objs = [r for r in wrows if r[2] is not None]
        print(f"\n## declared widths of {len(wrows)} refused models with a kept .fzn ({len(objs)} with an objective)")
        print(f"objective is the widest variable: {sum(1 for r in objs if r[2] >= r[1])}")
        print(f"objective >= 1e4 wide: {sum(1 for r in objs if r[2] >= 10_000)}")
        print(f"objective share of the summed width >= 0.5: {sum(1 for r in objs if r[0] and r[2] / r[0] >= 0.5)}"
              f"   >= 0.9: {sum(1 for r in objs if r[0] and r[2] / r[0] >= 0.9)}")
        print(f"summed width p10/p50/p90: {pct([r[0] for r in wrows],.1)} / {pct([r[0] for r in wrows],.5)} / {pct([r[0] for r in wrows],.9)}")
        print(f"summed width < 1e6: {sum(1 for r in wrows if r[0] < 1e6)}   < 1e7: {sum(1 for r in wrows if r[0] < 1e7)}")


if __name__ == "__main__":
    main()
