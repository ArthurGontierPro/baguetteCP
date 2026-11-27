#!/usr/bin/env python3
"""Which global constraints the Challenge editions use, against what baguette propagates
natively, joined with baguette's outcome on each instance. Written for M7-T26 (the Challenge
editions as benchmark sets); its first table is D-0122, what the 1 600 instances ask for
against what baguette propagates.

    challenge_globals.py <archive> <lists-dir> [<runs-dir>] [--min=20] [--arm=A] [--mznlib=DIR]

<archive>   the downloaded Challenge archive, /scratch/arthur/mznc-archive on the node
            (~/mznc-archive on the laptop), read for probs/mznc<Y>_probs.tar.gz
<lists-dir> bench/challenge (the <Y>.lst files written by challenge_lists.py)
<runs-dir>  a directory holding <Y>/results.tsv from scripts/compare_run.sh, or a series
            directory whose ARMS hold it (<runs-dir>/<arm>/<Y>/results.tsv, as
            M10-search-strategy-T5's /scratch/arthur/m10t5 and the M17 series of
            bench/series/); --arm picks the arm, default the first in name order. Without
            <runs-dir> only the usage census is printed.
--min       the fewest instances a global must appear in to get a row (default 20).
--mznlib    the library the NATIVE set is read from; default the mznlib/ of this checkout.

Output on stdout: `#` lines (the run directory, the instance count and the native set), then
one TAB-separated row per global. Exit 0; 2 with this text on stderr when <archive> or
<lists-dir> is not given; a <runs-dir> with no results.tsv (or no arm --arm names) stops with a
message and status 1.

An instance "uses" a global when its model, or a .mzn it includes from its own directory,
calls it outside a comment. A NATIVE global is one mznlib routes to a baguette propagator,
and the set is READ FROM mznlib/ (since M18-coverage-T0, which replaced a hand-kept list that
had gone stale), never listed here: every
fzn_<g>[_int|_bool|_set].mzn names <g>, and a body-less array_int_<g> declaration (the
FlatZinc builtin kept whole, as maximum/minimum) names <g>. `element` is the one native
with no mznlib file, because array_int_element is a FlatZinc builtin (SPEC 2.1) that std
already emits. Every other global reaches baguette decomposed by the MiniZinc standard
library.
`VAR-SET` and `VAR-FLOAT` mark models declaring such variables (also decomposed, or refused).

Outcome columns are baguette's harness statuses. REFUSED is the FRONT END refusing the
model before any search (exit 2 or 3: width wall, heap budget, an unsupported shape); it is
not a proof rejected by the checker, which would be `check_verdict` REJECTED, a column this
census does not read (an answer is counted by its status whatever its proof's verdict).
`complete%` is OPT+UNSAT over the instances actually attempted (not REFUSED,
not FLATTEN-FAIL). A SAT answer is complete when the model has no objective (the `kind` column of
the .lst is SAT) and goes to its own column `SAT-satisfied`, counted in `complete%`; on a MIN or
MAX model it stays an incumbent. (M18-coverage-T12 made that split, after D-0232 section 1
found the census counting a satisfaction model's SAT as an incumbent.)

Python 3.8+, standard library only.
"""
import collections
import csv
import os
import posixpath
import re
import sys
import tarfile

GLOBALS = """alldifferent all_different alldifferent_except_0 all_equal among at_least at_most
exactly bin_packing bin_packing_capa bin_packing_load circuit subcircuit count count_eq
count_leq count_geq count_lt count_gt count_neq cumulative cumulatives diffn diffn_nonstrict
disjunctive disjunctive_strict distribute element global_cardinality global_cardinality_closed
global_cardinality_low_up global_cardinality_low_up_closed increasing decreasing
strictly_increasing strictly_decreasing int_set_channel inverse inverse_set knapsack lex_less
lex_lesseq lex_greater lex_greatereq lex2 strict_lex2 link_set_to_booleans maximum minimum
member network_flow network_flow_cost nvalue partition_set range regular regular_nfa roots
sliding_sum sort arg_sort sum_pred table value_precede value_precede_chain arg_max arg_min
geost geost_bb piecewise_linear span seq_precede_chain symmetric_all_different""".split()
# MiniZinc's own aliases: the census matches either spelling in a model.
ALIASES = {"all_different": ["alldifferent"]}
FZN_FILE = re.compile(r"^fzn_(\w+?)(?:_int|_bool|_set)?\.mzn$")
BODYLESS_BUILTIN = re.compile(r"^predicate\s+array_int_(\w+)\s*\([^=]*?\)\s*;", re.M | re.S)


def native_from_mznlib(d):
    """The globals mznlib routes to a propagator: its fzn_ files, the FlatZinc builtins it
    redeclares body-less, and array_int_element, which std emits as it is."""
    out = {"element"}
    for f in sorted(os.listdir(d)):
        m = FZN_FILE.match(f)
        if m:
            out.add(m.group(1))
        if f.endswith(".mzn"):
            out.update(BODYLESS_BUILTIN.findall(open(os.path.join(d, f)).read()))
    for g in list(out):
        out.update(ALIASES.get(g, []))
    return out


NATIVE = set()
CALL = re.compile(r"\b(" + "|".join(sorted(set(GLOBALS), key=len, reverse=True)) + r")\s*\(")
SETVAR = re.compile(r"\bvar\s+set\s+of\b")
FLOATVAR = re.compile(r"\bvar\s+float\b")
INCLUDE = re.compile(r'include\s+"([^"]+)"')


def strip1(p):
    p = re.sub(r"/+", "/", p.strip())
    return p.split("/", 1)[1] if "/" in p else p


def census(archive, lists, year):
    rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(lists, "%d.lst" % year))
            if not l.startswith("#")]
    texts = {}
    with tarfile.open(os.path.join(archive, "probs", "mznc%d_probs.tar.gz" % year)) as t:
        for m in t.getmembers():
            if m.isfile() and m.name.endswith(".mzn"):
                texts[strip1(m.name)] = t.extractfile(m).read().decode("utf-8", "replace")

    def model_text(rel):
        base, seen, out, todo = rel.split("/", 1)[1], set(), [], []
        todo.append(base)
        while todo:
            f = todo.pop()
            if f in seen or f not in texts:
                continue
            seen.add(f)
            out.append(texts[f])
            todo += [posixpath.join(posixpath.dirname(f), i) for i in INCLUDE.findall(texts[f])]
        return "\n".join(out)

    uses = {}
    for r in rows:
        txt = re.sub(r"%.*", "", model_text(r[1]))
        found = set(CALL.findall(txt))
        if SETVAR.search(txt):
            found.add("VAR-SET")
        if FLOATVAR.search(txt):
            found.add("VAR-FLOAT")
        uses[r[0]] = (found, r[4], r[5] if len(r) > 5 else "")
    return uses


def arm_dir(runs, arm):
    """<runs> itself when it holds <Y>/results.tsv, else its arm <arm> (or the first arm)."""
    has = lambda d: any(os.path.exists(os.path.join(d, str(y), "results.tsv")) for y in range(2011, 2027))
    if has(runs):
        return runs
    arms = sorted(a for a in os.listdir(runs) if os.path.isdir(os.path.join(runs, a)) and has(os.path.join(runs, a)))
    if not arms or (arm and arm not in arms):
        sys.exit("challenge_globals: no <Y>/results.tsv under %s%s (arms: %s)"
                 % (runs, " for arm " + arm if arm else "", " ".join(arms) or "none"))
    return os.path.join(runs, arm or arms[0])


def outcomes(runs, year):
    out = {}
    p = os.path.join(runs, str(year), "results.tsv")
    if not os.path.exists(p):
        return out
    for r in csv.reader(open(p), delimiter="\t"):
        if len(r) > 5 and r[1] == "baguette":
            st = r[2]
            if st == "TIMEOUT" and int(r[5] or 0) > 0:
                st = "TIMEOUT+inc"
            out[r[0]] = st
    return out


def main(argv):
    args = [a for a in argv[1:] if not a.startswith("--")]
    opts = dict(a[2:].split("=", 1) for a in argv[1:] if a.startswith("--"))
    if len(args) < 2:
        sys.stderr.write(__doc__)
        return 2
    archive, lists = args[0], args[1]
    runs = args[2] if len(args) > 2 else None
    minimum = int(opts.get("min", 20))
    here = os.path.dirname(os.path.abspath(__file__))
    NATIVE.update(native_from_mznlib(opts.get("mznlib", os.path.join(here, "..", "..", "mznlib"))))
    if runs:
        runs = arm_dir(runs, opts.get("arm"))
        print("# outcomes from %s" % runs)
    per_year = {}
    for y in range(2011, 2027):
        if os.path.exists(os.path.join(lists, "%d.lst" % y)):
            per_year[y] = (census(archive, lists, y), outcomes(runs, y) if runs else {})
    n = collections.Counter()
    probs = collections.defaultdict(set)
    years = collections.defaultdict(collections.Counter)
    agg = collections.defaultdict(collections.Counter)
    for y, (uses, outs) in per_year.items():
        for iid, (gs, prob, kind) in uses.items():
            st = outs.get(iid, "-")
            if st == "SAT" and kind == "SAT":
                st = "SAT-satisfied"
            keys = list(gs) + ([] if gs - NATIVE else ["(native globals only, or none)"])
            for g in keys:
                n[g] += 1
                probs[g].add("%d/%s" % (y, prob))
                years[g][y] += 1
                agg[g][st] += 1
    total = sum(len(u) for u, _ in per_year.values())
    print("# %d instances in %d editions; natives: %s" % (total, len(per_year), " ".join(sorted(NATIVE))))
    hdr = ["global", "instances", "problems", "native"]
    if runs:
        hdr += ["REFUSED", "OPT+UNSAT", "SAT-satisfied", "incumbent", "TIMEOUT-empty", "other", "complete%"]
    hdr += ["per-year"]
    print("\t".join(hdr))
    for g, k in n.most_common():
        if k < minimum:
            continue
        c = agg[g]
        line = [g, str(k), str(len(probs[g])), "yes" if g in NATIVE else ""]
        if runs:
            ref, sat = c["REFUSED"], c["SAT-satisfied"]
            comp = c["OPT"] + c["UNSAT"] + sat
            inc, te = c["TIMEOUT+inc"] + c["SAT"], c["TIMEOUT"]
            att = k - ref - c["FLATTEN-FAIL"]
            line += [str(ref), str(comp - sat), str(sat), str(inc), str(te), str(k - ref - comp - inc - te),
                     "%.0f" % (100.0 * comp / att) if att else "-"]
        line.append(" ".join("%d:%d" % (y, years[g][y]) for y in sorted(years[g])))
        print("\t".join(line))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
