#!/usr/bin/env python3
# M11-complexity-T2 (D-0141). The differential lane's two pure functions, kept out of the
# shell so they can be self-tested without a solver:
#
#   observe.py observe RC STDOUT STDERR [OPB PBP] > OBS
#       What a run SHOWED, as a line-per-item text file: the exit code, every stdout line,
#       the `--stats`/`limit:` counters with their prose stripped, and the sha256 of the
#       .opb and .pbp when the configuration writes a proof.
#   observe.py compare REF NOW LABEL
#       Exit 0 when NOW equals REF on every item both carry, else print ONE failure line
#       naming LABEL, the class of the item and the first item that differs, and exit 1.
#   observe.py --self-test
#       Fabricated observations: equal passes, and each kind of difference fails with the
#       message the lane promises. Runs first on every `make diff`, like `lint`'s.
#
# WHAT IS KEPT FROM STDERR, AND WHY NOT THE WHOLE LINE. The `stats:` lines carry a
# free-text description after their number, and that text is edited for reasons that
# have nothing to do with the search (a reworded comment would turn the lane red and
# invite a re-record, which D-0141 forbids except after a deliberate search change). So
# a counter is kept as `key/unit value [unit value ...]` -- the leading number-unit pairs
# only -- and a non-numeric line only when its value IS data (the LBD and width
# histograms, the retention summary, the first fallback reason). Prose lines are dropped.
# The `limit:` line is kept field by field minus its clocks (cpu, wall, fired) and the
# time-limit setting. `time:` lines (only under --time, which the lane never passes) are
# dropped by construction.
#
# THE CLASSES. Every kept counter is labelled SEARCH or WORK. WORK is how much
# propagation it took to reach the same tree -- propagator runs, wakes, seeds, deferred
# reasons materialised -- and is the class an M11 batch is most likely to move ON
# PURPOSE (D-0138 kept it identical; a watched-literal engine might not). Both classes
# FAIL the lane; the label is there so that a diff that touches WORK only, with every
# SEARCH counter, stdout and both proof hashes equal, reads as what it is.
#
# A KEY PRESENT ON ONE SIDE ONLY IS A NOTE, NOT A FAILURE: a counter added to --stats by
# a later row must not turn the lane red, and a counter removed is visible in the note.
import hashlib
import re
import sys

WORK_KEYS = {
    "props", "eff", "contra", "passes", "deductions", "wakes", "masked", "vetoed",
    "advised", "seeded", "later", "cites",
    "limit.props", "limit.eff", "limit.contra",
}
# `skipped` is printed twice, once as search nodes and once as engine seed slots;
# key/unit tells them apart.
WORK_KEYUNITS = {"skipped/slots"}
DATA_LINES_FIRST = {"lbd", "width"}          # keep the token after the key
DATA_LINES_REST = {"retention", "pb-why", "lvl-why"}  # keep the whole rest
LIMIT_DROP = {"cpu", "wall", "fired", "time-limit"}

NUM = re.compile(r"^-?[0-9]+(\.[0-9]+)?$")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def stat_items(stderr_text):
    """Yield (class, key, value) for every kept counter, in printed order."""
    for line in stderr_text.splitlines():
        if line.startswith("limit:"):
            for k, v in re.findall(r"(\S+?)=(\S+)", line):
                if k in LIMIT_DROP:
                    continue
                key = "limit." + k
                yield ("work" if key in WORK_KEYS else "search", key, v)
            continue
        if not line.startswith("stats:"):
            continue
        t = line.split()[1:]
        if len(t) < 2:
            continue
        key = t[0]
        if NUM.match(t[1]):
            # leading (number, unit) pairs: `991 inst 73.7 runs/node 0.02 eff/node`
            vals, i = [], 1
            while i < len(t) and NUM.match(t[i]):
                vals.append(t[i])
                if i + 1 < len(t):
                    vals.append(t[i + 1])
                i += 2
            unit = vals[1] if len(vals) > 1 else ""
            kk = key + "/" + unit
            family = len(vals) > 2  # the per-family propagator lines (M6-T20)
            cls = "work" if (key in WORK_KEYS or kk in WORK_KEYUNITS or family) else "search"
            yield (cls, kk, " ".join(vals))
        elif key in DATA_LINES_FIRST:
            yield ("search", key, t[1])
        elif key in DATA_LINES_REST:
            yield ("search", key, " ".join(t[1:]))
        # anything else is prose: dropped


def observe(rc, out_path, err_path, opb=None, pbp=None):
    lines = ["rc " + rc.strip()]
    with open(out_path, errors="replace") as f:
        for l in f.read().splitlines():
            lines.append("out " + l)
    with open(err_path, errors="replace") as f:
        err = f.read()
    seen = {}
    for cls, key, val in stat_items(err):
        # a key printed twice keeps both, numbered, so nothing is silently overwritten
        n = seen.get(key, 0)
        seen[key] = n + 1
        k = key if n == 0 else "%s#%d" % (key, n)
        lines.append("%s %s %s" % (cls, k, val))
    if opb is not None:
        lines.append("opb " + sha256(opb))
        lines.append("pbp " + sha256(pbp))
    return "\n".join(lines) + "\n"


def parse(text):
    rc, out, stats, order, hashes = None, [], {}, [], {}
    for l in text.splitlines():
        tag, _, rest = l.partition(" ")
        if tag == "rc":
            rc = rest
        elif tag == "out":
            out.append(rest)
        elif tag in ("search", "work"):
            key, _, val = rest.partition(" ")
            stats[key] = (tag, val)
            order.append(key)
        elif tag in ("opb", "pbp"):
            hashes[tag] = rest
    return rc, out, stats, order, hashes


def compare(ref_text, now_text, label):
    """Return (ok, message). The message names the FIRST differing item."""
    r_rc, r_out, r_st, r_ord, r_h = parse(ref_text)
    n_rc, n_out, n_st, n_ord, n_h = parse(now_text)
    if r_rc != n_rc:
        return False, "DIFF %s: exit code: reference %s, now %s" % (label, r_rc, n_rc)
    for i in range(max(len(r_out), len(n_out))):
        a = r_out[i] if i < len(r_out) else "<no line>"
        b = n_out[i] if i < len(n_out) else "<no line>"
        if a != b:
            return False, "DIFF %s: stdout line %d: reference %r, now %r" % (label, i + 1, a, b)
    for k in r_ord:
        if k in n_st and r_st[k][1] != n_st[k][1]:
            return False, "DIFF %s: %s counter `%s`: reference %s, now %s" % (
                label, r_st[k][0].upper(), k, r_st[k][1], n_st[k][1])
    for h in ("opb", "pbp"):
        if r_h.get(h) != n_h.get(h):
            return False, "DIFF %s: .%s sha256: reference %s, now %s" % (
                label, h, r_h.get(h, "<none>"), n_h.get(h, "<none>"))
    notes = [k for k in r_ord if k not in n_st] + [k for k in n_ord if k not in r_st]
    msg = "ok   %s" % label
    if notes:
        msg += "   (note: counters on one side only, not compared: %s)" % ", ".join(notes)
    return True, msg


SELF_ERR = """stats: nodes            2001 nodes  search-tree nodes visited: the root, plus
stats: Boolean per value (`x >= v`) before any constraint is posted, so the size of
limit: reached time-limit=none cpu=2.35s wall=2.35s nodes=2001 learned=991 props=517 at=node fired=none
stats: skipped             0 nodes  siblings NOT explored: one per backjump (M2-L3)
stats: lbd        5:1,6:3,16:877        M2-L4: learned-clause LBD histogram
stats: learned_clause                  991 inst       73.7 runs/node     0.02 eff/node
stats: props          517082 runs   propagator runs taken off the queue (258.4/node)
stats: skipped       1739699 slots  seed slots SKIPPED as clean (M6-T18)
stats: pb-why                       first fallback reason: no PB row for instance bool2int
"""


def self_test():
    import os
    import tempfile

    fails = []
    d = tempfile.mkdtemp(prefix="observe-selftest-")

    def obs(out, err, rc="0", proof=b"x"):
        p = lambda n: os.path.join(d, n)
        open(p("o"), "w").write(out)
        open(p("e"), "w").write(err)
        open(p("opb"), "wb").write(b"opb")
        open(p("pbp"), "wb").write(proof)
        return observe(rc, p("o"), p("e"), p("opb"), p("pbp"))

    ref = obs("=====UNKNOWN=====\n", SELF_ERR)
    want_in = [
        "search nodes/nodes 2001", "search skipped/nodes 0", "work skipped/slots 1739699",
        "search lbd 5:1,6:3,16:877", "work learned_clause/inst 991 inst 73.7 runs/node 0.02 eff/node",
        "search limit.nodes 2001", "work limit.props 517",
        "search pb-why first fallback reason: no PB row for instance bool2int",
    ]
    for w in want_in:
        if w not in ref.splitlines():
            fails.append("observe lost %r" % w)
    for bad in ("cpu", "wall", "Boolean", "fired", "time-limit"):
        if bad in ref:
            fails.append("observe kept %r, which is a clock or prose" % bad)

    cases = [
        ("equal", ref, True, None),
        ("prose reworded", obs("=====UNKNOWN=====\n", SELF_ERR.replace("search-tree nodes", "tree nodes")), True, None),
        ("clock moved", obs("=====UNKNOWN=====\n", SELF_ERR.replace("cpu=2.35s", "cpu=9.99s")), True, None),
        ("new counter", obs("=====UNKNOWN=====\n", SELF_ERR + "stats: brandnew  7 x  y\n"), True, "note"),
        ("rc", obs("=====UNKNOWN=====\n", SELF_ERR, rc="1"), False, "exit code"),
        ("stdout", obs("x = 1;\n", SELF_ERR), False, "stdout line 1"),
        ("search", obs("=====UNKNOWN=====\n", SELF_ERR.replace("2001 nodes", "2002 nodes")), False, "SEARCH counter `nodes/nodes`"),
        ("work", obs("=====UNKNOWN=====\n", SELF_ERR.replace("517082", "517081")), False, "WORK counter `props/runs`"),
        ("hist", obs("=====UNKNOWN=====\n", SELF_ERR.replace("16:877", "16:876")), False, "SEARCH counter `lbd`"),
        ("pbp", obs("=====UNKNOWN=====\n", SELF_ERR, proof=b"y"), False, ".pbp sha256"),
    ]
    for name, now, want_ok, want_msg in cases:
        ok, msg = compare(ref, now, "self-test [%s]" % name)
        if ok != want_ok or (want_msg and want_msg not in msg):
            fails.append("case %s: ok=%s msg=%s" % (name, ok, msg))
    for f in os.listdir(d):
        os.remove(os.path.join(d, f))
    os.rmdir(d)
    if fails:
        for f in fails:
            print("observe.py self-test FAIL: " + f)
        return 1
    print("observe.py self-test: ok (%d comparison cases, every difference caught)" % len(cases))
    return 0


def main(argv):
    if len(argv) >= 2 and argv[1] == "--self-test":
        return self_test()
    if len(argv) in (5, 7) and argv[1] == "observe":
        sys.stdout.write(observe(argv[2], argv[3], argv[4], *(argv[5:7] or [None, None])))
        return 0
    if len(argv) == 5 and argv[1] == "compare":
        with open(argv[2]) as f:
            ref = f.read()
        with open(argv[3]) as f:
            now = f.read()
        ok, msg = compare(ref, now, argv[4])
        print(msg)
        return 0 if ok else 1
    sys.stderr.write(
        "usage: observe.py observe RC STDOUT STDERR [OPB PBP] | compare REF NOW LABEL "
        "| --self-test\n")
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
