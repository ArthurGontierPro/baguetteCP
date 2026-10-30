#!/usr/bin/env python3
"""M7-T26. The benchmark set of each MiniZinc Challenge edition, as an instance list.

    challenge_lists.py <archive> <out-dir> [YEAR ...]        default: 2011..2026

<archive> is the downloaded ~/mznc-archive (README there): `results/<YEAR>.json`, the
official results page's data, and `probs/mznc<YEAR>_probs.tar.gz`, the official problem
set. The list is built from `results.json`'s `locations` -- the exact (model, data) of
every one of the 100 instances, in `benchmarks` order -- and every path is checked
against the tarball's members, so a row in the list is a file the run will find.

Output `<out-dir>/<YEAR>.lst`, TAB-separated, `#` comment lines first:

    id  model  data  idx  problem  kind  benchmark

`id`     unique in the year, `<YEAR>_<family>_<benchmark>` restricted to [A-Za-z0-9._-]
`model`  path RELATIVE TO THE CORPUS ROOT: `<YEAR>/<family>/<file>.mzn`
`data`   likewise, or `<none>` when the instance is a bare model (2011, 2020's bnn-planner)
`idx`    the instance's index in `results.json` -- the join key for challenge_rank.py
`kind`   SAT | MIN | MAX

The corpus root is laid out one edition per directory, each tarball's single top-level
directory stripped:

    mkdir -p $CORPUS/$Y && tar xzf mznc${Y}_probs.tar.gz -C $CORPUS/$Y --strip-components=1

scripts/compare_run.sh reads the first three columns (INSTANCES=<list>), and the paths it
flattens are `$CORPUS/<model>` and `$CORPUS/<data>`.

Layout facts this encodes, all measured on the 2026-10-30 download:
  * the tarball's top directory is NOT the one `locations` names in 2012-2014 (`probs/`
    there, `mznc12-problems/` in the tarball), so both sides are compared with their
    first component stripped;
  * some problems have a null model path (2014, 2019-2021) while their instances are
    complete; the model is then the one .mzn beside the data (checked to be unique);
  * when the instance path itself ends in .mzn (2011: one model per instance, 2020
    bnn-planner) it IS the model and there is no data file;
  * `locations.instances` is MISALIGNED with `benchmarks` in places (2012 filters swapped,
    2013 l2p rotated, 2014 amaze and cyclic-rcpsp shifted by one), and `benchmarks` is
    what every results column is indexed by. So the instance's file is the one in the
    problem's directory whose name (minus extension) is the benchmark name, and the
    `locations` path is only the fallback (2019 code-generator, whose benchmark names
    drop the `mips_` prefix). Each fallback and disagreement is a `#` line in the list;
  * an instance whose file is in neither place (2014 cyclic-rcpsp easy_5: the tarball
    simply lacks it) is a `# MISSING` line, not a row. challenge_rank.py scores it UNK.

Python 3.8+, standard library only.
"""
import json
import os
import posixpath
import re
import sys
import tarfile

YEARS = tuple(range(2011, 2027))


def strip1(p):
    """`mznc2024_probs//accap/accap.mzn` -> `accap/accap.mzn`."""
    p = re.sub(r"/+", "/", p.strip())
    return p.split("/", 1)[1] if "/" in p else p


def sanitize(s):
    return re.sub(r"[^A-Za-z0-9._-]", "_", s)


def build(archive, year):
    with open(os.path.join(archive, "results", "%d.json" % year)) as f:
        doc = json.load(f)
    R, L = doc["results"], doc["locations"]
    tar = os.path.join(archive, "probs", "mznc%d_probs.tar.gz" % year)
    with tarfile.open(tar) as t:
        members = {strip1(m.name) for m in t.getmembers() if m.isfile()}
    by_dir = {}
    for m in members:
        by_dir.setdefault(posixpath.dirname(m), []).append(m)
    rows, errors, notes, missing, ids = [], [], [], [], set()
    for pi, prob in enumerate(R["problems"]):
        kind = R["kind"][pi]
        ploc = L["problems"][pi] if pi < len(L["problems"]) else None
        pmodel = strip1(ploc) if ploc and ploc != "null" else None
        for i in R["instances"][pi]:
            bench = R["benchmarks"][i]
            iloc = L["instances"][i]
            if not iloc or iloc == "null":
                errors.append("%s/%s (idx %d): no instance path" % (prob, bench, i))
                continue
            ipath = strip1(iloc)
            pdir = posixpath.dirname(ipath)
            # The benchmark name is the authority (see the header); `locations` second.
            named = [m for m in by_dir.get(pdir, [])
                     if posixpath.basename(m) == bench
                     or posixpath.basename(m).rsplit(".", 1)[0] == bench]
            named = [m for m in named if m.endswith((".dzn", ".json", ".mzn"))]
            if len(named) == 1:
                if named[0] != ipath:
                    notes.append("idx %d %s/%s: locations says %s, the benchmark name says %s"
                                 % (i, prob, bench, ipath, named[0]))
                ipath = named[0]
            elif len(named) > 1:
                errors.append("%s/%s (idx %d): %d files named after it: %s"
                              % (prob, bench, i, len(named), named))
                continue
            elif ipath not in members:
                notes.append("MISSING idx %d %s/%s: neither %s nor a file named %s.* is in the "
                             "tarball; challenge_rank.py scores it UNK" % (i, prob, bench, ipath, bench))
                missing.append(i)
                continue
            else:
                notes.append("idx %d %s/%s: no file named after the benchmark; using locations' %s"
                             % (i, prob, bench, ipath))
            if ipath.endswith(".mzn"):
                model, data = ipath, None
            else:
                model, data = pmodel, ipath
                if model is None or model not in members:
                    cands = [m for m in by_dir.get(posixpath.dirname(ipath), [])
                             if m.endswith(".mzn")]
                    if len(cands) == 1:
                        model = cands[0]
                    else:
                        errors.append("%s/%s (idx %d): model %r not in the tarball and "
                                      "%d .mzn beside the data: %s"
                                      % (prob, bench, i, pmodel, len(cands), cands))
                        continue
            for p in (model, data):
                if p is not None and p not in members:
                    errors.append("%s/%s (idx %d): %s is not in the tarball" % (prob, bench, i, p))
            family = model.split("/", 1)[0]
            iid = sanitize("%d_%s_%s" % (year, family, bench))
            if iid in ids:
                errors.append("duplicate id %s" % iid)
            ids.add(iid)
            rows.append((iid, "%d/%s" % (year, model),
                         "%d/%s" % (year, data) if data else "<none>",
                         str(i), prob, kind, bench))
    return rows, errors, notes, missing, len(R["benchmarks"])


def main(argv):
    if len(argv) < 3:
        sys.stderr.write(__doc__)
        return 2
    archive, outdir = argv[1], argv[2]
    years = [int(y) for y in argv[3:]] or YEARS
    os.makedirs(outdir, exist_ok=True)
    bad = 0
    for y in years:
        rows, errors, notes, missing, n = build(archive, y)
        if errors or len(rows) + len(missing) != n:
            bad += 1
            print("%d: %d of %d instances listed, %d error(s)" % (y, len(rows), n, len(errors)))
            for e in errors[:20]:
                print("   " + e)
            continue
        out = os.path.join(outdir, "%d.lst" % y)
        with open(out + ".part", "w") as f:
            f.write("# MiniZinc Challenge %d: the official %d instances, in results.json order "
                    "(M7-T26, tools/compare/challenge_lists.py)\n" % (y, n))
            for note in notes:
                f.write("# " + note + "\n")
            f.write("# id\tmodel\tdata\tidx\tproblem\tkind\tbenchmark\n")
            for r in rows:
                f.write("\t".join(r) + "\n")
        os.replace(out + ".part", out)
        kinds = {}
        for r in rows:
            kinds[r[5]] = kinds.get(r[5], 0) + 1
        print("%d: %d instances%s, %d problems, %s, %d note(s) -> %s"
              % (y, len(rows), " (%d MISSING)" % len(missing) if missing else "",
                 len({r[4] for r in rows}),
                 " ".join("%s %d" % kv for kv in sorted(kinds.items())), len(notes), out))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
