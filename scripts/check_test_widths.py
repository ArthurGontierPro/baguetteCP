#!/usr/bin/env python3
"""Refuse a declared domain whose WIDTH is large.

Why this exists. Three test binaries had to be killed at the machine's memory ceiling on
2026-09-16. Every one was the same mistake: a wide ``~lo:``/``~hi:`` pair.
``Encoding.declare_int`` writes one ladder clause per interior value (D-0028, D-0031 --
the ladder is eager and width-proportional), so ``~hi:(max_int / 3)`` is not a larger test
case, it is an unbounded allocation loop that never reaches the test body.

WIDTH, not magnitude, is the hazard. ``~lo:big ~hi:big`` is a fixed variable at a huge
value and costs nothing: there are no interior values. That, and large COEFFICIENTS
against modest domains, is how to drive overflow arithmetic.

Each ``~lo:``/``~hi:`` argument is judged ON ITS OWN. The first version of this lint
exempted a whole line when any one argument was a small literal, so the real historical
bug -- ``~lo:0 ~hi:(max_int / 3)`` -- was waved through by its own ``~lo:0``. That is this
project's signature failure mode occurring inside the check written to prevent it, and it
was caught only by running the lint against the line it exists to catch. If you change the
matching here, re-run the self-test at the bottom.

A line that genuinely needs a width may name a reason, in one of two forms.

ON THE LINE. The marker sits on the line that carries the bound:

    Encoding.declare_int e "w" ~lo:0 ~hi:999  (* width-ok: D-0028 measured shape *)

This form does not survive ocamlformat wherever the line is reformatted: a trailing
comment that no longer fits is moved onto a line of its own, after the code, and the
bound loses its marker (M6-T7, found merging M4-T3; test_learn.ml carries the scar, a
``(* width-ok: see above *)`` stranded on the line below the call it was written for).

A REGION, the form that survives formatting (M6-T7, D-0160). Two comments, each on a line
of its own, which ocamlformat leaves where they are:

    (* width-ok-begin: M1-T54, the cap is the subject *)
    E.declare_int e "x" ~lo:0
      ~hi:cap;
    (* width-ok-end *)

Every bound strictly between the two lines is exempt. The region is held to what an
exemption should be, so that it cannot become a quiet way of switching the lint off:

- the begin marker must name a reason on its own line (``width-ok-begin:`` and text);
- a region must be closed, and closed by its own ``width-ok-end``: an unclosed begin, a
  second begin before the end, or an end with no begin is a FAILURE, never a region that
  runs to the end of the file;
- a region may span at most MAX_REGION lines between its markers -- one declaration and
  the call around it, not a test function;
- a region that exempts no labelled bound at all is a failure too: it is stale, and a
  stale exemption is the one that later waves a real bug through.

The markers are recognised only inside a comment that opens on the marker's line
(``(* width-ok-begin:``), so prose that merely names the pragma is not a pragma.

The matcher itself is unchanged by the region form: outside a region, every argument is
judged exactly as before.
"""
import pathlib
import re
import sys

# An argument is EITHER a parenthesised expression -- which may contain spaces,
# e.g. ~hi:(max_int / 3) or ~lo:(-1) -- OR a bare token with none.
#
# The bare alternative deliberately excludes the space that the first version of this
# class allowed. With a space in it, `~hi:5 l (Learn.minimise l)` matched "5 l", which
# is not a small literal, so the lint failed the gate on a width-6 domain. That is a
# lint bug rather than a finding, and it cost a gate run on 2026-09-18. A bound is
# followed by another argument far more often than not, so this shape is common.
ARG = re.compile(r"~(hi|lo):\s*(\([^()]*\)|[A-Za-z0-9_.]+)")
SMALL = re.compile(r"^\(?-?[0-9]{1,4}\)?$")

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The region pragma (M6-T7). Recognised only where a comment OPENS on the marker.
BEGIN = re.compile(r"\(\*\s*width-ok-begin:")
END = re.compile(r"\(\*\s*width-ok-end\b")
# Lines strictly between the markers. One declaration, its call and a reflowed comment
# fit in this; a test function does not.
MAX_REGION = 15


def offenders(text):
    """Yield (argument, is_bad) for each labelled bound in one line.

    Each argument is judged on its own -- see the module docstring for why a
    line-level exemption is wrong. One line-level rule does apply, and it is about
    width rather than about magnitude: if every bound on the line is the SAME text
    (``~lo:big ~hi:big``) the declared width is zero, there are no interior values
    and no ladder, so the magnitude is irrelevant and the line is fine.
    """
    args = [a.strip() for _, a in ARG.findall(text)]
    if not args:
        return
    if len(set(args)) == 1 and len(args) > 1:
        for a in args:
            yield a, False
        return
    for arg in args:
        yield arg, not SMALL.match(arg)


def strip_comments(lines):
    """Blank out OCaml comments, tracking (* *) nesting ACROSS lines.

    The first version skipped only lines that *began* with "(*", so a
    continuation line inside a multi-line comment still matched -- and the lint
    duly failed the gate on a comment that was explaining this very trap. A
    check that fires on prose about the bug is not checking the code.
    """
    depth = 0
    out = []
    for line in lines:
        kept = []
        i = 0
        while i < len(line):
            if line.startswith("(*", i):
                depth += 1
                i += 2
                continue
            if line.startswith("*)", i) and depth:
                depth -= 1
                i += 2
                continue
            if depth == 0:
                kept.append(line[i])
            i += 1
        out.append("".join(kept))
    return out


def regions(raw):
    """Return (exempt line numbers, pragma errors) for one file's lines, 1-based.

    The pragma is read from the RAW lines (it lives in a comment, which
    strip_comments blanks out). Every malformed use is an error rather than a
    silently wider or narrower region; see the module docstring.
    """
    exempt, errors = set(), []
    start = None
    for n, line in enumerate(raw, 1):
        b, e = BEGIN.search(line), END.search(line)
        if b and e:
            errors.append((n, "width-ok-begin and width-ok-end on one line exempt nothing"))
            continue
        if b:
            if start is not None:
                errors.append((n, f"width-ok-begin inside the region opened at line {start}"))
                continue
            if not line[b.end():].split("*)")[0].strip():
                errors.append((n, "width-ok-begin names no reason"))
            start = n
        elif e:
            if start is None:
                errors.append((n, "width-ok-end with no width-ok-begin"))
                continue
            inner = range(start + 1, n)
            if len(inner) > MAX_REGION:
                errors.append((start, f"width-ok region of {len(inner)} lines "
                                      f"(at most {MAX_REGION}): exempt the declaration, "
                                      "not the function"))
            else:
                exempt.update(inner)
            start = None
    if start is not None:
        errors.append((start, "width-ok-begin is never closed by a width-ok-end"))
    return exempt, errors


def judge(raw):
    """Yield (line number, message) for every finding in one file's lines."""
    exempt, errors = regions(raw)
    yield from errors
    used = set()
    for n, (line, code) in enumerate(zip(raw, strip_comments(raw)), 1):
        found = list(offenders(code))
        if n in exempt:
            if found:
                used.add(n)
            continue
        if "width-ok:" in line:
            continue
        for arg, is_bad in found:
            if is_bad:
                yield n, f"~...:{arg}    {line.strip()[:90]}"
    # A region whose lines carry no labelled bound exempts nothing: it is stale.
    if exempt:
        for start, stop in spans(sorted(exempt)):
            if not used & set(range(start, stop + 1)):
                yield start - 1, "width-ok region exempts no ~lo:/~hi: bound (stale marker)"


def spans(lines):
    """Group sorted line numbers into maximal runs of consecutive lines."""
    run = []
    for n in lines:
        if run and n != run[-1] + 1:
            yield run[0], run[-1]
            run = []
        run.append(n)
    if run:
        yield run[0], run[-1]


def scan():
    bad = []
    for sub in ("lib", "test", "bin"):
        for path in sorted((ROOT / sub).rglob("*.ml")):
            if "_build" in path.parts:
                continue
            rel = path.relative_to(ROOT)
            for n, msg in judge(path.read_text().splitlines()):
                bad.append(f"{rel}:{n}: {msg}")
    return bad


def self_test():
    """The check must be able to fail. Run with --self-test."""
    must_flag = [
        'Encoding.declare_int e3 "p" ~lo:0 ~hi:(max_int / 3)',  # the real 2026-09-16 bug
        "declare_int e ~lo:0 ~hi:max_int",
        "declare_int e ~lo:0 ~hi:100000",
        # the same shape as the 2026-09-18 false positive, but genuinely wide: the fix
        # must not have bought its silence by simply matching less
        "declare_int e ~lo:0 ~hi:100000 store other_arg",
        'agree_on ~name:"x" ~lo:0 ~hi:(max_int / 3) l (Learn.minimise l)',
    ]
    must_pass = [
        'Encoding.declare_int e "x" ~lo:0 ~hi:9',
        "declare_int e ~lo:(-4) ~hi:4",
        "declare_int e2 ~lo:big ~hi:big",  # width 0, however large big is
        # 2026-09-18: a bound followed by another argument on the same line. The old
        # character class swallowed the space and read this as "5 l".
        'agree_on ~name:"x" ~lo:(-1) ~hi:5 l (Learn.minimise l)',
        "declare_int e ~lo:0 ~hi:9 store other_arg",
    ]
    # A width mentioned inside a comment is prose, not code. The lint failed the
    # gate on exactly this on 2026-09-16: a comment explaining the trap.
    commented = [
        "   (D-0028), so `~hi:(max_int / 3)` is not a slightly bigger case, it is",
        "(* declare_int e ~lo:0 ~hi:max_int would be an allocation loop *)",
    ]
    ok = True
    for s in commented:
        stripped = strip_comments(["(* a multi-line comment opens here", s, "*)"])
        if any(b for line in stripped for _, b in offenders(line)):
            print(f"SELF-TEST FAIL: flagged a comment: {s}", file=sys.stderr)
            ok = False
    for s in must_flag:
        if not any(b for _, b in offenders(s)):
            print(f"SELF-TEST FAIL: should have flagged: {s}", file=sys.stderr)
            ok = False
    for s in must_pass:
        if any(b for _, b in offenders(s)):
            print(f"SELF-TEST FAIL: should have passed: {s}", file=sys.stderr)
            ok = False
    # M6-T7: the region pragma, the form that survives ocamlformat. Each case is a whole
    # file; the expected result is the set of line numbers judge() reports.
    wide = "  E.declare_int e \"x\" ~lo:0 ~hi:cap;"
    files = [
        ("a region exempts the bound ocamlformat left without its marker",
         ["(* width-ok-begin: M1-T54, the cap is the subject *)",
          "  E.declare_int e \"x\" ~lo:0",
          "    ~hi:cap;", "(* width-ok-end *)"], set()),
        ("a reflowed begin comment still opens the region",
         ["(* width-ok-begin: M1-T54, the cap is the subject, and the reason runs",
          "   on over a second line *)", wide, "(* width-ok-end *)"], set()),
        ("the line AFTER the region is judged again",
         ["(* width-ok-begin: M1-T54 *)", wide, "(* width-ok-end *)", wide], {4}),
        ("the line BEFORE the region is judged too",
         [wide, "(* width-ok-begin: M1-T54 *)", wide, "(* width-ok-end *)"], {1}),
        ("the trailing form still works where nothing moved it",
         [wide + " (* width-ok: M1-T54 *)"], set()),
        ("a trailing marker moved onto the next line by ocamlformat does NOT exempt",
         [wide, "(* width-ok: M1-T54 *)"], {1}),
        ("an unclosed begin is a failure, not a region to the end of the file",
         ["(* width-ok-begin: M1-T54 *)", wide, wide], {1, 2, 3}),
        ("an end with no begin is a failure",
         [wide, "(* width-ok-end *)"], {1, 2}),
        ("a second begin inside a region is a failure",
         ["(* width-ok-begin: a *)", "(* width-ok-begin: b *)", wide,
          "(* width-ok-end *)"], {2}),
        ("a begin without a reason is a failure",
         ["(* width-ok-begin: *)", wide, "(* width-ok-end *)"], {1}),
        # The limit is pinned at 15 here, so that raising MAX_REGION fails the test
        # instead of silently widening every region.
        ("a region of 15 lines is accepted",
         ["(* width-ok-begin: at the limit *)"] + ["  ()"] * 14 + [wide,
          "(* width-ok-end *)"], set()),
        ("a region of 16 lines exempts nothing",
         ["(* width-ok-begin: too long *)"] + ["  ()"] * 15 + [wide,
          "(* width-ok-end *)"], {1, 17}),
        ("a region with no labelled bound in it is stale",
         ["(* width-ok-begin: stale *)", "  let x = 3 in", "(* width-ok-end *)"], {1}),
        ("prose naming the pragma is not a pragma",
         ["(* use a `width-ok-begin:` region here *)", wide], {2}),
    ]
    for what, lines, expected in files:
        got = {n for n, _ in judge(lines)}
        if got != expected:
            print(f"SELF-TEST FAIL: {what}: expected findings at lines "
                  f"{sorted(expected)}, got {sorted(got)}", file=sys.stderr)
            ok = False
    if not ok:
        return 1
    print("width lint self-test: flags the 2026-09-16 line, passes narrow and width-0, "
          "and the width-ok region holds its shape")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    found = scan()
    if found:
        print("FAIL a declared domain has a width that is not a small literal,\n"
              "     or a width-ok region is malformed:",
              file=sys.stderr)
        for f in found:
            print("  " + f, file=sys.stderr)
        print(
            "\nThe ladder is eager and width-proportional (D-0028/D-0031): one clause per\n"
            "interior value. A wide domain is an allocation loop, not a bigger test.\n"
            "Drive overflow with large COEFFICIENTS against modest domains, or fix the\n"
            "variable (~lo:v ~hi:v -- width 0 costs nothing however large v is).\n"
            "If the width is genuinely needed, mark the line: (* width-ok: reason *),\n"
            "or, where ocamlformat moves that comment off the line, wrap the declaration\n"
            "in (* width-ok-begin: reason *) ... (* width-ok-end *), each on its own line.\n"
            "A malformed or stale region is reported here too.",
            file=sys.stderr)
        sys.exit(1)
    print("width lint: no wide declared domain")
