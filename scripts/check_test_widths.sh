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

A line that genuinely needs a width may name a reason:

    Encoding.declare_int e "w" ~lo:0 ~hi:999  (* width-ok: D-0028 measured shape *)
"""
import pathlib
import re
import sys

ARG = re.compile(r"~(hi|lo):\s*(\(?-?[A-Za-z0-9_./ *+-]+\)?)")
SMALL = re.compile(r"^\(?-?[0-9]{1,4}\)?$")

ROOT = pathlib.Path(__file__).resolve().parent.parent


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


def scan():
    bad = []
    for sub in ("lib", "test", "bin"):
        for path in sorted((ROOT / sub).rglob("*.ml")):
            if "_build" in path.parts:
                continue
            for n, line in enumerate(path.read_text().splitlines(), 1):
                if "width-ok:" in line or line.lstrip().startswith("(*"):
                    continue
                for arg, is_bad in offenders(line):
                    if is_bad:
                        rel = path.relative_to(ROOT)
                        bad.append(f"{rel}:{n}: ~...:{arg}    {line.strip()[:90]}")
    return bad


def self_test():
    """The check must be able to fail. Run with --self-test."""
    must_flag = [
        'Encoding.declare_int e3 "p" ~lo:0 ~hi:(max_int / 3)',  # the real 2026-09-16 bug
        "declare_int e ~lo:0 ~hi:max_int",
        "declare_int e ~lo:0 ~hi:100000",
    ]
    must_pass = [
        'Encoding.declare_int e "x" ~lo:0 ~hi:9',
        "declare_int e ~lo:(-4) ~hi:4",
        "declare_int e2 ~lo:big ~hi:big",  # width 0, however large big is
    ]
    ok = True
    for s in must_flag:
        if not any(b for _, b in offenders(s)):
            print(f"SELF-TEST FAIL: should have flagged: {s}", file=sys.stderr)
            ok = False
    for s in must_pass:
        if any(b for _, b in offenders(s)):
            print(f"SELF-TEST FAIL: should have passed: {s}", file=sys.stderr)
            ok = False
    if not ok:
        return 1
    print("width lint self-test: flags the 2026-09-16 line, passes narrow and width-0")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    found = scan()
    if found:
        print("FAIL a declared domain has a width that is not a small literal:",
              file=sys.stderr)
        for f in found:
            print("  " + f, file=sys.stderr)
        print(
            "\nThe ladder is eager and width-proportional (D-0028/D-0031): one clause per\n"
            "interior value. A wide domain is an allocation loop, not a bigger test.\n"
            "Drive overflow with large COEFFICIENTS against modest domains, or fix the\n"
            "variable (~lo:v ~hi:v -- width 0 costs nothing however large v is).\n"
            "If the width is genuinely needed, mark the line: (* width-ok: reason *)",
            file=sys.stderr)
        sys.exit(1)
    print("width lint: no wide declared domain")
