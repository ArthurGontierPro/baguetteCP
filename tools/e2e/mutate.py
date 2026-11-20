#!/usr/bin/env python3
"""The lane's deliberate corruptions (M14-e2e-verification-T2, D-0176). Each edits one file in
place and prints what it changed, for the lane to check the refusal against.

  mutate.py scp FILE.scp D      the first lin_less_equal/lin_equals: right-hand side + D;
                                prints the constraint's name (cN)
  mutate.py opb FILE.opb        the first row with three terms or more (a model row, not a
                                ladder rung): degree + 1, so it says more than the model;
                                prints its label (@cK)
  mutate.py witness FILE.pbp    the first `@A2[...]` atom definition: witness `-> 1` becomes
                                `-> 0`; prints its label
  mutate.py reif FILE.opb       a WRONG REIFICATION in baguette's .opb (T4, D-0178): the first
                                row of three terms or more whose largest coefficient, 2 or
                                more and on one term only, is on a Boolean's `_ge_1` (not a
                                `_neN` selector) gets that literal's polarity flipped, so
                                its big-M guard fires on the wrong value of the reifier;
                                prints its label (@cK)
  mutate.py copy FILE.pbp       a WRONG DEFINITION of an auxiliary baguette introduces (T5,
                                D-0180): the first `@Y1[...]` red line, which defines a
                                global_cardinality COPY's rung as its original's, gets the
                                witness `Y -> ~X` in place of `Y -> X`; prints its label
Exit 1 when there is nothing to mutate.
"""
import re
import sys


def main(kind, path, *rest):
    text = open(path).read()
    if kind == "scp":
        m = re.search(r"\((c\d+) lin_(less_equal|equals) (\([^)]*\)) (-?\d+)\)", text)
        if not m:
            return 1
        text = text[:m.start(4)] + str(int(m.group(4)) + int(rest[0])) + text[m.end(4):]
        what = m.group(1)
    elif kind == "opb":
        lines = text.splitlines()
        for i, l in enumerate(lines):
            m = re.fullmatch(r"(@\S+ (?:[+-]\d+ \S+ ){3,})>= (-?\d+) ;", l)
            if m:
                lines[i] = f"{m.group(1)}>= {int(m.group(2)) + 1} ;"
                what = l.split()[0]
                break
        else:
            return 1
        text = "\n".join(lines) + "\n"
    elif kind == "reif":
        lines = text.splitlines()
        for i, l in enumerate(lines):
            m = re.fullmatch(r"(@\S+) ((?:[+-]\d+ \S+ ){3,})>= (-?\d+) ;", l)
            if not m:
                continue
            terms = re.findall(r"([+-]\d+) (\S+)", m.group(2))
            top = max(abs(int(c)) for c, _ in terms)
            at = [k for k, (c, v) in enumerate(terms) if abs(int(c)) == top]
            v = terms[at[0]][1] if len(at) == 1 else ""
            if top < 2 or not v.endswith("_ge_1") or v.lstrip("~").startswith("_ne"):
                continue
            terms[at[0]] = (terms[at[0]][0], v[1:] if v.startswith("~") else "~" + v)
            lines[i] = f"{m.group(1)} {' '.join(f'{c} {x}' for c, x in terms)} >= {m.group(3)} ;"
            what = m.group(1)
            break
        else:
            return 1
        text = "\n".join(lines) + "\n"
    elif kind == "copy":
        m = re.search(r"^(@Y1\[[^\]]*\]) red .* -> (\S+) ;$", text, re.M)
        if not m:
            return 1
        text = text[:m.start(2)] + "~" + m.group(2) + text[m.end(2):]
        what = m.group(1)
    elif kind == "witness":
        m = re.search(r"^(@A2\[[^\]]*\]) red .* -> (1) ;$", text, re.M)
        if not m:
            return 1
        text = text[:m.start(2)] + "0" + text[m.end(2):]
        what = m.group(1)
    else:
        return 64
    open(path, "w").write(text)
    print(what)
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
