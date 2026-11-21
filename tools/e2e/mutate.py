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
  mutate.py bounds FILE D        a WRONG CLAIMED OPTIMUM (T8, D-0182): the `conclusion BOUNDS
                                LB : ID UB` line of a proof (baguette's .pbp) or of an
                                elaborated core gets LB and UB moved by D, so it claims an
                                optimum D away from the one found (in the PB objective's
                                numbers, which are minimised: D < 0 claims a better one);
                                prints the new `LB UB`
  mutate.py pin FILE.opb FILE.pbp
                                (T3, D-0187) the row `opb` would pick in baguette's .opb, but
                                corrupted where the SOLVER-WRITTEN prefix states it: that
                                row's pin line in the --e2e proof (`@cK ia ROW : ..`,
                                `@cK rup ROW` or, T6, `@cK pbc ROW : subproof`) gets its
                                degree + 1, so the prefix claims more
                                than cake's file implies; a pin that is one `pol` (T3b,
                                D-0188) becomes that pol under `@Wmut` and `@cK ia ROW : @Wmut`
                                with the degree + 1; the .opb is not touched; prints @cK
  mutate.py sel FILE.pbp        (T3, D-0187) a WRONG DEFINITION of a disequality selector:
                                the first `@D1[...]` red line, `~s + F >= 1 : s -> F`, gets
                                the witness `s -> ~F`; prints its label. (T6, D-0195: on an
                                int_abs model the first is the sign guard's, F = x_ge_0)
  mutate.py flag FILE.pbp       (T6, D-0195) a WRONG DEFINITION of a regular state flag: the
                                first `@D1[...]` whose F is cake's flag past layer 0 gets the
                                witness `s -> ~F`; prints its label
  mutate.py bitdef FILE.pbp     (T7, D-0196) a WRONG DEFINITION of a bits-arm bit: the first
                                variable's digit-0 pair `@BP[x_bit_0]`, `@BN[x_bit_0]` (both
                                red lines, still valid definitions of a fresh variable) gets
                                cake's `i[X][b1]` where it reads `i[X][b0]`, so x_bit_0 is
                                defined as the wrong cake bit; the first line that depends on
                                it is the variable's bound-row pin against @BU (the halves no
                                longer telescope), on the first variable whose ub row is not
                                a tautology; prints that pin's label (@cK)
  mutate.py tight FILE.pbp      (T7, D-0196) the first row derived by contradiction against a
                                bits variable's ub row (`@cK pbc ROW : subproof` whose second
                                step cites @BU) gets its degree + 1; prints @cK
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
    elif kind == "pin":
        what = row = None
        for l in text.splitlines():
            m = re.fullmatch(r"(@\S+) ((?:[+-]\d+ \S+ ){3,})>= (-?\d+) ;", l)
            if m:
                what, row = m.group(1), m
                break
        if what is None:
            return 1
        path = rest[0]
        lines = open(path).read().splitlines()
        for i, l in enumerate(lines):
            m = re.fullmatch(re.escape(what) + r" (ia|rup) ((?:[+-]\d+ \S+ )+)>= (-?\d+)( : \S+)? ;", l)
            if not m:
                # T6 (D-0195): a row derived by contradiction, `@cK pbc ROW : subproof`
                m = re.fullmatch(re.escape(what) + r" (pbc) ((?:[+-]\d+ \S+ )+)>= (-?\d+)( : subproof)", l)
                if m:
                    lines[i] = f"{what} pbc {m.group(2)}>= {int(m.group(3)) + 1} : subproof"
                    break
            if m:
                lines[i] = f"{what} {m.group(1)} {m.group(2)}>= {int(m.group(3)) + 1}{m.group(4) or ''} ;"
                break
            # T3b (D-0188): a pin that IS one pol of a linearised cake row states no row;
            # the corruption states it, with degree + 1, as an `ia` against that pol
            m = re.fullmatch(re.escape(what) + r" pol (.*) ;", l)
            if m:
                lines[i] = (f"@Wmut pol {m.group(1)} ;\n"
                            f"{what} ia {row.group(2)}>= {int(row.group(3)) + 1} : @Wmut ;")
                break
        else:
            return 1
        text = "\n".join(lines) + "\n"
    elif kind == "sel":
        m = re.search(r"^(@D1\[[^\]]*\]) red .* -> (~?)(\S+) ;$", text, re.M)
        if not m:
            return 1
        text = text[:m.start(2)] + ("" if m.group(2) else "~") + text[m.end(2):]
        what = m.group(1)
    elif kind == "flag":
        # T6 (D-0195): the first regular state flag past layer 0 (cake's x[cK][<i>_<q>][st]
        # with i >= 1, not fixed by `st0`), defined with the witness s -> ~F
        m = re.search(r"^(@D1\[[^\]]*\]) red .* -> (~?)(x\[c\d+\]\[[1-9]\d*_\d+\]\[st\]) ;$", text, re.M)
        if not m:
            return 1
        text = text[:m.start(2)] + ("" if m.group(2) else "~") + text[m.end(2):]
        what = m.group(1)
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
    elif kind == "bitdef":
        lines = text.splitlines()
        # the first variable whose ub row is not a tautology (u - l < 2^n - 1), so that its pin
        # judges the halves: S <= 7 over three bits holds whatever the bits mean
        for l in lines:
            m = re.fullmatch(r"(@c\d+) ia ((?:[+-]\d+ \S+ )+)>= (-?\d+) : @BU\[(\S+)\] ;", l)
            if m and -int(m.group(3)) < sum(-int(c) for c in re.findall(r"([+-]\d+) ", m.group(2))):
                pin, x = m.group(1), m.group(4)
                break
        else:
            return 1
        mm = re.search(r"^@BP\[" + re.escape(x) + r"_bit_0\] red .*?\bi\[([^\]]+)\]\[b0\]", text, re.M)
        if not mm:
            return 1
        X = mm.group(1)
        n = 0
        for i, l in enumerate(lines):
            if l.startswith((f"@BP[{x}_bit_0] red ", f"@BN[{x}_bit_0] red ")):
                lines[i] = l.replace(f"i[{X}][b0]", f"i[{X}][b1]")
                n += 1
        if n != 2:
            return 1
        text = "\n".join(lines) + "\n"
        what = pin
    elif kind == "tight":
        # T7 (D-0196): the first row derived by contradiction against a bits ub row, its
        # degree + 1 (on either path's proof)
        lines = text.splitlines()
        for i, l in enumerate(lines):
            m = re.fullmatch(r"(@\S+) pbc ((?:[+-]\d+ \S+ )+)>= (-?\d+) : subproof", l)
            if m and i + 2 < len(lines) and "@BU[" in lines[i + 2]:
                lines[i] = f"{m.group(1)} pbc {m.group(2)}>= {int(m.group(3)) + 1} : subproof"
                what = m.group(1)
                break
        else:
            return 1
        text = "\n".join(lines) + "\n"
    elif kind == "bounds":
        m = re.search(r"^conclusion BOUNDS (-?\d+)( : \S+ )(-?\d+)", text, re.M)
        if not m:
            return 1
        d = int(rest[0])
        lb, ub = int(m.group(1)) + d, int(m.group(3)) + d
        text = text[:m.start(1)] + f"{lb}{m.group(2)}{ub}" + text[m.end(3):]
        what = f"{lb} {ub}"
    else:
        return 64
    open(path, "w").write(text)
    print(what)
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
