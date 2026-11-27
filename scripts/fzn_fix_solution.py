#!/usr/bin/env python3
"""M19-config-T1 (D-0261). A printed solution, as constraints on its model.

    fzn_fix_solution.py MODEL.fzn SOLVER.out > FIXED.fzn

Reads the LAST solution of SOLVER.out (the block of `name = value;` lines before its last
`----------`) and writes MODEL.fzn again with one `int_eq` or `bool_eq` per printed value
put in front of the solve item, and the solve item replaced by `solve satisfy;`. The printed
solution is a solution of the model exactly when FIXED.fzn is satisfiable, and
scripts/free_model_tests.sh asks that of the fixed search with a proof veripb checks: the
check of a free-search answer that does not compare it byte for byte with the fixed
search's (a satisfaction model may have several solutions, and the two searches may print
different ones).

A scalar `x = 3;` becomes `constraint int_eq(x, 3);` (`bool_eq` for true/false). An array
`x = array1d(1..2, [1, 4]);` (or arrayNd, flattened in row-major order as FlatZinc prints
it) becomes one constraint per element on `x[i]`, 1-based over the flat array, which is how
FlatZinc declares every output array. Exit 2 when the output has no solution or a value
this script cannot read (a set, a float), naming it: a check that cannot be made is never
a pass.
"""
import re
import sys


def die(msg):
    print("fzn_fix_solution: " + msg, file=sys.stderr)
    sys.exit(2)


def last_solution(text):
    lines = text.split("\n")
    ends = [i for i, l in enumerate(lines) if l.strip() == "----------"]
    if not ends:
        die("no solution (no `----------` line) in the solver's output")
    last = ends[-1]
    start = ends[-2] + 1 if len(ends) > 1 else 0
    return [l.strip() for l in lines[start:last] if l.strip()]


def value(tok, where):
    tok = tok.strip()
    if tok in ("true", "false"):
        return "bool_eq", tok
    if re.fullmatch(r"-?[0-9]+", tok):
        return "int_eq", tok
    die("cannot read the value %r of %s" % (tok, where))


def constraints(sol):
    out = []
    for l in sol:
        m = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*);", l)
        if not m:
            die("cannot read the output line %r" % l)
        name, rhs = m.group(1), m.group(2).strip()
        a = re.fullmatch(r"array\d+d\((.*)\[(.*)\]\s*\)", rhs)
        if a:
            elems = [e for e in a.group(2).split(",") if e.strip()]
            for i, e in enumerate(elems, 1):
                p, v = value(e, "%s[%d]" % (name, i))
                out.append("constraint %s(%s[%d], %s);" % (p, name, i, v))
        else:
            p, v = value(rhs, name)
            out.append("constraint %s(%s, %s);" % (p, name, v))
    return out


def main():
    if len(sys.argv) != 3:
        die("usage: fzn_fix_solution.py MODEL.fzn SOLVER.out")
    model = open(sys.argv[1]).read()
    sol = last_solution(open(sys.argv[2]).read())
    cons = constraints(sol)
    # The solve item: the last item that starts with `solve`, to the `;` that ends it.
    m = None
    for m in re.finditer(r"(?m)^\s*solve\b[^;]*;", model):
        pass
    if m is None:
        die("no solve item in %s" % sys.argv[1])
    sys.stdout.write(model[: m.start()] + "\n".join(cons) + "\nsolve satisfy;\n" + model[m.end():])


if __name__ == "__main__":
    main()
