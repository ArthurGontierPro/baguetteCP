#!/usr/bin/env python3
"""FlatZinc -> .scp, the input of CakeML's verified CP encoder `cake_pb_cp` (M14-e2e-verification-T2).

Usage: python3 -I fzn2scp.py MODEL.fzn OUT.scp OUT.names

This translator is TRUSTED: the verified chain of D-0174 starts at the .scp, so a wrong
translation here verifies (GCS's issue #987 was exactly that). It is therefore kept small,
and it shares NOTHING with baguette's front end (lib/flatzinc/): its own scanner, its own
parser, its own reading of each builtin (D-0174 section 5). A parsing bug common to both
would otherwise be invisible. Its validation is `tools/e2e/scpsem.py` against Gecode's
FlatZinc interpreter, in the lane (D-0176).

Covered, and nothing else (anything else is refused, exit 2, with one line on stderr that
starts `UNCOVERED:` and names the first construct it cannot translate):

  int_lin_le(as, xs, c)   sum as_i xs_i <= c    (c lin_less_equal (a1 x1 ...) c)
  int_lin_eq(as, xs, c)   sum as_i xs_i  = c    (c lin_equals ...)
  int_lin_ne(as, xs, c)   sum as_i xs_i != c    (c lin_not_equals ...)
  int_le(a, b)            a <= b                (c less_equal a b)
  int_lt(a, b)            a <  b                (c less_than a b)
  int_eq(a, b)            a  = b                (c equals a b)
  int_ne(a, b)            a != b                (c not_equals a b)
  all_different_int(xs)   pairwise distinct     (c all_different (x1 ...))

  The Boolean family and the reified forms (M14-e2e-verification-T4, D-0178). A FlatZinc
  Boolean is cake's integer 0..1, so `b` true is the reify tuple `(b = 1)`, `b` false is
  `(b = 0)`, and a constant Boolean is the tuple `(1 = 1)` or `(0 = 1)` (cake's varc
  accepts an integer). Each is the cake keyword whose HOL4 meaning is the builtin's own:

  bool_clause(ps, ns)     some ps_i true or some ns_j false (c or ((p1 = 1) ... (n1 = 0) ...) (1 = 1))
  array_bool_or(as, r)    r <-> OR_i as_i              (c or ((a1 = 1) ...) (r = 1))
  array_bool_and(as, r)   r <-> AND_i as_i             (c and ((a1 = 1) ...) (r = 1))
  bool_eq(a, b)           a = b                        (c equals a b)
  bool_not(a, b)          a != b, i.e. a = not b       (c not_equals a b)
  bool2int(b, x)          x = b                        (c equals b x)
  int_le_reif(a, b, r)    r <-> a <= b                 (c less_equal_iff (r = 1) a b)
  int_eq_reif(a, b, r)    r <-> a = b                  (c equals_iff (r = 1) a b)
  int_ne_reif(a, b, r)    r <-> a != b                 (c not_equals_iff (r = 1) a b)
  int_lin_le_reif(as, xs, c, r)  r <-> sum as_i xs_i <= c
                                              (c lin_less_equal_iff (r = 1) (a1 x1 ...) c)

  These are every Boolean and reified builtin of SPEC section 2.1 (M2, M3); SPEC has no
  `bool_lin_*`, `int_lin_eq_reif` or `int_lt_reif`, so neither does this table.

  `var lo..hi` and `var bool` (as 0..1) variables, arrays of them, aliases (`= y`, with the
  alias's own domain kept as a constraint on y when it is narrower), parameters and constant
  arrays (written in place: .scp accepts an integer wherever a variable may stand), set
  domains with holes (bounds plus `(dN in (v1 ...) x)`), annotations (ignored: they do not
  change the solutions), `solve satisfy` (with or without a search annotation).

Refused: `var int` with no domain (cake needs bounds, and a bound the translator invented
would change the model), an objective (M14-T8), floats, sets as values, and every builtin
not listed above. When a model has an uncovered builtin, that is the reason given, the first
one in file order, whatever else the model also has.

OUT.names is one line per .scp variable, `SCP_NAME FLATZINC_NAME`, for the bridge (which
needs to find baguette's name of each variable) and for the validator.
"""
import re
import sys

COVERED = (
    "int_lin_le", "int_lin_eq", "int_lin_ne",
    "int_le", "int_lt", "int_eq", "int_ne",
    "all_different_int",
    "bool_clause", "array_bool_or", "array_bool_and", "bool_eq", "bool_not", "bool2int",
    "int_le_reif", "int_eq_reif", "int_ne_reif", "int_lin_le_reif",
)


class Uncovered(Exception):
    pass


# ---------------------------------------------------------------- scanner

TOKEN = re.compile(r"""
    (?P<ws>\s+|%[^\n]*)
  | (?P<range>\.\.)
  | (?P<int>-?\d+)
  | (?P<id>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<str>"(?:[^"\\]|\\.)*")
  | (?P<punct>::|[\[\](){},:;=])
""", re.VERBOSE)


def scan(text):
    pos, out = 0, []
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m:
            raise Uncovered(f"unexpected character {text[pos]!r} at offset {pos}")
        pos = m.end()
        kind = m.lastgroup
        if kind == "ws":
            continue
        out.append((kind, m.group(kind)))
    return out


class Parser:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else (None, None)

    def next(self):
        tok = self.peek()
        self.i += 1
        return tok

    def expect(self, val):
        k, v = self.next()
        if v != val:
            raise Uncovered(f"expected {val!r}, got {v!r}")
        return v

    def at(self, val):
        return self.peek()[1] == val

    def done(self):
        return self.i >= len(self.t)

    # an expression: int, bool, identifier, identifier[int], [e, ...], {int, ...}, lo..hi
    def expr(self):
        k, v = self.next()
        if k == "int":
            if self.at(".."):
                self.next()
                k2, v2 = self.next()
                if k2 != "int":
                    raise Uncovered("non-integer range bound")
                return ("range", int(v), int(v2))
            return ("int", int(v))
        if k == "id":
            if v in ("true", "false"):
                return ("int", 1 if v == "true" else 0)
            if self.at("["):
                self.next()
                k2, idx = self.next()
                if k2 != "int":
                    raise Uncovered(f"array access {v}[{idx}] with a non-integer index")
                self.expect("]")
                return ("elem", v, int(idx))
            if self.at("("):
                # an annotation call or a float function: skip balanced
                self.skip_balanced()
                return ("annot", v)
            return ("id", v)
        if v == "[":
            items = []
            while not self.at("]"):
                items.append(self.expr())
                if self.at(","):
                    self.next()
            self.next()
            return ("array", items)
        if v == "{":
            items = []
            while not self.at("}"):
                k2, v2 = self.next()
                if k2 != "int":
                    raise Uncovered("a set literal of something other than integers")
                items.append(int(v2))
                if self.at(","):
                    self.next()
            self.next()
            return ("set", items)
        if k == "str":
            return ("str", v)
        raise Uncovered(f"unexpected token {v!r}")

    def skip_balanced(self):
        depth = 0
        while True:
            k, v = self.next()
            if v is None:
                raise Uncovered("unbalanced parentheses")
            if v in ("(", "[", "{"):
                depth += 1
            elif v in (")", "]", "}"):
                depth -= 1
                if depth == 0:
                    return

    def annotations(self):
        while self.at("::"):
            self.next()
            k, v = self.next()
            if k != "id":
                raise Uncovered(f"annotation expected, got {v!r}")
            if self.at("("):
                self.skip_balanced()


# ---------------------------------------------------------------- model

class Model:
    def __init__(self):
        self.vars = {}       # fzn name -> (lo, hi, holes-or-None as sorted value list)
        self.order = []      # fzn names in declaration order
        self.alias = {}      # fzn name -> a term ("var", name) or ("int", k)
        self.params = {}     # name -> int or list of ints
        self.arrays = {}     # name -> list of terms
        self.cons = []       # (builtin, args)
        self.extra = []      # (kind, ...) domain restrictions from aliases

    def term(self, e):
        """An expression standing for one integer: ("var", name) or ("int", k)."""
        if e[0] == "int":
            return e
        if e[0] == "id":
            n = e[1]
            if n in self.params and isinstance(self.params[n], int):
                return ("int", self.params[n])
            if n in self.alias:
                return self.alias[n]
            if n in self.vars:
                return ("var", n)
            raise Uncovered(f"unknown identifier {n!r} where an integer was expected")
        if e[0] == "elem":
            arr = self.array(("id", e[1]))
            if not 1 <= e[2] <= len(arr):
                raise Uncovered(f"index {e[2]} out of range of {e[1]}")
            return arr[e[2] - 1]
        raise Uncovered(f"an integer was expected, got {e[0]}")

    def array(self, e):
        if e[0] == "array":
            return [self.term(x) for x in e[1]]
        if e[0] == "id":
            n = e[1]
            if n in self.params and isinstance(self.params[n], list):
                return [("int", k) for k in self.params[n]]
            if n in self.arrays:
                return self.arrays[n]
            raise Uncovered(f"unknown array {n!r}")
        raise Uncovered(f"an array was expected, got {e[0]}")

    def ints(self, e):
        out = []
        for t in self.array(e):
            if t[0] != "int":
                raise Uncovered("a coefficient array holds a variable")
            out.append(t[1])
        return out


def domain_of(p):
    """`var` type after the keyword: returns (lo, hi, values-or-None)."""
    k, v = p.peek()
    if v == "int":
        raise Uncovered("`var int` with no declared domain (cake needs bounds; an invented "
                        "bound would change the model)")
    if v == "bool":
        p.next()
        return (0, 1, None)
    if v == "float" or v == "set":
        raise Uncovered(f"`var {v}`")
    e = p.expr()
    if e[0] == "range":
        if e[1] > e[2]:
            raise Uncovered(f"empty domain {e[1]}..{e[2]}")
        return (e[1], e[2], None)
    if e[0] == "set":
        vals = sorted(set(e[1]))
        if not vals:
            raise Uncovered("empty set domain")
        full = vals == list(range(vals[0], vals[-1] + 1))
        return (vals[0], vals[-1], None if full else vals)
    raise Uncovered(f"domain {e!r}")


def first_uncovered(toks):
    for (k1, v1), (k2, v2) in zip(toks, toks[1:]):
        if k1 == "id" and v1 == "constraint" and k2 == "id" and v2 not in COVERED:
            return v2
    return None


def parse(text):
    toks = scan(text)
    bad = first_uncovered(toks)
    if bad:
        raise Uncovered(bad)
    p = Parser(toks)
    m = Model()
    solved = False
    while not p.done():
        k, v = p.peek()
        if v == "predicate":
            # a declaration only; a call to it is refused by name below
            while p.next()[1] not in (";", None):
                pass
            continue
        if v == "constraint":
            p.next()
            k, name = p.next()
            if k != "id":
                raise Uncovered(f"constraint name expected, got {name!r}")
            if name not in COVERED:
                raise Uncovered(name)
            p.expect("(")
            args = []
            while not p.at(")"):
                args.append(p.expr())
                if p.at(","):
                    p.next()
            p.next()
            p.annotations()
            p.expect(";")
            m.cons.append((name, args))
            continue
        if v == "solve":
            p.next()
            p.annotations()
            k, goal = p.next()
            if goal != "satisfy":
                raise Uncovered(f"`solve {goal}`: an objective (M14-e2e-verification-T8)")
            p.expect(";")
            solved = True
            continue
        if v == "array":
            p.next()
            p.expect("[")
            r = p.expr()
            p.expect("]")
            if r[0] != "range" or r[1] != 1:
                raise Uncovered("an array index set that is not 1..n")
            n = r[2]
            p.expect("of")
            if p.at("var"):
                p.next()
                dom = domain_of(p)
                p.expect(":")
                k, name = p.next()
                p.annotations()
                if p.at("="):
                    p.next()
                    items = m.array(p.expr())
                    if len(items) != n:
                        raise Uncovered(f"array {name} has {len(items)} items for 1..{n}")
                    for j, t in enumerate(items):
                        restrict(m, t, dom, f"{name}[{j + 1}]")
                    m.arrays[name] = items
                else:
                    items = []
                    for j in range(1, n + 1):
                        en = f"{name}[{j}]"
                        declare(m, en, dom)
                        items.append(("var", en))
                    m.arrays[name] = items
                p.expect(";")
            else:
                k, ty = p.next()
                if ty not in ("int", "bool"):
                    raise Uncovered(f"array of {ty}")
                p.expect(":")
                k, name = p.next()
                p.annotations()
                p.expect("=")
                e = p.expr()
                if e[0] != "array" or any(x[0] != "int" for x in e[1]):
                    raise Uncovered(f"parameter array {name} that is not a literal of constants")
                m.params[name] = [x[1] for x in e[1]]
                p.expect(";")
            continue
        if v == "var":
            p.next()
            dom = domain_of(p)
            p.expect(":")
            k, name = p.next()
            p.annotations()
            if p.at("="):
                p.next()
                t = m.term(p.expr())
                restrict(m, t, dom, name)
                m.alias[name] = t
            else:
                declare(m, name, dom)
            p.expect(";")
            continue
        if v in ("int", "bool"):
            p.next()
            p.expect(":")
            k, name = p.next()
            p.annotations()
            p.expect("=")
            e = p.expr()
            if e[0] != "int":
                raise Uncovered(f"parameter {name} that is not an integer constant")
            m.params[name] = e[1]
            p.expect(";")
            continue
        raise Uncovered(f"unexpected item starting with {v!r}")
    if not solved:
        raise Uncovered("no solve item")
    return m


def declare(m, name, dom):
    m.vars[name] = dom
    m.order.append(name)


def restrict(m, t, dom, name):
    """An alias `var D: name = t` says t lies in D. Keep that, unless D adds nothing."""
    lo, hi, vals = dom
    allowed = set(vals) if vals else None
    if t[0] == "int":
        k = t[1]
        if not (lo <= k <= hi) or (allowed is not None and k not in allowed):
            raise Uncovered(f"constant {k} aliased by {name} lies outside its declared domain")
        return
    tlo, thi, tvals = m.vars[t[1]]
    tset = set(tvals) if tvals else set(range(tlo, thi + 1))
    dset = allowed if allowed is not None else set(range(lo, hi + 1))
    if tset <= dset:
        return
    m.extra.append((t[1], sorted(tset & dset), name))


# ---------------------------------------------------------------- .scp

def sanitise(name):
    return re.sub(r"[^A-Za-z0-9_]", "_", name)


def emit(m):
    names = {}
    for n in m.order:
        s = sanitise(n)
        if s in names:
            raise Uncovered(f"variables {names[s]!r} and {n!r} both sanitise to {s!r}")
        names[s] = n
    scp_of = {v: k for k, v in names.items()}

    def tm(t):
        return str(t[1]) if t[0] == "int" else scp_of[t[1]]

    cons = []
    for k, (name, args) in enumerate(m.cons, 1):
        cn = f"c{k}"
        if name not in COVERED:
            raise Uncovered(name)
        if name in ("int_lin_le", "int_lin_eq", "int_lin_ne"):
            if len(args) != 3:
                raise Uncovered(f"{name} with {len(args)} arguments")
            a, xs, c = m.ints(args[0]), m.array(args[1]), m.term(args[2])
            if len(a) != len(xs) or c[0] != "int":
                raise Uncovered(f"{name}: malformed arguments")
            kw = {"int_lin_le": "lin_less_equal", "int_lin_eq": "lin_equals",
                  "int_lin_ne": "lin_not_equals"}[name]
            terms = " ".join(f"{ai} {tm(xi)}" for ai, xi in zip(a, xs))
            cons.append(f"({cn} {kw} ({terms}) {c[1]})")
        elif name in ("int_le", "int_lt", "int_eq", "int_ne"):
            if len(args) != 2:
                raise Uncovered(f"{name} with {len(args)} arguments")
            x, y = m.term(args[0]), m.term(args[1])
            kw = {"int_le": "less_equal", "int_lt": "less_than", "int_eq": "equals",
                  "int_ne": "not_equals"}[name]
            cons.append(f"({cn} {kw} {tm(x)} {tm(y)})")
        elif name == "all_different_int":
            if len(args) != 1:
                raise Uncovered(f"{name} with {len(args)} arguments")
            xs = m.array(args[0])
            cons.append(f"({cn} all_different ({' '.join(tm(x) for x in xs)}))")
        elif name == "bool_clause":
            if len(args) != 2:
                raise Uncovered(f"{name} with {len(args)} arguments")
            ps, ns = m.array(args[0]), m.array(args[1])
            lits = [f"({tm(p)} = 1)" for p in ps] + [f"({tm(n)} = 0)" for n in ns]
            cons.append(f"({cn} or ({' '.join(lits)}) (1 = 1))")
        elif name in ("array_bool_or", "array_bool_and"):
            if len(args) != 2:
                raise Uncovered(f"{name} with {len(args)} arguments")
            xs, r = m.array(args[0]), m.term(args[1])
            kw = "or" if name == "array_bool_or" else "and"
            cons.append(f"({cn} {kw} ({' '.join(f'({tm(x)} = 1)' for x in xs)}) ({tm(r)} = 1))")
        elif name in ("bool_eq", "bool_not", "bool2int"):
            if len(args) != 2:
                raise Uncovered(f"{name} with {len(args)} arguments")
            a, b = m.term(args[0]), m.term(args[1])
            kw = "not_equals" if name == "bool_not" else "equals"
            cons.append(f"({cn} {kw} {tm(a)} {tm(b)})")
        elif name in ("int_le_reif", "int_eq_reif", "int_ne_reif"):
            if len(args) != 3:
                raise Uncovered(f"{name} with {len(args)} arguments")
            x, y, r = m.term(args[0]), m.term(args[1]), m.term(args[2])
            kw = {"int_le_reif": "less_equal_iff", "int_eq_reif": "equals_iff",
                  "int_ne_reif": "not_equals_iff"}[name]
            cons.append(f"({cn} {kw} ({tm(r)} = 1) {tm(x)} {tm(y)})")
        elif name == "int_lin_le_reif":
            if len(args) != 4:
                raise Uncovered(f"{name} with {len(args)} arguments")
            a, xs, c, r = m.ints(args[0]), m.array(args[1]), m.term(args[2]), m.term(args[3])
            if len(a) != len(xs) or c[0] != "int":
                raise Uncovered(f"{name}: malformed arguments")
            terms = " ".join(f"{ai} {tm(xi)}" for ai, xi in zip(a, xs))
            cons.append(f"({cn} lin_less_equal_iff ({tm(r)} = 1) ({terms}) {c[1]})")
    k = 0
    for n in m.order:
        lo, hi, vals = m.vars[n]
        if vals is not None:
            k += 1
            cons.append(f"(d{k} in ({' '.join(map(str, vals))}) {scp_of[n]})")
    for n, vals, by in m.extra:
        k += 1
        if not vals:
            raise Uncovered(f"alias {by} has an empty domain")
        cons.append(f"(d{k} in ({' '.join(map(str, vals))}) {scp_of[n]})")
    var_s = " ".join(f"({scp_of[n]} {m.vars[n][0]} {m.vars[n][1]})" for n in m.order)
    scp = (f"( (version 1) (variables {var_s}) (constraints {' '.join(cons)}) "
           f"(prob_type decide) )\n")
    return scp, names


def main(argv):
    if len(argv) != 4:
        print("usage: fzn2scp.py MODEL.fzn OUT.scp OUT.names", file=sys.stderr)
        return 64
    try:
        m = parse(open(argv[1]).read())
        scp, names = emit(m)
    except Uncovered as e:
        print(f"UNCOVERED: {e}", file=sys.stderr)
        return 2
    with open(argv[2], "w") as f:
        f.write(scp)
    with open(argv[3], "w") as f:
        for s, n in names.items():
            f.write(f"{s} {n}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
