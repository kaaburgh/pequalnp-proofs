#!/usr/bin/env python3
"""L-meta-18249: a perfect matching in 4 by 4 bipartite graphs, on 16 edge bits.

The posted function is the OR of the twenty-four perfect matchings of K4,4
(rows 0..3, columns 0..3; the edge bits are numbered row major, so the bit
4*i+j is the edge from row i to column j).

THE CONSTRUCTION.  Split the rows in two and the columns in two.  A perfect
matching uses, say, the columns S for the rows 0,1 and the columns Sc for the
rows 2,3; there are three ways to split four columns in two.

    A(S) = the rows 0,1 are matched to S   = (x0s & x1t) | (x0t & x1s)
    B(T) = the rows 2,3 are matched to T   = (x2u & x3v) | (x2v & x3u)

for S = {s,t} and T = {u,v}.  Then

    f = OR over the three column splits S | Tc of ( A(S) & B(Tc) ).

Each of the six two-row functions costs three gates, the three products cost
one gate each and the final OR two, so twenty-three gates in all: the fleet
holds forty-five.
"""

import itertools
import re
import sys

N = 16
ROWS = 4
COLS = 4


def bit(i, j):
    """the bit of the edge from row i to column j"""
    return 4 * i + j


def statement_terms(path):
    """the terms of the posted statement"""
    t = open(path).read()
    m = re.search(r"HasCircuitSize 16 \(fun x : Fin 16 → Bool => (.*?)\) 36", t, re.S)
    body = m.group(1)
    terms = []
    for tm in re.finditer(r"\(x (\d+) && x (\d+) && x (\d+) && x (\d+)\)", body):
        terms.append(tuple(int(x) for x in tm.groups()))
    return terms


def f(bits):
    for t in TERMS:
        if all(bits[e] for e in t):
            return True
    return False


def is_perfect_matching(t):
    """the four bits of the term must be one edge per row and per column"""
    rows = [e // 4 for e in t]
    cols = [e % 4 for e in t]
    return sorted(rows) == [0, 1, 2, 3] and sorted(cols) == [0, 1, 2, 3]


class Builder:
    def __init__(self):
        self.gates = []

    def add(self, op, *ins):
        self.gates.append((op, tuple(ins)))
        return N + len(self.gates) - 1

    def AND(self, a, b):
        return self.add("and", a, b)

    def OR(self, a, b):
        return self.add("or", a, b)


def two_rows(b, r0, r1, c0, c1):
    """the rows r0,r1 are matched to the columns c0,c1"""
    p = b.AND(bit(r0, c0), bit(r1, c1))
    q = b.AND(bit(r0, c1), bit(r1, c0))
    return b.OR(p, q)


def build():
    b = Builder()
    # the three splits of the columns into two pairs
    splits = []
    for c0 in range(COLS):
        for c1 in range(c0 + 1, COLS):
            rest = [c for c in range(COLS) if c not in (c0, c1)]
            if c0 == 0 and rest == sorted(rest):
                splits.append(((c0, c1), tuple(rest)))
    splits = splits[:3]
    assert len(splits) == 3, splits

    outs = []
    for (c0, c1), (c2, c3) in splits:
        a = two_rows(b, 0, 1, c0, c1)
        t = two_rows(b, 2, 3, c2, c3)
        outs.append(b.AND(a, t))
    out = outs[0]
    for o in outs[1:]:
        out = b.OR(out, o)
    return b.gates, out


def evaluate(gates, output, bits):
    wires = list(bits)
    for op, ins in gates:
        if op == "and":
            val = all(wires[i] if i < len(wires) else False for i in ins)
        elif op == "or":
            val = any(wires[i] if i < len(wires) else False for i in ins)
        else:
            i = ins[0]
            val = not (wires[i] if i < len(wires) else False)
        wires.append(val)
    return wires[output]


def main():
    global TERMS
    TERMS = statement_terms(
        "/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_18249.lean")
    print("terms in the statement:", len(TERMS))
    assert len(TERMS) == 24
    assert all(is_perfect_matching(t) for t in TERMS), "not a perfect matching"
    print("every term is a perfect matching of K4,4")
    allpm = set()
    for p in itertools.permutations(range(COLS)):
        allpm.add(tuple(sorted(bit(i, p[i]) for i in range(ROWS))))
    print("the statement has all the perfect matchings:",
          set(TERMS) == allpm)

    gates, out = build()
    print("gates:", len(gates))
    bad = 0
    for x in itertools.product([False, True], repeat=N):
        bits = [bool(b) for b in x]
        if evaluate(gates, out, bits) != f(bits):
            bad += 1
            if bad < 3:
                print("  wrong on", x)
    print("wrong on", bad, "of", 2 ** N, "inputs")
    assert bad == 0
    print("GATES:", gates)
    print("OUTPUT:", out)
    import json
    json.dump({"gates": gates, "output": out, "terms": TERMS},
              open("/workspace/output/pm44.json", "w"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
