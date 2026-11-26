#!/usr/bin/env python3
"""L-meta-17117 / L-meta-17118: Hamiltonian cycle on 5 vertices, on its 10 edge bits.

The posted function (L-meta-17118) is the OR of the twelve 5-cycles of K5.
The fleet's best circuit has 26 gates; the ladder asks for 25 (L-meta-17117) and
23 (L-meta-17118).

THE DECOMPOSITION.  Fix a vertex v of the cycle.  The five edges of the cycle
split into

    the wedge at v            two adjacent edges (v,u) and (v,w)
    the matching              two disjoint edges (u,c) and (d,w)
    the middle edge           the edge (c,d)

with {c,d} the two vertices that are neither v nor the neighbours of v.  So a
cycle is the product of three factors: a wedge, a matching and one edge.

A wedge lies in exactly two of the twelve cycles, and in those two cycles the
matching and the middle edge are determined.  So the twelve cycles split into
six groups of two, one group per wedge; each group shares its wedge and its
middle edge and differs in its matching.

Then the circuit is

    f = OR over classes g of ( (OR over wedges w in g of (wedge_w & middle_w))
                              & (OR over matchings m of g of m) )

where two groups are merged into one class exactly when they use the same two
matchings, so that one bracket serves both.  The cost is

    r (wedges) + r (wedge & middle) + D (distinct matchings)
        + sum over classes of (n_g + s_g - 1) + (number of classes - 1)

with r the number of wedges used, n_g the number of wedges in the class and
s_g the size of its matching set.

Choosing a DIFFERENT vertex for different cycles changes the wedges, and that
is where the gates are: this program searches all ways of pairing the twelve
cycles by wedges and reports the cheapest.
"""

import itertools
import sys

# ---------------------------------------------------------------------------
# the function

# edge index -> vertex pair, from the posted statement's numbering
EDGE = {
    0: (0, 1), 1: (0, 2), 2: (0, 3), 3: (0, 4),
    4: (1, 2), 5: (1, 3), 6: (1, 4),
    7: (2, 3), 8: (2, 4),
    9: (3, 4),
}
# the twelve 5-cycles, as the posted statement lists them
TERMS = [
    (0, 3, 4, 7, 9), (0, 2, 4, 8, 9), (0, 3, 5, 7, 8), (0, 1, 5, 8, 9),
    (0, 2, 6, 7, 8), (0, 1, 6, 7, 9), (1, 3, 4, 5, 9), (1, 2, 4, 6, 9),
    (1, 3, 5, 6, 7), (1, 2, 5, 6, 8), (2, 3, 4, 5, 8), (2, 3, 4, 6, 7),
]


def cycles_as_sequences():
    """Each 5-cycle as a cyclic sequence of edges, e1..e5, plus its vertices.

    In the returned pair, the vertex v_i sits between e_{i-1} and e_i.
    """
    out = []
    for t in TERMS:
        t = tuple(sorted(t))
        found = None
        for perm in itertools.permutations(t):
            a, b = EDGE[perm[0]]
            for start, nxt in ((a, b), (b, a)):
                verts = [start, nxt]
                cur = nxt
                ok = True
                for k in range(1, 5):
                    x, y = EDGE[perm[k]]
                    if k == 4:
                        if not ((x == cur and y == verts[0]) or
                                (y == cur and x == verts[0])):
                            ok = False
                            break
                    elif x == cur and y not in verts:
                        verts.append(y)
                        cur = y
                    elif y == cur and x not in verts:
                        verts.append(x)
                        cur = x
                    else:
                        ok = False
                        break
                if ok and len(set(verts)) == 5:
                    found = (perm, tuple(verts))
                    break
            if found:
                break
        if not found:
            raise AssertionError("not a cycle: %s" % (t,))
        out.append(found)
    return out


CYC = cycles_as_sequences()


def f(bits):
    """The posted function."""
    for t in TERMS:
        if all(bits[e] for e in t):
            return True
    return False


# ---------------------------------------------------------------------------
# the decomposition

def wedge_options(seq):
    """For a cycle (seq of 5 edges e1..e5, with v_i between e_{i-1} and e_i),
    the five decompositions, one per special vertex v_i.

    Each is (wedge, matching, middle): wedge and matching are frozensets of
    two edges, middle is an edge index.
    """
    out = []
    for i in range(5):
        wedge = frozenset((seq[(i - 1) % 5], seq[i]))
        matching = frozenset((seq[(i + 1) % 5], seq[(i + 3) % 5]))
        middle = seq[(i + 2) % 5]
        out.append((wedge, matching, middle))
    return out


# for every wedge: the cycles containing it, and their (matching, middle)
WEDGE_INFO = {}
for idx, (seq, verts) in enumerate(CYC):
    for wedge, matching, middle in wedge_options(seq):
        WEDGE_INFO.setdefault(wedge, []).append((idx, matching, middle))

for w, lst in WEDGE_INFO.items():
    assert len(lst) == 2, (w, lst)
    # the two cycles sharing a wedge share the middle edge
    assert lst[0][2] == lst[1][2], (w, lst)

# the wedges two cycles share
SHARED = {}
for wedge, lst in WEDGE_INFO.items():
    a, b = lst[0][0], lst[1][0]
    SHARED.setdefault((min(a, b), max(a, b)), []).append(wedge)


def cost_of_cover(cover):
    """cover: list of (wedge, [cycle indices assigned to it]).

    Returns (cost, detail), or None when the cover is not a partition.
    """
    seen = []
    for wedge, cs in cover:
        for c in cs:
            if c in seen:
                return None
            seen.append(c)
    if sorted(seen) != list(range(12)):
        return None

    msets = []
    for wedge, cs in cover:
        ms = set()
        for c in cs:
            for idx2, matching, middle in WEDGE_INFO[wedge]:
                if idx2 == c:
                    ms.add(matching)
        msets.append(frozenset(ms))

    classes = {}
    for (wedge, cs), ms in zip(cover, msets):
        classes.setdefault(ms, []).append((wedge, cs))

    nmatch = len(set().union(*msets)) if msets else 0
    combining = len(classes) - 1
    for ms, items in classes.items():
        combining += len(items) + len(ms) - 1

    total = 2 * len(cover) + nmatch + combining
    return total, dict(nwedges=len(cover), nmatch=nmatch, nclasses=len(classes),
                       combining=combining,
                       classes={tuple(sorted(ms)): len(v) for ms, v in classes.items()})


def all_partitions():
    """Every partition of the twelve cycles into six pairs, each pair the two
    cycles of some wedge."""
    out = []

    def rec(remaining, pairs):
        if not remaining:
            out.append(list(pairs))
            return
        c = remaining[0]
        for (a, b) in SHARED:
            if c not in (a, b):
                continue
            if a not in remaining or b not in remaining:
                continue
            nxt = [x for x in remaining if x != a and x != b]
            rec(nxt, pairs + [(a, b)])

    rec(list(range(12)), [])
    return out


def search():
    """The cheapest cover, over every partition and every wedge choice."""
    best = None
    counts = {}
    for pairs in all_partitions():
        choices = [SHARED[(min(a, b), max(a, b))] for (a, b) in pairs]
        for combo in itertools.product(*choices):
            cover = [(w, [a, b]) for w, (a, b) in zip(combo, pairs)]
            res = cost_of_cover(cover)
            if res is None:
                continue
            counts[res[0]] = counts.get(res[0], 0) + 1
            if best is None or res[0] < best[0]:
                best = (res[0], cover, res[1])
    return best, counts


def build_circuit(cover):
    """Turn a cover into an explicit gate list.

    Returns (gates, output_wire); gates is a list of (op, (i, j)).
    """
    gates = []

    def add(op, *ins):
        gates.append((op, tuple(ins)))
        return 10 + len(gates) - 1

    def AND(a, b):
        return add("and", a, b)

    def OR(a, b):
        return add("or", a, b)

    match_wire = {}
    wedge_wire = {}
    wm_wire = {}

    def get_match(m):
        if m not in match_wire:
            a, b = sorted(m)
            match_wire[m] = AND(a, b)
        return match_wire[m]

    def get_wedge(w):
        if w not in wedge_wire:
            a, b = sorted(w)
            wedge_wire[w] = AND(a, b)
        return wedge_wire[w]

    def get_wm(w):
        """the wedge AND the middle edge"""
        if w not in wm_wire:
            middle = WEDGE_INFO[w][0][2]
            wm_wire[w] = AND(get_wedge(w), middle)
        return wm_wire[w]

    classes = {}
    for wedge, cs in cover:
        ms = frozenset(
            matching
            for c in cs
            for idx2, matching, middle in WEDGE_INFO[wedge] if idx2 == c)
        classes.setdefault(ms, []).append((wedge, cs))

    outs = []
    for ms, items in classes.items():
        ws = [get_match(m) for m in sorted(ms)]
        cur = ws[0]
        for w in ws[1:]:
            cur = OR(cur, w)
        cur2 = get_wm(items[0][0])
        for wedge, cs in items[1:]:
            cur2 = OR(cur2, get_wm(wedge))
        outs.append(AND(cur2, cur))

    out = outs[0]
    for o in outs[1:]:
        out = OR(out, o)
    return gates, out


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


def check(gates, output):
    for x in itertools.product([False, True], repeat=10):
        bits = [bool(b) for b in x]
        if evaluate(gates, output, bits) != f(bits):
            return False
    return True


def main():
    print("cycles:", len(CYC), " wedges:", len(WEDGE_INFO))
    parts = all_partitions()
    print("partitions into pairs of cycles sharing a wedge:", len(parts))
    best, counts = search()
    print("cost histogram:", dict(sorted(counts.items())))
    print("BEST:", best[0], best[2])
    for wedge, cs in best[1]:
        print("   wedge", sorted(wedge), "-> cycles", cs,
              "matchings", sorted(tuple(sorted(m)) for i, m, _ in WEDGE_INFO[wedge]))
    gates, out = build_circuit(best[1])
    ok = check(gates, out)
    print("gates:", len(gates), " correct on all 1024 inputs:", ok)
    assert ok
    print("GATE LIST:", gates)
    print("OUTPUT WIRE:", out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
