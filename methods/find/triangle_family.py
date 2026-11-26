#!/usr/bin/env python3
"""A circuit for "the graph on n vertices contains a triangle", and a check of it.

The construction.  A triangle on the vertices i, j, w is the edge ij together with a
vertex w joined to both.  So the triangles that share an edge ij are computed together:
the OR of the wedges (iw, jw) over the other vertices w, ANDed with the edge ij.  Every
triangle has to be assigned to one of its edges, and the edges that can be used are the
ones of a set E that meets every triangle; the complement of E has to be a graph without
a triangle, so the smallest such E is the set of the edges inside the two parts of a
balanced bipartition of the vertices (the Turan graph T_2(n) is the largest triangle-free
graph on n vertices).

The size.  With T triangles in G = C(n,3) of them and g edges in E, the circuit has
  2 G + g - 1  gates:
  one wedge (an AND of two edges) per triangle, one OR per wedge inside a group and one
  AND with the shared edge per group, and g - 1 OR gates to join the groups.

    python3 triangle_family.py --n 5
    python3 triangle_family.py --n 6
"""

import argparse
import itertools
import sys


def build(n):
    """The gate list and the output wire of the construction, on the edge bits."""
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    eidx = {e: k for k, e in enumerate(edges)}
    triangles = list(itertools.combinations(range(n), 3))

    # the hitting set: the edges inside the two parts of a balanced bipartition
    half = (n + 1) // 2
    parts = [list(range(half)), list(range(half, n))]
    E = [(i, j) for part in parts for i, j in itertools.combinations(part, 2)]

    def group_of(t):
        """The edge of E that the triangle is assigned to."""
        for e in E:
            if e[0] in t and e[1] in t:
                return e
        raise AssertionError("the set E meets every triangle")

    groups = {}
    for t in triangles:
        groups.setdefault(group_of(t), []).append(t)

    gates = []
    outs = []
    for e, ts in groups.items():
        wires = []
        for t in ts:
            # the wedge: the two edges of the triangle that are not the shared edge
            other = [x for x in ((t[0], t[1]), (t[0], t[2]), (t[1], t[2]))
                     if x != e]
            assert len(other) == 2
            gates.append(("and", [eidx[other[0]], eidx[other[1]]]))
            wires.append(len(edges) + len(gates) - 1)
        cur = wires[0]
        for w in wires[1:]:
            gates.append(("or", [cur, w]))
            cur = len(edges) + len(gates) - 1
        gates.append(("and", [eidx[e], cur]))
        outs.append(len(edges) + len(gates) - 1)
    cur = outs[0]
    for o in outs[1:]:
        gates.append(("or", [cur, o]))
        cur = len(edges) + len(gates) - 1
    return gates, cur, len(edges), len(triangles), len(E), edges


def check(n):
    gates, out, nedges, ntri, ngroups, edges = build(n)

    def has_triangle(bits):
        for t in itertools.combinations(range(n), 3):
            need = 0
            for a, b in ((t[0], t[1]), (t[0], t[2]), (t[1], t[2])):
                need |= 1 << edges.index((min(a, b), max(a, b)))
            if (bits & need) == need:
                return True
        return False

    def value(bits):
        w = [bool((bits >> i) & 1) for i in range(nedges)]
        for op, pins in gates:
            vals = [w[p] if 0 <= p < len(w) else False for p in pins]
            w.append(all(vals) if op == "and" else any(vals))
        return w[out] if 0 <= out < len(w) else False

    bad = 0
    for bits in range(1 << nedges):
        if value(bits) != has_triangle(bits):
            bad += 1
            if bad < 4:
                print("   WRONG on the edge set %d" % bits)
    nand = sum(1 for g in gates if g[0] == "and")
    print("n = %d: %d edges, %d triangles, %d groups | %d gates (%d AND, %d OR) | "
          "wrong on %d of %d inputs"
          % (n, nedges, ntri, ngroups, len(gates), nand, len(gates) - nand, bad, 1 << nedges))
    return bad == 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--n", type=int, default=5)
    args = ap.parse_args()
    sys.exit(0 if check(args.n) else 1)
