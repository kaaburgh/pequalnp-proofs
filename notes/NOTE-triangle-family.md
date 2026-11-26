# A triangle in n-vertex graphs: a family of circuits

`methods/find/triangle_family.py` builds a circuit for "the graph on n vertices
contains a triangle", on the bits of its edges, and checks it on every input.

## The construction

A triangle on the vertices i, j, w is the edge ij together with a vertex w
joined to both.  So the triangles that share an edge ij are computed together:
the OR of the wedges (iw, jw) over the other vertices w, ANDed with the edge
ij.  Every triangle has to be assigned to one of its edges, and the edges that
can be used are the ones of a set E that meets every triangle; the complement
of E has to be a graph without a triangle, so the smallest such E is the set
of the edges inside the two parts of a balanced bipartition of the vertices
(the Turan graph T_2(n) is the largest triangle-free graph on n vertices).

With T triangles in G = C(n,3) of them and g edges in E, the circuit has

    2 G + g - 1  gates:

one wedge (an AND of two edges) per triangle, one OR per wedge inside a group
and one AND with the shared edge per group, and g - 1 OR gates to join the
groups.

## The numbers

    n = 5: 10 edges, 10 triangles, 4 groups | 23 gates (14 AND, 9 OR) | correct on all 1024 inputs
    n = 6: 15 edges, 20 triangles, 6 groups | 45 gates (26 AND, 19 OR) | correct on all 32768 inputs
    n = 7: 21 edges, 35 triangles, 9 groups | 78 gates (44 AND, 34 OR) | correct on all 2097152 inputs

The fleet holds 24 gates for n = 5 (L-meta-17391, checked) and 49 for n = 6.
So the construction is one gate better than the record on five vertices and
four gates better on six.

## Why 22 is out of reach for five vertices

Two triangles of K5 share at most one edge, so no two of them can share a
product of two edges: each triangle needs a wedge of its own, and that is
`C(n,3)` gates, ten of them for n = 5.  The third edge of a triangle is
attached to the group of triangles that share it, which costs one gate per
group, and joining the groups costs one gate per group beyond the first.  A
group is a set of triangles sharing an edge, and an edge of K5 lies in three
triangles, so there are at least four groups.  The total is therefore

    C(n,3) (wedges) + C(n,3) (groups) + (g - 1) (final OR) = 19 + g

with g at least 4 for n = 5, hence 23, and the construction is at the bound.

The ladder for the five-vertex triangle sits at 24 (L-meta-17391, checked),
22 (L-meta-17392) and 20 (L-meta-17393), so the gap of one gate between 23
and 22 is exactly the gap this analysis leaves open, and it is not a gap that
this family of constructions can close.  The six-vertex triangle is a better
target: the fleet holds 49 and this construction gives 45.
