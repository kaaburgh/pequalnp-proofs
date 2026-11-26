# L-meta-17117 and L-meta-17118: the Hamiltonian cycle on 5 vertices

The posted function (L-meta-17118) is the OR of the twelve 5-cycles of K5, on
the ten edge bits.  The ladder asks for 25 gates (L-meta-17117), 23 gates
(L-meta-17118) and 21 gates (L-meta-17123).  The fleet holds 26.

## A 26-gate circuit

`methods/find/h5cycle.py` builds one and checks it on every one of the 1024
inputs.  It reproduces the record, and the program also settles the question
of where the gates go.

## Why 25 looks out of reach

Fix a vertex `v` of a cycle.  The five edges of the cycle split into

* the **wedge** at `v`: the two edges of the cycle at `v`;
* the **matching**: the two edges of the cycle that are disjoint;
* the **middle edge**: the one edge left over.

So a cycle is the product of a wedge, a matching and one edge.

A wedge lies in exactly two of the twelve cycles, and in those two cycles the
matching and the middle edge are determined.  The twelve cycles therefore split
into six groups of two, one group per wedge, each group sharing its wedge and
its middle edge and differing in its matching.  The circuit is then

    f = OR over classes g of ( (OR over wedges w in g of (wedge_w & middle_w))
                              & (OR over matchings m of g of m) )

with two groups merged into one class exactly when they use the same two
matchings, so that one bracket serves both.  The cost is

    6 (wedges) + 6 (wedge & middle) + D (distinct matchings)
        + sum over classes of (n_g + s_g - 1) + (number of classes - 1)

where `n_g` is the number of wedges in the class and `s_g` the size of its
matching set.

The program enumerates **every** way of pairing the twelve cycles by wedges
(265 pairings) and, for each, every choice of wedge, and reports the cost of
each.  The minimum is **26**, reached five times; the histogram of the costs is
26, 29, 34, 35, 37, 38, 39.  So within this family no 25-gate circuit exists.

Two further facts bound the family from below, and they are why 26 is the
number rather than a coincidence:

* a matching (two disjoint edges) lies in exactly four of the twelve cycles,
  so a class can hold at most four wedges and there are at least three
  classes;
* the six wedges are shared by two cycles each, so the 24 cycles need at
  least six wedges, and the cost is `19 + D + 2m` with `D` the number of
  distinct matchings and `m` the number of classes.

## What is left

The rungs 25, 23 and 21 of this ladder look closed for monotone circuits built
this way, and 26 is the fleet's record, so the search here has not produced a
new circuit.  What it has produced is the search itself: a program that
enumerates the whole family and certifies the minimum.  A proof that **no**
25-gate circuit of any shape computes the function would need a different tool
(a complete enumeration of circuits, not a family of constructions), and that
is what the shards of the step are for.
