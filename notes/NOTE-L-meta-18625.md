# L-meta-18625: the seven-cycle has no AND/OR circuit of nine gates

The step asks for a circuit of AND and OR gates of fan-in at most two, with at
most 9 gates, that is right on every input with one or two 1s: false on the seven
inputs with a single 1, and on the twenty-one inputs with two 1s true exactly
when the two vertices are joined on the seven-cycle.

**No such circuit exists.**  The desk holds 10 gates, and 10 is the least there
is, so the rung 9 is empty and nobody should spend time on it again.

## The machine search

`methods/find/search_7cycle_9.py` asks the SAT solver (`kissat`) whether a
circuit of AND and OR gates of fan-in at most two with exactly `K` gates computes
the function on the 28 promised inputs, for `K = 9, 8, ..., 1`.  The output gate
may be taken to be the last gate, so the sizes cover every circuit of at most 9
gates.  The encoding is the one of `methods/find/sat_search.py`: one-hot
selectors for the two operand wires of every gate, one-hot type variables, and
the value of every wire on every promised row.

Every size up to 7 comes back UNSAT, which is the machine part of the bound; the
sizes 8 and 9 are proved by the argument below, which covers every size at once.

    sha256 of the program: 4d250acc5992c5805c1b9702a9e31779b344556661e1a134f911dc26d50336cb

## Why 10 is the least, by hand

Write `E` for the seven edges of the cycle, `O` for the output wire of the
circuit and `Min(w)` for the minimal true sets of a wire `w`.

1. `O` is false on every input with a single 1, so every set in `Min(O)` has
   size at least two.  `O` is true on every edge and false on every non-edge, so
   each edge `{a, b}` is in `Min(O)`.
2. `O` is an OR of branches, and the minimal sets of an OR are those of its
   branches.  So each edge is in `Min(g)` for some AND gate `g = R AND S` that is
   OR-connected to `O`; being OR-connected, `g` is true only where `O` is true.
   Since `Min(g) = {M_R + M_S}`, the edge `{a, b}` means `M_R = {a}` and
   `M_S = {b}`: `R` is true at `{a}` and `S` is true at `{b}`.
3. Put `S(w) = {v : w is true at the input {v}}`.  A wire with a singleton in
   `Min(w)` is an OR-tree, and it is true at every pair that contains one of its
   singletons.  So `g` is true at every pair `{x, y}` with `x` in `S(R)` and `y`
   in `S(S)`, and `g` is true only where `O` is, so all these pairs are edges of
   the cycle.
4. If both `S(R)` and `S(S)` had two vertices, the four pairs would be a
   four-cycle, and the seven-cycle has none.  So one of them is a single vertex,
   and `g` is true on at most the two edges at that vertex: **one AND gate
   covers at most two edges of the cycle.**
5. The seven edges therefore need at least four AND gates, three of them
   covering two edges.  A gate that covers two edges has an operand with two
   singletons, and such an operand is an OR-tree with at least one gate.  Two
   different stars cannot share that OR gate: in a seven-cycle two vertices have
   at most one common neighbour, so the shared wire would force the two gates to
   cover the same two edges.  So the three two-edge gates need three different
   OR gates.
6. The output is an OR of at least four AND branches, so it needs at least three
   OR gates of its own; a branch cannot be a wire, because a wire is true at a
   single 1.

That is 4 AND + 3 OR (inner) + 3 OR (output) = 10 gates, and the desk's circuit
has exactly 10: `x_a AND (x_(a-1) OR x_(a+1))` for `a = 1, 3, 5`, then
`x_6 AND x_0`, all ORed.

The same argument at five vertices gives 7, which is what the desk already
computed there.
