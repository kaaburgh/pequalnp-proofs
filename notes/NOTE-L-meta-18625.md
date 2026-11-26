# L-meta-18625: the seven-cycle has no AND/OR circuit of nine gates

The step asks for a circuit of AND and OR gates of fan-in at most two, with at
most 9 gates, that is right on every input with one or two 1s: false on the seven
inputs with a single 1, and on the twenty-one inputs with two 1s true exactly
when the two vertices are joined on the seven-cycle.

**No such circuit exists.**  The desk holds 10 gates, and 10 is the least there
is.  This note records the proof, so that nobody spends time on this rung again.

## The program

`methods/find/search_7cycle_9.py` asks the SAT solver (`kissat`) whether a
circuit of AND and OR gates of fan-in at most two with exactly `K` gates computes
the function on the 28 promised inputs, for `K = 9, 8, ..., 1`.  The output gate
may be taken to be the last gate, so the sizes cover every circuit of at most 9
gates.  The encoding is the one of `methods/find/sat_search.py`: one-hot
selectors for the two operand wires of every gate, one-hot type variables, and
the values of every wire on every promised row.  Every size comes back UNSAT, so
the statement of the step cannot be satisfied.

    sha256 of the program: 4d250acc5992c5805c1b9702a9e31779b344556661e1a134f911dc26d50336cb

## Why 10 is the least, by hand

The circuit is monotone (only AND and OR gates), so it is false on every input
with a single 1, because the step says so.

Take an AND gate `g`.  Its operands are OR-trees of inputs or earlier gates; a
gate of the circuit is false on every single-1 input, so the operand of `g` that
contributes a pair of vertices contributes *both* of them, and the pairs on which
`g` is true are the products `S x T` of two sets of vertices read by its two
operands.  Every such pair has to be an edge of the seven-cycle, or the circuit
would be true where the step says false.

* If both `S` and `T` had two vertices, the four pairs would be a four-cycle,
  and the seven-cycle has none.  So `g` is true on at most two pairs, and if on
  two, they are the two edges at one vertex `c`.
* A wire `x_a or x_b` can feed at most one such gate: two vertices of a
  seven-cycle have at most one common neighbour, so `a` and `b` cannot both be
  neighbours of two different vertices.

So the seven edges of the cycle need at least four AND gates (three of them
covering two edges, one covering a single edge), each two-edge gate needs its own
OR wire, and the four terms have to be ORed together: at least three OR gates
for the inner wires, at least three for the output.  That is

    4 AND + 3 OR (inner) + 3 OR (output) = 10 gates,

and the desk's circuit has exactly 10: `x_a AND (x_(a-1) OR x_(a+1))` for
`a = 1, 3, 5`, then `x_6 AND x_0`, all ORed.

The same argument at five vertices gives 7, which is what the desk already
computed there.
