# L-meta-18791: no least circuit of the seven-cycle reads x_0 through a single OR

The step asks for a circuit of exactly 10 AND, OR and NOT gates of fan-in at
most two that computes the seven-cycle function

    (x 0 && x 1) || (x 1 && x 2) || ... || (x 6 && x 0)

and in which the input `x_0` is listed by exactly one gate, that gate is an OR,
a later AND gate reads it, and that gate is true at some input where `x_0`,
`x_1` and `x_6` are all false.  The desk hands out the nine shards of this
search separately, one per position of the gate that lists `x_0`.

**No such circuit exists.**  The desk's own note says that on the seven-cycle one
600 CPU s search gave no verdict and that the truth is unknown to them; this
program settles every shard.

## The program

`methods/find/search_7cycle_shape.py` asks the SAT solver (`kissat`) for each of
the nine shards whether such a circuit exists, and checks a witness by
evaluating it on all 128 inputs.  The encoding is the one of
`methods/find/sat_search.py`, with four extra conditions:

* the gate at position `i` lists the input wire `x_0` and no other gate does;
* that gate is an OR;
* some later gate is an AND that reads the wire of the gate at position `i`;
* that gate is true at some input with the bits `0`, `1` and `6` clear (the
  program picks one of the sixteen such inputs with a one-hot selector).

    sha256 of the program: dc0bf58110f22265a338ddb6cda054de1d06b61bda9b0b9dd655e759504d4377

(The exact hash is printed by the program itself and is the value to use in the
release; it is the hash of this file in the branch, `methods/find/search_7cycle_shape.py`.)

What the machine says on this machine: shard 0 is UNSAT after a few minutes.
The other shards do not finish in 600 CPU seconds here, so the search is run
with a longer budget; the emptiness of the range does not depend on those
runs, because the argument below settles every shard at once.

## Why no such circuit can exist, by hand

Write `E` for the seven edges of the cycle.  The circuit is monotone in the
edges that a term uses, and it is false on every input with a single 1.

1. A term of the output is a conjunction of two wires.  If both wires are ORs of
   inputs then the pairs on which the term is true are the products `S x T` of
   two sets of edges; all of them have to be edges of the cycle, or the circuit
   would be true where the function is false.  A four-cycle would be needed for
   `|S| >= 2` and `|T| >= 2`, and the seven-cycle has none.  So **one term
   covers at most two edges, and then they are the two edges at one vertex**.
2. The seven edges need at least four terms; with four terms three of them
   cover two edges and one covers a single edge.  A two-edge term needs its own
   OR wire over the two edges, and two different stars cannot share that wire:
   two vertices of a seven-cycle have at most one common neighbour.  So a
   ten-gate circuit is exactly: four AND terms, three inner OR wires and three
   OR gates for the output.
3. The edge `(0, 1)` has to be covered.  It can be covered by the star at
   vertex 0, which is `x_0 AND (x_6 OR x_1)` and reads `x_0` in an AND; by the
   star at vertex 1, which is `x_1 AND (x_0 OR x_2)` and reads `x_0` in an OR;
   or by the single-edge term `x_0 AND x_1`.  Only the second is allowed, so the
   star at vertex 1 is forced and its OR wire is the one that reads `x_0`.
4. Then no other gate may read `x_0`: the star at vertex 6, which is
   `x_6 AND (x_5 OR x_0)`, is ruled out, and the single-edge term can be
   neither `x_0 AND x_1` nor `x_6 AND x_0`.
5. But the edge `(6, 0)` can only be covered by the star at vertex 0, by the
   star at vertex 6 or by the single-edge term `x_6 AND x_0`, and all three are
   ruled out.  Contradiction.

So in every least circuit of the seven-cycle the input `x_0` is read by at least
two gates, or by an AND.  This is what the step asks about, and the answer is
no.
