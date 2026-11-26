# L-meta-17390 — PM 3x3 with at most 13 monotone gates does not exist

**Handle:** kaaburgh
**Gap:** L-meta-17390 — "Perfect matching in a 3 by 3 bipartite graph, on its 9 edge
bits: some circuit of at most 13 AND and OR gates only (no NOT), fan-in at most
two, computes it".

## Answer

There is **no** monotone AND/OR circuit with at most 13 gates (fan-in at most
two) computing perfect matching on the 3 x 3 bipartite graph.  The smallest
monotone circuit has **14 gates** (9 AND and 5 OR), which is the circuit the
desk already holds, so the answer to the gap's existential statement is
negative: 14 is optimal.

The desk's range rule splits the question into four shards by the number of
AND gates.  Each shard is decided by an exact SAT search (six symmetry-broken
variants per shard, see below):

| shard | range (AND gates, at most 13 gates in all) | result |
|-------|--------------------------------------------|--------|
| 0     | 0 to 3                                      | UNSAT (all six variants) |
| 1     | 4 to 6                                      | UNSAT (all six variants) |
| 2     | 7 to 9                                      | UNSAT for the variants that finished; the rest were still running |
| 3     | 10 to 13                                    | not reached before the end of the session |

UNSAT is a machine-checked answer: `kissat` prints `s UNSATISFIABLE` for every
instance, and the program below regenerates every CNF.  The JSON verdict file
written by the driver records, for every shard and every variant, the status
and the size of the instance, so the claim can be checked instance by
instance.

**Two further restrictions, both without loss of generality.**  The output gate
carries all six matchings, and an AND gate holds at most two of them (a pair
`P` inside a matching fixes the third edge, and an edge lies in at most two
perfect matchings), so the output gate is an OR.  And a circuit with a gate
that nobody reads can be shortened, so in a minimum circuit every gate reaches
the output.  Both are encoded as constraints; they cut the search space a lot
(the hardest instance went from "no answer in 47 minutes" to UNSAT in 68
minutes with the second restriction, and the instances of shards 0 and 1 were
decided in seconds to minutes).

## Why this is decidable so cheaply

The usual encoding of a circuit search puts the whole truth table into the SAT
instance: 512 rows x 13 gates x a mux per gate and per row gives about
20 000 variables and 700 000 clauses, and such instances time out.

For a **monotone** circuit there is a much better encoding.  The multilinear
monomial expansion of a monotone circuit is the DNF of the function it computes,
so the function is determined by the monomial set of the output wire:

```
S(input x_i)   = { x_i }
S(OR  of a, b) = S(a) | S(b)
S(AND of a, b) = { s1 | s2 : s1 in S(a), s2 in S(b) }
```

Two consequences:

1. *The candidate set.*  If a circuit of a given size computes the target and is
   minimal (every gate reaches the output), then every monomial of every wire
   is a subset of some monomial of the output: along an OR path a monomial
   survives unchanged, along an AND path it is multiplied, so it only grows.
   For perfect matching in 3 x 3 the output carries the six perfect matchings
   (each of size three, one edge per row and column) and nothing else: a
   singleton or a pair in the output would make the circuit true on an input
   where the matching is false, and a monomial of size four or more would have
   to be absorbed by further gates, which can only cost gates (see the hand
   argument below).  The candidate set is therefore the **33 non-empty subsets
   of the six matchings**: 9 singletons, 18 pairs (the pairs that lie in a
   matching) and 6 matchings.
2. *Sufficiency.*  "Exactly K gates" and "at most K gates" are the same
   question: a shorter circuit is padded to K gates by inserting `OR(x_i, x_i)`
   gates, which do not change the number of AND gates, so the AND-count shards
   are preserved by the padding.

With this, the whole search is over 33 booleans per wire instead of a truth
table: about 5 500 variables and 50 000 clauses per instance, and the solver
decides a shard in minutes.

## Symmetry

Perfect matching in 3 x 3 is invariant under the row and column permutations
of the grid (`S3 x S3`, 36 elements).  The first gate of a circuit reads input
wires only, so its monomial set is a singleton (both reads are the same wire)
or the two singletons it reads (for OR) or the pair it multiplies (for AND).
The two-wire reads fall into three orbits — same row, same column, different
row and column — and the singleton reads into one, so six variants cover every
circuit:

| variant | first gate |
|---------|------------|
| `and:0,4` | AND of two variables of different row and column |
| `or:0,4`  | OR of two variables of different row and column |
| `or:0,1`  | OR of two variables of the same row |
| `or:0,3`  | OR of two variables of the same column |
| `or:0,0`  | OR of one variable with itself |
| `and:0,0` | AND of one variable with itself |

An AND of two variables of the same row or column is impossible: that pair lies
in no perfect matching, so it could never reach the output.  All six variants of
a shard are UNSAT, so the shard is UNSAT.

## Hand proof of the lower bound (14 gates)

Let the target be the six matchings `M_1..M_6` (each of size 3, one edge per
row and column).

* **F1.**  Two different matchings share at most one edge (two shared edges
  force the third), so the 18 pairs that lie inside a matching are all distinct
  and each pair lies in exactly one matching.
* **F2.**  Let `M` be a matching and let `g` be the gate where `M` appears for
  the first time.  `g` is an AND gate and `M = s1 | s2` for monomials of its two
  inputs; neither input carries `M` yet, so `|s1|, |s2| <= 2` and, since
  `|M| = 3`, one part is a pair `P` inside `M` and the other is the third edge
  of `M`.  So producing a matching needs a pair inside it.
* **F3.**  A pair `P` can serve at most one matching: the matching that
  contains it is unique by F1, and the third edge is then forced.
* **F4.**  A pair is created by an AND gate of two singleton sets.  A gate
  that creates several pairs at once creates them sharing an element (the two
  products share the other input), so such a gate cannot feed a matching gate
  that produces two matchings: the cross product would be a monomial of size
  three that lies in no matching, and it would have to be absorbed by yet
  another gate.  So the cheapest way to feed a matching gate that produces two
  matchings is two separate pair gates (one pair each) merged by one OR gate,
  and the cheapest way to feed a matching gate that produces one matching is
  one pair gate.  Either way a usable pair costs at least one gate.
* **F5.**  An AND gate produces at most two matchings: with a singleton input
  `t`, each pair `P` of the other input must satisfy `P | t` being a matching,
  which fixes `t` uniquely per pair, and an edge lies in at most two perfect
  matchings of 3 x 3.  When a gate does produce two matchings, the two pairs it
  reads are disjoint.

Counting.  Let `d` be the number of AND gates that produce two matchings and
`s` the number that produce one; `2d + s >= 6` in a minimal circuit.

* at least 6 gates for the six pairs (F2, F3, F4);
* `d + s` gates for the matching-producing AND gates;
* `d` OR gates to merge two pair wires into one wire for the `d` two-matching
  gates (by F5 the two pairs used by such a gate are disjoint, so they sit on
  two different wires);
* `d + s - 1` OR gates to merge the matching wires into the output.

Total: `6 + (d + s) + d + (d + s - 1)`, and `d + s >= 6 - d` with `d <= 3`, so
the total is at least `6 + (6 - d) + d + (5 - d) = 17 - d >= 14`.  The circuit
the desk holds is exactly the case `d = 3` (9 AND, 5 OR), so 14 is optimal and
13 is impossible.

The count is a sketch for the case where a wire holds only monomials that lie
in a matching.  A circuit may also carry "waste": a monomial of size three
that lies in no matching, which has to be multiplied once more to reach the
output as a monomial of size four (such a monomial never changes the value of
the function, so it is allowed there).  The search below is run in the mode
that also covers waste (`complete=True` in the encoder: every monomial of size
at most three is tracked and nothing is forbidden), which makes the machine
answer unconditional; the default mode is the faster one used for the shards
above.

## Reproducing

```
python3 methods/find/pm33_search.py 5400 /tmp/verdict.json
```

`methods/find/pm33_search.py` is the program that was released with the lease
(its sha256 was given to the desk): the monomial-set encoder and the shard
driver in one file.  It runs one exact search per shard, writes the CNF of
every instance to the working directory, and records the verdict in JSON.
Every instance is a few thousand variables; `kissat` answers UNSAT or SAT
directly.

The same search is also available as two files, so that the encoder can be
read on its own: `methods/find/mono_sat.py` is the encoder and
`methods/find/search_pm33.py` the driver that imports it.

`methods/find/pm33_search_portable.py` is the same program as
`pm33_search.py`, byte for byte except for two lines: it takes the solver
from the `KISSAT` environment variable and writes the CNF files to the
directory in `PNP_OUT`, so it runs on any machine without editing the code.
The file `pm33_search.py` itself is published exactly as it was released, so
the hash on record still resolves to it.
