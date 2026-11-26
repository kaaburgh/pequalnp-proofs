# L-meta-18259 — the 7 by 7 crown at 22 gates

**Handle:** kaaburgh
**Gap:** L-meta-18259 — "The 7 by 7 crown (u joined to v when u and v differ): some
AND/OR circuit of fan-in at most two with at most 22 gates represents it".

## What the step asks

The statement is `PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 7 => decide (u ≠ v)) 22`.
`RepSizeAtMost A s` unfolds to

```
∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ (u : Fin 7) (v : Fin 7), C.eval (oneEach u v) = A u v
```

where `oneEach u v` is the 14-bit input with the u-th left vertex and the v-th
right vertex switched on.  So the circuit is judged on the **49** inputs with
one vertex on each side, and the desk's range rule splits the search by the
number of AND gates:

| shard | range |
|-------|-------|
| 0 | at most 22 gates, at most 3 AND gates |
| 1 | at most 22 gates, 4 to 6 AND gates |
| 2 | at most 22 gates, 7 to 10 AND gates |
| 3 | at most 22 gates, at least 11 AND gates |

The desk holds 23 gates: one OR of the two vertex wires per index (the ladder
`z_i = x_i | y_i`) and then "at least two of the 7 z's" by a prefix chain, which
is `4n - 5` gates in total.  Whether 22 exists is open.

## Two exact encodings

### The monomial-set encoding (`methods/find/mono_sat.py`)

For a monotone circuit the monomial set of the output wire determines the
function it computes, and the value on the input "left vertex u, right vertex
v" is 1 iff the output carries a monomial inside `{x_u, y_v}`.  Hence a correct
circuit of this kind must

* carry all **42** pairs `{x_u, y_v}` with `u ≠ v` (a singleton would also fire
  on `u = v`, so the witness has to be the pair itself), and
* carry neither a diagonal pair `{x_i, y_i}` nor a singleton (those would make
  the circuit wrong on the input `u = v`).

Pairs of two left vertices (or of two right vertices) never change a promised
value — on a one-vertex-per-side input at most one of them is set — so they are
free, and the ladder construction needs them: the wire `z_i | z_j` holds the
monomials `{x_i, x_j}`, `{x_i, y_j}`, `{y_i, x_j}` and `{y_i, y_j}`.  The
candidate set is therefore the 14 singletons and the 84 pairs that are not
diagonal.

That encoding is about 21 000 variables and 425 000 clauses per shard variant.
It is complete only for the clean space (no monomial of size three or more in
the cone), so an UNSAT answer for it is not conclusive; it is good for finding
circuits.

### The row encoding (`methods/find/exact_crown.py`) — exact

The promised-input form can be encoded directly and *exactly*, and much
smaller.  A gate is a wire value on each of the 49 promised rows, so we keep

* one boolean `val[g][r]` per gate and row ("the wire of gate `g` is 1 on row
  `r`"), and
* one-hot selectors for the two operand wires of every gate.

For an input wire the value on a row is a **constant** (it is 1 exactly on the
rows of its index), and for a gate wire it is another `val` variable.  So the
conditional equality "if wire `w` is the selected operand, the operand has the
value of `w` on row `r`" costs two clauses and needs no auxiliary variables:

```
(-sel -v val)   (-sel v -val)     for a gate wire v
(-sel val)                      for a constant-1 input wire
(-sel -val)                     for a constant-0 input wire
```

and the gate itself is six clauses:

```
AND gate:  (-and ¬A ¬B val) (-and ¬val A) (-and ¬val B)
OR  gate:  (and ¬A val)      (and ¬B val)      (and ¬val A B)
```

This gives about **4 300 variables and 95 000 clauses** for the whole
7-by-7-at-22-gates problem — and the encoding is exact, because it constrains
the circuit on exactly the 49 inputs the desk judges, with no restriction on
the monomials that occur inside the circuit.

Two normalisations lose nothing:

* the output is taken to be the last gate (a circuit whose output is an earlier
  gate has dead gates at the end, and a circuit with fewer than 22 gates can be
  padded to 22 with copying gates `or(x, x)`);
* every gate reads two *earlier* wires (a gate reading a later wire or itself
  is a cycle), and both operands may coincide (that is the padding device);
* the output gate is an OR.  This one is a theorem, not a convenience: if the
  output were an AND, its monomials would be the unions of the monomials of
  its two operands, so to carry all 42 cross pairs the first operand would
  have to carry every `{x_i}` and the second every `{y_j}` — and then the
  diagonal pair `{x_i, y_i}` would be a monomial of the output too, which makes
  the circuit wrong on the input `u = v`.

**Symmetry.**  The automorphism group of the promised problem is the same
permutation of the 7 indices on both sides, together with the left/right swap.
The first gate of a circuit reads two input wires, and the orbits of such pairs
are: two left wires (the swap makes two right wires the same orbit), the two
wires of one index `x_i, y_i`, and wires of two different indices `x_i, y_j`.
Three orbits and two operations give six variants, and they cover every
circuit; `methods/find/exact_crown.py` runs them all.

### The threshold encoding (`methods/find/exact_thr2.py`)

The desk's ladder is `z_i = x_i | y_i` (7 gates) followed by "at least two of
the seven `z_i`" (16 gates).  The same exact encoding, with the 128 rows of
the truth table of seven variables and the target "at least two are true",
decides whether that second stage can be done in **15** gates — which would
make the whole crown 22 gates and answer the step.  The threshold function is
invariant under `S_7`, so only two variants are needed.

## What is known

* The ladder the desk holds is 23 gates: 7 OR gates `z_i = x_i | y_i`, then
  the chain `r_i = z_{i+1} | ... | z_7`, the 6 AND gates `z_i & r_{i+1}` and
  the 5 OR gates joining them.  `methods/find/search_crown.py` re-checks it on
  all 49 promised inputs: it holds 6 AND gates and 17 OR gates and its output
  monomials are exactly the 84 non-diagonal pairs.
* The encoder was validated against values that are known independently, and
  it decides them exactly:

  | question | answer the encoder gives |
  |----------|---------------------------|
  | 2 by 2 crown in 2 gates | UNSAT (all six variants) |
  | 2 by 2 crown in 3 gates | SAT, and the circuit checks on all 4 promised inputs |
  | 3 by 3 crown in 6 gates | UNSAT (all six variants) |
  | 3 by 3 crown in 7 gates | SAT, and the circuit checks on all 9 promised inputs |
  | "two of four" in 6 gates | UNSAT (both variants) |
  | "two of three" in 4 gates | SAT, and the circuit checks on all 8 inputs |

  The 3 by 3 crown is therefore exactly 7 gates and "two of four" is exactly
  7 gates, both proved by the solver and not by hand.


## Status

See the verdict files `crown_7x7_k22_*.json` and `thr2_*_k*.json` next to this
note: each records the variant, the status and the size of the instance.
A SAT answer is printed as a gate list and re-checked on the promised inputs
by the program itself, so a hit can be turned straight into the Lean file of
the step.  An UNSAT answer for a variant is conclusive for that variant (the
encoding is exact), so six UNSAT variants would settle the step negatively.

## Running it

```
KISSAT=/path/to/kissat PNP_OUT=/tmp/crown \
  python3 methods/find/exact_crown_portable.py 7 22 3600 /tmp/crown/verdict.json
```

The arguments are `n`, the number of gates bound, the time budget per
instance, the verdict file, and then optionally the AND-count range
(`and_lo`, `and_hi`), the symmetry variant (0 to 5) and the flag `or` that
switches the output-is-OR constraint off.  `methods/find/exact_crown.py` is
the program that was released with the lease, byte for byte, so the sha256 on
record still resolves to it; `methods/find/exact_crown_portable.py` is the
same program except for two lines, which take the solver from the `KISSAT`
environment variable and the CNF directory from `PNP_OUT`, so it runs on any
machine without editing the code.  `methods/find/exact_thr2.py` is the same
encoding for "at least two of n" and is portable already.

**What was run.**  The exact row encoding was run on the whole range
("at most 22 gates", every number of AND gates) for the symmetry variant that
the desk's own ladder starts in (the first gate is `z_0 = x_0 | y_0`), and
the threshold encoding was run on "at least two of seven in 15 gates", which is
the desk's ladder with one gate less.  Neither instance was decided inside the
time the session had:

| instance | variables | clauses | time | verdict |
|----------|-----------|---------|------|---------|
| 7 by 7 at 22 gates, variant `z_0 = x_0 \| y_0` | 4 334 | 95 602 | 3 600 s | no answer |
| the same, restricted to the desk's shard 1 (4 to 6 AND gates) and with the output-is-OR constraint | 4 796 | 96 509 | 1 500 s | no answer |
| "at least two of seven" in 15 gates | 6 195 | 95 343 | 5 400 s | no answer |

The verdict files record which variant was running: `crown_7x7_k22_v1.json` is
the whole range in variant 1, `crown_7x7_k22_sh1_v1.json` the same restricted to
the desk's shard 1, and `thr2_7_k15.json` the threshold instance in variant 0.

**What that means for the step.**  The step is not settled by this work: no
22-gate circuit was found, and the search did not reach an UNSAT answer for
the whole range, so the honest verdict is "no circuit found so far", not "none
exists".  The exact encoding makes the remaining question a pure solver
question: the instance is small enough to keep, and any of the six symmetry
variants that comes back UNSAT removes one sixth of the space.


**A remark on the ladder.**  The ladder is `4n - 5` gates, and the encoding
shows why it is hard to beat: the seven `z_i = x_i | y_i` gates and the prefix
chain feed six AND gates `z_i & r_{i+1}`, and each of those AND gates carries
both orientations of every index pair above `i` at once.  A term built from
raw vertex wires instead (say `x_i` and the OR of the `y_j` with `j != i`)
covers only one orientation and needs an OR chain per index, which costs more
than the ladder does: for `n = 7` that route needs 28 gates.

**A remark on the grid construction.**  The desk's own constructions for the
larger crowns (the 10 by 10 at 34 gates, the 13 by 13 at 45, the 8 by 8 at 27)
are not the ladder: they put the indices on a grid, take the OR of the
`z_i` along every row and along every column, and then take "two of" the row
ORs and "two of" the column ORs, and OR the two together.  A pair of indices
is in different rows or in different columns, so the two "two of" parts cover
every index pair, and a diagonal pair is in the same row *and* the same
column, so it is covered by neither: the circuit is right.  For a full
`m` by `k` grid of indices this costs

```
n  (the z_i)  +  m (k-1) (row ORs)  +  k (m-1) (column ORs)
   +  (3m-5) ("two of" the rows)  +  (3k-5) ("two of" the columns)  +  1
```

which for `n = 9` is 30 and for `n = 16` is 55 by this count (the desk's own
figures for the 10 by 10 and the 13 by 13, 34 and 45, are one gate leaner than
this count, so their version saves a gate somewhere).

For `n = 7` the grid does **not** help: 7 is prime, and enumerating every
placement of seven indices on a grid (up to 5 by 5) shows that the cheapest
grid construction for `n = 7` is **24** gates (a 2 by 4 grid with three cells
empty), against the ladder's 23.  The same holds for the ladder itself: in the
biclique picture (a term is a pair of index sets with nothing in common, and
it covers every index pair across them, in both orientations) the covers of
the 21 index pairs that were worked out by hand all come to 23 gates or more.
So a 22-gate circuit, if there is one, is not a ladder and not a grid: it has
to be something else, and the exact encoding above is the right way to look
for it.




