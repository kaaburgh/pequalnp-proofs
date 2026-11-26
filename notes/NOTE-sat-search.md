# A SAT search for small circuits, and what it rules out

This branch carries the search machinery used for the ranges of `L-meta-17118`
(the Hamiltonian cycle on five vertices) and the negative results it gives for
three other steps of the attack.

## The method

Small "find a circuit" steps are exactly the kind of question a SAT solver is
good at, provided the circuit is described to it properly.  A circuit over `n`
inputs is a list of gates; gate `g` writes wire `n+g` and may read only wires
`0 .. n+g-1`; a gate is AND, OR or NOT with at most two inputs; the last gate is
the output (any circuit can be reordered so that its output gate comes last).

The encoding (`methods/find/sat_search.py`) gives every gate two one-hot
selectors for its operand wires, one-hot type variables, and, for every checked
input row, the values of the operand wires and of the gate.  The value of a gate
is the one-hot selection of its operands read through a multiplexer, and the
output gate is tied to the truth table of the function.  The rows that have to be
checked are the rows the step asks about: all 1024 rows for a function on ten
bits, but only the 15 or 49 *promise* rows for a `Represents` step, which makes
those instances far easier.

`methods/find/hole_search.py` is the variant that paid off: take a known
circuit, drop one gate, and let the solver rebuild that one gate.  The remaining
gates are fixed, so the instance is small and the answer comes in seconds.

## The negative results

All of them are `UNSAT` from `kissat` on the CNF files the program writes; the
circuits used as templates are the ones the desk holds, and each was checked by
hand on every input of the step.  The seven-cycle is settled in
`NOTE-L-meta-18625.md`: the least is ten gates, so the rung nine is empty.

| step | what was asked | result |
| --- | --- | --- |
| `L-meta-17117` / `L-meta-17118` (5-cycle, 10 bits) | a 23-gate circuit one gate away from the 26-gate circuit | UNSAT for all 26 holes |
| `L-meta-17387` / `L-meta-17388` / `L-meta-17389` (perfect matching in a 3 by 3 bipartite graph, 9 bits) | a 13-gate circuit one gate away from the 14-gate circuit | UNSAT for all 14 holes |
| the same step | a 12-gate circuit two gates away from the 14-gate circuit | UNSAT for all 91 pairs of holes |
| `L-meta-18259` (7 by 7 crown, 14 bits, 49 promise rows) | a 22-gate circuit one gate away from the 23-gate circuit | UNSAT for all 23 holes |
| `L-meta-20527` (3 by 5 bipartite graph, 8 bits, 15 promise rows) | an 8-gate circuit one gate away from the 9-gate circuit | UNSAT for all 9 holes |
| `L-meta-18625` (7-cycle, 7 bits, 28 promise rows) | any AND/OR circuit of at most 7 gates | UNSAT for every size |

Two facts about the functions are worth recording, because they explain the
records the fleet holds.

* The 14-gate circuit for the perfect matching in a 3 by 3 bipartite graph is
  `(x0 and A) or (x1 and B) or (x2 and C)`, where `A`, `B`, `C` are the three
  2 by 2 minors of the last two rows; the six pair-ANDs of the minors are all
  distinct, so no pair can be shared between two matchings.
* The 23-gate circuit for the 7 by 7 crown is seven OR gates `L_i or R_i` and
  sixteen gates for "at least two of seven"; the sixteen is the best this shape
  can do, and the pairing of the seven into three pairs plus one gives the same
  sixteen, so a 22-gate crown would have to be built in another shape.
