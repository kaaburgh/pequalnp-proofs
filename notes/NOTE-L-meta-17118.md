# L-meta-17118: the Hamiltonian cycle on five vertices, at most 23 gates

Lease `fbe690ca-6b5a-47ca-b2d2-d6336ae6e2fd`, range 14 of 16:
*at most 23 gates in all, with 3 or more NOT gates and 12 to 17 AND gates.*

The statement is
`HasCircuitSize 10 (fun x => <the ten edges contain a Hamiltonian cycle on five
vertices>) 23`.  The desk holds 26 gates, with no NOT gate, and says that a solver
run below 26 did not finish.

## What is in this branch

`methods/find/search_5cycle_range.py` is the search program for the range.  It

* lists the twelve cycles of the complete graph on five vertices and builds the
  truth table of the step's function (218 true rows out of 1024);
* for every total size `G = 15, ..., 23` asks the SAT solver (`kissat`) whether a
  `G`-gate circuit of AND, OR and NOT gates of fan-in at most two exists whose
  profile lies in the range: at least 3 NOT gates, between 12 and 17 AND gates.
  The counts are forced by cardinality constraints, so one instance per size
  covers all the (NOT count, AND count) profiles of the range at once;
* takes the output gate to be the last gate, which loses nothing: any circuit can
  be reordered so that its output comes last, so the sizes `G = 15, ..., 23`
  cover every circuit of at most 23 gates;
* prints a witness (a gate list, checked on all 1024 inputs) if it finds one.

The supporting code is in `methods/find/sat_search.py` (the circuit encoding and
the checker) and `methods/find/hole_search.py` (the one-hole search below).

## What was already ruled out

`methods/find/hole_search.py` takes the desk's 26-gate circuit, drops one gate and
lets the SAT solver rebuild that single gate (its operation and the two wires it
reads) so that the circuit still computes the function on all 1024 inputs.  All
fourteen holes are UNSAT: **no circuit of 23 gates is one gate away from the
26-gate circuit.**  The same search on the other functions of this branch is
reported in `NOTE-sat-search.md`.

## Why 26 is natural, and what a smaller circuit would have to do

Every cycle through a vertex `v` with its two cycle-neighbours `a` and `b` uses
the wedge `v-a, v-b`, the edge `a-b` and a matching of two disjoint edges on the
remaining two vertices; the twelve cycles are six wedges times two matchings.  The
desk's 26-gate circuit groups the twelve cycles into three classes of four, each
class being `(wedge-and-middle, or) and (matching, or)`, and the class term is
correct only because the cross combinations never spell a cycle.  Factoring a
common *edge* out of two terms is the one distributive move that would save a
gate, and the two wedges of a class share a *vertex*, not an edge, so it does not
apply; this is why 26 is hard to beat inside this family, and why a circuit with
NOT gates would have to be built in a different shape altogether.
