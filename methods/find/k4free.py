#!/usr/bin/env python3
"""L-meta-17435: the K4-free function on the 10 edge bits of K5.

Statement (posted):
  HasCircuitSize 10 (fun x => !((x4&&x5&&x6&&x7&&x8&&x9) || (x0&&x2&&x3&&x5&&x6&&x9)
                             || (x0&&x1&&x3&&x4&&x6&&x8) || (x0&&x1&&x2&&x4&&x5&&x7)
                             || (x1&&x2&&x3&&x7&&x8&&x9))) 20

The five terms are the five K4's of K5 (K4 missing vertex v = the six edges away from v).
f = 1 iff the graph on the 10 edge bits contains no K4.

Gate semantics (PEqualNP.Defs.CircuitLowerBounds):
  and = all of its inputs, or = any of its inputs, not = NOT of its first input.
  Gate j (0-based) produces wire 10 + j; a wire that does not exist yet reads false.
"""

import itertools
import sys

N = 10

# S_v = the six edges away from vertex v (edges are numbered 0..9 as in the statement).
S = {
    0: (4, 5, 6, 7, 8, 9),
    1: (1, 2, 3, 7, 8, 9),
    2: (0, 2, 3, 5, 6, 9),
    3: (0, 1, 3, 4, 6, 8),
    4: (0, 1, 2, 4, 5, 7),
}


def f(bits):
    """The posted function: NOT of the OR of the five K4 terms."""
    for v in S:
        if all(bits[e] for e in S[v]):
            return False
    return True


def evaluate(gates, output, bits):
    """gates: list of (op, (i, j)); op in 'and', 'or', 'not'. Returns the output wire value."""
    wires = list(bits)  # wires 0..9 are the inputs
    for op, ins in gates:
        if op == "and":
            val = all(wires[i] if i < len(wires) else False for i in ins)
        elif op == "or":
            val = any(wires[i] if i < len(wires) else False for i in ins)
        elif op == "not":
            i = ins[0]
            val = not (wires[i] if i < len(wires) else False)
        else:
            raise ValueError(op)
        wires.append(val)
    return wires[output] if output < len(wires) else False


def check(gates, output, name, verbose=True):
    """Check the circuit against f on all 1024 inputs."""
    bad = []
    for x in range(1 << N):
        bits = [(x >> i) & 1 == 1 for i in range(N)]
        got = evaluate(gates, output, bits)
        want = f(bits)
        if got != want:
            bad.append((x, got, want))
            if len(bad) > 5:
                break
    counts = {}
    for op, _ in gates:
        counts[op] = counts.get(op, 0) + 1
    if verbose:
        print(f"{name}: {len(gates)} gates {counts} -> "
              + ("CORRECT on all 1024 inputs" if not bad else f"WRONG on {len(bad)} inputs"))
    return not bad


class Builder:
    """Appends gates and hands back the wire index of each new gate."""

    def __init__(self):
        self.gates = []

    def add(self, op, a, b=None):
        self.gates.append((op, (a,)) if b is None else (op, (a, b)))
        return N + len(self.gates) - 1

    def prod(self, vars_):
        """A product of the given wire indices; returns the output wire."""
        vs = list(vars_)
        w = vs[0]
        for v in vs[1:]:
            w = self.add("and", w, v)
        return w


def build_cycle():
    """g = OR of the five K4 products, shared through the 5-cycle of pair intersections.

    S_v & S_w have exactly three elements, so the product of S_v & S_w can be shared by
    the trees of v and w.  Around the cycle 0-1-2-3-4-0 each S_v is the union of its two
    cycle-neighbour intersections plus one leftover variable.
    """
    cyc = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    inter = {(a, b): tuple(sorted(set(S[a]) & set(S[b]))) for a, b in cyc}
    b = Builder()
    pwire = {}
    for a, bb in cyc:
        pwire[(a, bb)] = b.prod(inter[(a, bb)])
    for v in range(5):
        (a, bb) = ((v - 1) % 5, v)
        (c, d) = (v, (v + 1) % 5)
        left = sorted(set(S[v]) - set(inter[(a, bb)]) - set(inter[(c, d)]))
        assert len(left) == 1, (v, left)
        w = b.add("and", pwire[(a, bb)], pwire[(c, d)])
        w = b.add("and", w, left[0])
        pwire[("t", v)] = w
    out = pwire[("t", 0)]
    for v in range(1, 5):
        out = b.add("or", out, pwire[("t", v)])
    out = b.add("not", out)
    return b.gates, out


def build_pairs():
    """g = OR of the five K4 products, combining them in pairs.

    (AND A) OR (AND B) = (AND (A & B)) AND ((AND (A \\ B)) OR (AND (B \\ A)))
    so two K4's sharing three edges cost 8 gates instead of 9 plus a later OR.
    """
    b = Builder()

    def pair_or(v, w):
        sv, sw = set(S[v]), set(S[w])
        p = b.prod(tuple(sorted(sv & sw)))
        pa = b.prod(tuple(sorted(sv - sw)))
        pb = b.prod(tuple(sorted(sw - sv)))
        return b.add("and", p, b.add("or", pa, pb))

    n01 = pair_or(0, 1)
    n23 = pair_or(2, 3)
    t4 = b.prod(S[4])
    out = b.add("or", n01, n23)
    out = b.add("or", out, t4)
    out = b.add("not", out)
    return b.gates, out


def main():
    ok = True
    g, o = build_cycle()
    ok &= check(g, o, "cycle DNF")
    g, o = build_pairs()
    ok &= check(g, o, "pair DNF")
    print("all good" if ok else "FAILURES")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
