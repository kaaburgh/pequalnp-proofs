#!/usr/bin/env python3
"""The structure of the 9-input function of L-meta-17326, and the best circuit found.

The function of the step is

  f (x) = (x0&&x4) || (x0&&x5) || (x1&&x5) || (x0&&x6) || (x2&&x6) || (x3&&x6)
          || (x1&&x7) || (x2&&x7) || (x4&&x7) || (x1&&x8) || (x3&&x8) || (x5&&x8)

Let H be the graph on the nine inputs whose twelve edges are those pairs.  Then f = 1
exactly when the set of true inputs contains an edge of H, and H is the Petersen graph
with one vertex deleted (the Petersen graph is the Kneser graph KG(5,2), the graph on the
two-subsets of a five-set with two vertices joined when they are disjoint).

The complement g = "no edge of H has both ends true" is antitone.  Its maximal true sets
are the five stars of the K5 the Petersen graph comes from, and

  g = (AND over a star) | (AND over a star) | ...   (five of them)

is its DNF.  Factoring the DNF (the OR of two products sharing a variable is
x & (A | B)) gives a circuit for g with 15 gates, and f = NOT g with 16.

A monotone circuit for f needs at least 12 AND gates (one for each of the twelve minimal
true sets: on the pair {i,j} alone the circuit must be 1, so it must contain the gate
i AND j) and eleven OR gates to join them: 23.

    python3 structure17326.py
"""

import itertools

PAIRS = [(0, 4), (0, 5), (1, 5), (0, 6), (2, 6), (3, 6),
         (1, 7), (2, 7), (4, 7), (1, 8), (3, 8), (5, 8)]
NIN = 9


def f(bits):
    return any((bits >> i) & 1 and (bits >> j) & 1 for i, j in PAIRS)


def g(bits):
    return not f(bits)


def neighbours():
    a = {v: set() for v in range(NIN)}
    for i, j in PAIRS:
        a[i].add(j)
        a[j].add(i)
    return a


def maximal_independent_sets():
    """The maximal sets with no edge of H: the five stars."""
    out = []
    for bits in range(1 << NIN):
        if not g(bits):
            continue
        if all(not g(bits | (1 << i)) for i in range(NIN) if not (bits >> i) & 1):
            out.append(bits)
    return sorted(out)


def petersen_minus_one():
    """The Petersen graph with one vertex deleted, and the relabelling to H."""
    k = list(itertools.combinations(range(5), 2))
    pet = [set() for _ in range(10)]
    for i in range(10):
        for j in range(i + 1, 10):
            if set(k[i]).isdisjoint(k[j]):
                pet[i].add(j)
                pet[j].add(i)
    h = neighbours()
    # backtracking: map the nine surviving vertices of the Petersen graph to the labels 0..8
    def search(assign, used, rem):
        if not rem:
            return dict(assign)
        v = rem[0]
        for x in range(NIN):
            if x in used:
                continue
            ok = True
            for u, y in assign.items():
                if (v in pet[u]) != (y in h[x]):
                    ok = False
                    break
            if ok:
                assign[v] = x
                got = search(assign, used | {x}, rem[1:])
                if got:
                    return got
                del assign[v]
        return None
    for skip in range(10):
        alive = [v for v in range(10) if v != skip]
        got = search({}, set(), alive)
        if got:
            return skip, got
    return None, None


def build_g():
    """The circuit for g: the DNF of the five stars, factored."""
    stars = maximal_independent_sets()
    # the stars as sets of input indices
    idx = [[i for i in range(NIN) if (s >> i) & 1] for s in stars]
    gates = []

    def add(op, a, b=None):
        gates.append((op, (a,)) if b is None else (op, (a, b)))
        return NIN + len(gates) - 1

    def prod(vs):
        w = vs[0]
        for v in vs[1:]:
            w = add("and", w, v)
        return w

    # pick two stars that share a variable and factor their OR
    best = None
    for a, b in itertools.combinations(range(5), 2):
        sh = set(idx[a]) & set(idx[b])
        if len(sh) == 1:
            cost = len(idx[a]) - 1 + len(idx[b]) - 1 + 2      # two products and the merge
            if best is None or cost < best[0]:
                best = (cost, a, b, sh)
    _, a, b, sh = best
    only_a = [i for i in idx[a] if i not in sh]
    only_b = [i for i in idx[b] if i not in sh]
    w = add("and", prod(only_a), prod(only_b))
    w = add("and", list(sh)[0], w)
    others = [prod(idx[k]) for k in range(5) if k not in (a, b)]
    cur = w
    for o in others:
        cur = add("or", cur, o)
    return gates, cur, stars


def evaluate(gates, out, bits):
    w = [bool((bits >> i) & 1) for i in range(NIN)]
    for op, ins in gates:
        vals = [w[p] if 0 <= p < len(w) else False for p in ins]
        if op == "and":
            v = all(vals)
        elif op == "or":
            v = any(vals)
        else:
            v = not vals[0]
        w.append(v)
    return w[out] if 0 <= out < len(w) else False


def main():
    skip, inv = petersen_minus_one()
    print("H is the Petersen graph with the vertex %s deleted" % skip)
    if inv:
        print("the nine vertices of H correspond to the two-subsets",
              {v: sorted(k) for k, v in sorted(inv.items(), key=lambda kv: kv[1])})
    stars = maximal_independent_sets()
    print("the maximal true sets of g (the five stars):",
          [[i for i in range(NIN) if (s >> i) & 1] for s in stars])
    gates, out = build_g()
    bad = [x for x in range(1 << NIN) if evaluate(gates, out, x) != g(x)]
    counts = {}
    for op, _ in gates:
        counts[op] = counts.get(op, 0) + 1
    print("the circuit for g: %d gates %s, wrong on %d of %d inputs"
          % (len(gates), counts, len(bad), 1 << NIN))
    gates2 = gates + [("not", (out,))]
    out2 = NIN + len(gates2) - 1
    bad2 = [x for x in range(1 << NIN) if evaluate(gates2, out2, x) != f(x)]
    print("the circuit for f (NOT g): %d gates, wrong on %d of %d inputs"
          % (len(gates2), len(bad2), 1 << NIN))
    for i, (op, ins) in enumerate(gates2):
        print("  gate %2d: %s %s -> wire %d" % (i, op, list(ins), NIN + i))
    print("  output wire", out2)


if __name__ == "__main__":
    main()
