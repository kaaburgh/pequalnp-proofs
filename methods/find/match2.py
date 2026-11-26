#!/usr/bin/env python3
"""L-meta-17326: a counterexample to the lower bound of 16 gates for a 9-input function.

The step (a "refute" step) asks for a circuit of at most 15 gates of fan-in two that
computes

  f (x) = (x0&&x4) || (x0&&x5) || (x1&&x5) || (x0&&x6) || (x2&&x6) || (x3&&x6)
          || (x1&&x7) || (x2&&x7) || (x4&&x7) || (x1&&x8) || (x3&&x8) || (x5&&x8)

and whose FIRST gate (the one that writes wire 9) computes !x0, or (x0 && xj), or (x0 || xj)
for some j > 0.

The encoder is the one of triangle20.py: every gate picks an operation and two pins out of
the wires that exist before it, and the whole circuit is replayed on every input.

    python3 match2.py --gates 15            # the search
    python3 match2.py --gates 15 --first    # with the condition on the first gate
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import triangle20 as T           # noqa: E402

T.NIN = 9                       # this function has nine inputs

PAIRS = [(0, 4), (0, 5), (1, 5), (0, 6), (2, 6), (3, 6),
         (1, 7), (2, 7), (4, 7), (1, 8), (3, 8), (5, 8)]


def f(bits):
    """The posted function: 1 exactly when two of the twelve pairs are both true."""
    for i, j in PAIRS:
        if (bits >> i) & 1 and (bits >> j) & 1:
            return True
    return False


def g(bits):
    """The complement of f: 1 exactly when no two of the twelve pairs are both true."""
    return not f(bits)


def maximal_independent_sets():
    """The maximal sets of inputs with no pair of the twelve: the minimal true sets of g."""
    out = []
    for bits in range(1 << T.NIN):
        if not g(bits):
            continue
        if all(not g(bits | (1 << i)) for i in range(T.NIN) if not (bits >> i) & 1):
            out.append(bits)
    return out


def maximal_false_sets():
    """The maximal sets on which g is false: the maximal sets holding one of the pairs."""
    out = []
    for bits in range(1 << T.NIN):
        if g(bits):
            continue
        if all(g(bits | (1 << i)) for i in range(T.NIN) if not (bits >> i) & 1):
            out.append(bits)
    return out


# the encoder asks has_triangle(row) for the value the circuit must have there
T.has_triangle = f


def reduced_rows():
    """The rows that decide f for a MONOTONE circuit: the twelve minimal true sets (the
    pairs) and the maximal sets with no pair.  A circuit with a NOT gate is not monotone,
    so for those the search has to grow the rows (the lazy loop)."""
    rows = []
    for i, j in PAIRS:
        rows.append((1 << i) | (1 << j))
    for bits in range(1 << T.NIN):
        if not f(bits) and all(not f(bits | (1 << i))
                               for i in range(T.NIN) if not (bits >> i) & 1):
            rows.append(bits)
    return rows


T.rows_for_check = reduced_rows


def first_gate_ok(gates):
    """The condition of the step on the first gate: !x0, or x0 && xj, or x0 || xj (j > 0)."""
    if not gates:
        return False, "no gate"
    op, pins = gates[0]
    pins = [p for p in pins if p < 9]
    if op == "not" and pins == [0]:
        return True, "not x0"
    if op in ("and", "or") and len(pins) == 2 and 0 in pins:
        j = pins[1] if pins[0] == 0 else pins[0]
        if j > 0:
            return True, "%s x0 x%d" % (op, j)
    return False, "%s %s" % (op, pins)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--gates", type=int, default=15)
    ap.add_argument("--solver", default="/workspace/pnp/kissat")
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--target", choices=["f", "g"], default="f",
                    help="f is the posted function, g its complement (monotone)")
    ap.add_argument("--reduced", action="store_true",
                    help="use the rows that decide a monotone function (only sound for g)")
    ap.add_argument("--lazy", action="store_true",
                    help="start from the rows that decide the function and add the rows a "
                         "candidate circuit gets wrong")
    args = ap.parse_args()

    target = f if args.target == "f" else g
    T.has_triangle = target
    if args.lazy:
        verdict, rows, witness = T.lazy_search(args.gates, True, args.solver,
                                                "/workspace/output/_t20", 60)
        print("lazy search:", verdict, "with", len(rows), "rows")
        if witness:
            gs, out = witness
            ok, why = first_gate_ok(gs)
            print("the circuit has %d gates, output wire %d" % (len(gs), out))
            print("the first gate: %s -> the condition of the step: %s"
                  % (why, "yes" if ok else "no"))
            print(T.lean_of(gs, out))
        return 0 if verdict == "sat" else 1
    if args.reduced:
        rows = maximal_independent_sets() + maximal_false_sets()
    else:
        rows = list(range(1 << T.NIN))
    print("searching: %d gates for %s, %d rows" % (args.gates, args.target, len(rows)))
    cnf, layout = T.build(rows, args.gates, with_not=True)
    verdict, txt = T.solve(cnf, args.solver, "/workspace/output/_t20",
                           "m2_%s_g%d" % (args.target, args.gates))
    print("verdict:", verdict)
    if verdict != "sat":
        return 1
    gs, out = T.decode(layout, txt)
    bad = [x for x in range(1 << T.NIN) if T.evaluate(gs, out, x) != target(x)]
    print("the circuit has %d gates, output wire %d, wrong on %d of %d inputs"
          % (len(gs), out, len(bad), 1 << T.NIN))
    ok, why = first_gate_ok(gs)
    print("the first gate: %s -> the condition of the step: %s" % (why, "yes" if ok else "no"))
    if not bad:
        print(T.lean_of(gs, out))
    return 0 if (not bad and ok) else 1


if __name__ == "__main__":
    sys.exit(main())
