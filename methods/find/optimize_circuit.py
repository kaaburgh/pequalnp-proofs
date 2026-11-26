#!/usr/bin/env python3
"""Stochastic circuit optimiser.

Searches for a small AND/OR/NOT circuit of fan-in at most two that agrees with a
target function on a set of rows (the whole cube, or a promise set).  The objective
is the number of gates; a partial-credit score (number of rows satisfied) guides
the walk when the circuit is not yet correct.

Moves: change a gate's operation, rewire one of its inputs, delete a gate (and
repair the references), insert a gate.
"""
import random
import sys


def eval_circuit(gates, n, x):
    bank = [(x >> i) & 1 for i in range(n)]
    for op, ins in gates:
        vals = [bank[i] for i in ins]
        if op == "and":
            bank.append(int(all(vals)))
        elif op == "or":
            bank.append(int(any(vals)))
        else:
            bank.append(1 - vals[0])
    return bank[n + len(gates) - 1]


def score(gates, n, target, rows):
    """(number of wrong rows, number of gates)"""
    wrong = 0
    for x in rows:
        if eval_circuit(gates, n, x) != (1 if target[x] else 0):
            wrong += 1
    return wrong, len(gates)


def repair(gates, n, out_wire, deleted):
    """after deleting gate `deleted`, fix the wire references and the output wire."""
    cut = n + deleted

    def fix(w):
        return w - 1 if w >= cut else w

    newg = [(op, [fix(i) for i in ins]) for op, ins in gates]
    out = fix(out_wire)
    if out >= n + len(newg):
        out = n + len(newg) - 1
    return newg, out


def mutate(gates, n, out_wire, rng, kinds=("and", "or")):
    g = [(op, list(ins)) for op, ins in gates]
    out = out_wire
    m = rng.random()
    if not g:
        return [("or", [rng.randrange(n), rng.randrange(n)])], out
    if m < 0.40:                      # change the operation of a gate
        i = rng.randrange(len(g))
        op = rng.choice(kinds)
        g[i] = (op, g[i][1])
    elif m < 0.80:                    # rewire an input of a gate
        i = rng.randrange(len(g))
        if rng.random() < 0.5 and len(g[i][1]) == 2:
            j = rng.choice([0, 1])
            g[i][1][j] = rng.randrange(n + i)
        else:
            g[i] = (g[i][0], [rng.randrange(n + i)])
    elif m < 0.95:                    # delete a gate and repair the references
        i = rng.randrange(len(g))
        del g[i]
        g, out = repair(g, n, out, i)
    else:                             # insert a gate
        i = rng.randrange(len(g) + 1)
        op = rng.choice(kinds)
        ins = [rng.randrange(n + i), rng.randrange(n + i)]
        g.insert(i, (op, ins))
        if out >= n + i:
            out += 1
    return g, out


def optimise(n, target, rows, start=None, out_wire=None, iters=200000, seed=0,
             kinds=("and", "or"), verbose=True):
    rng = random.Random(seed)
    if start is None:
        g = [("or", [rng.randrange(n), rng.randrange(n)]) for _ in range(3)]
        out = n + len(g) - 1
    else:
        g = [(op, list(ins)) for op, ins in start]
        out = out_wire if out_wire is not None else n + len(g) - 1
    best = (score(g, n, target, rows), list(g), out)
    cur_wrong, cur_len = best[0]
    cur = list(g)
    T = 1.0
    for it in range(iters):
        ng, nout = mutate(cur, n, out, rng, kinds)
        w, l = score(ng, n, target, rows)
        key = (w, l)
        curkey = (cur_wrong, cur_len)
        accept = key < curkey or (w == cur_wrong and rng.random() < 0.02) or \
            rng.random() < 0.0005 * T
        if accept:
            cur, out, cur_wrong, cur_len = ng, nout, w, l
            if (w, l) < best[0]:
                best = ((w, l), list(ng), nout)
                if verbose:
                    print(f"  it={it} wrong={w} gates={l}", flush=True)
                if w == 0 and l <= 12:
                    break
        T *= 0.99995
        if it % 20000 == 0 and verbose:
            print(f"  it={it} best={best[0]}", flush=True)
    return best


def main():
    import sat_search as S
    which = sys.argv[1]
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
    if which == "crown7":
        n, target, rows = S.crown(7)
        start = crown23(n)
        out = n + len(start) - 1
        print("start gates:", len(start), "wrong:", score(start, n, target, rows)[0], flush=True)
        best = optimise(n, target, rows, start, out, iters=iters, seed=seed)
    elif which == "t2_7":
        n, target, rows = S.at_least_two_of_seven()
        start = t2_7_sixteen(n)
        out = n + len(start) - 1
        print("start gates:", len(start), "wrong:", score(start, n, target, rows)[0], flush=True)
        best = optimise(n, target, rows, start, out, iters=iters, seed=seed)
    else:
        raise SystemExit("unknown")
    print("BEST:", best[0], best[2])
    print("gates:", best[1])


def crown23(n):
    """the fleet's 23-gate crown circuit: o_i = L_i or R_i, then at least two of the seven."""
    side = n // 2
    g = []
    o = []
    for i in range(side):
        g.append(("or", [i, side + i])); o.append(n + len(g) - 1)
    # suffix ors s_i = o_i or s_{i+1}
    s = [None] * side
    s[side - 1] = o[side - 1]
    for i in range(side - 2, 0, -1):
        g.append(("or", [o[i], s[i + 1]])); s[i] = n + len(g) - 1
    terms = []
    for i in range(side - 1):
        g.append(("and", [o[i], s[i + 1]])); terms.append(n + len(g) - 1)
    acc = terms[0]
    for t in terms[1:]:
        g.append(("or", [acc, t])); acc = n + len(g) - 1
    return g


def t2_7_sixteen(n):
    """at least two of seven, sixteen gates."""
    g = []
    s = [None] * 7
    s[6] = 6
    for i in range(5, 0, -1):
        g.append(("or", [i, s[i + 1]])); s[i] = n + len(g) - 1
    terms = []
    for i in range(6):
        g.append(("and", [i, s[i + 1]])); terms.append(n + len(g) - 1)
    acc = terms[0]
    for t in terms[1:]:
        g.append(("or", [acc, t])); acc = n + len(g) - 1
    return g


if __name__ == "__main__":
    main()
