#!/usr/bin/env python3
"""Exhaustive search for the range of L-meta-17118.

The step: the Hamiltonian cycle on 5 vertices (10 edge bits) has a circuit of AND,
OR and NOT gates of fan-in at most two with at most 23 gates.

The range the desk handed out: at most 23 gates in all, with 3 or more NOT gates
and 12 to 17 AND gates.

For every total size G = 15, ..., 23 the program asks the SAT solver whether a
G-gate circuit with that profile exists.  The output gate may be taken to be the
last gate, so the sizes G cover every circuit of at most 23 gates.  The counts
are forced with cardinality constraints, so each instance covers all the
(not-count, and-count) profiles of the range at once.

Usage:  python3 search_5cycle_range.py [timeout per size]
"""
import subprocess
import sys
import json
import os

KISSAT = "/workspace/pnp/kissat"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sat_search import build_cnf, write_dimacs, run_kissat, decode, verify  # noqa: E402

N = 10   # edge bits of the complete graph on five vertices
EDGES = [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
EDGE_ID = {e: i for i, e in enumerate(EDGES)}


def five_cycle_target():
    """the truth table of "the ten edges contain a Hamiltonian cycle on five vertices"."""
    verts = [0, 1, 2, 3, 4]
    cycles = []
    # every cycle is a cyclic order of the five vertices, up to rotation and reversal
    for tail in verts:
        rest = [v for v in verts if v != tail]
        for perm in [(rest[0], rest[1], rest[2], rest[3]), (rest[0], rest[1], rest[3], rest[2]),
                     (rest[0], rest[2], rest[1], rest[3]), (rest[0], rest[2], rest[3], rest[1]),
                     (rest[0], rest[3], rest[1], rest[2]), (rest[0], rest[3], rest[2], rest[1])]:
            order = [tail] + list(perm)
            edges = []
            for i in range(5):
                a, b = order[i], order[(i + 1) % 5]
                edges.append(EDGE_ID[(min(a, b), max(a, b))])
            key = tuple(sorted(edges))
            if key not in [tuple(sorted(c)) for c in cycles]:
                cycles.append(key)
    target = [0] * (1 << N)
    for x in range(1 << N):
        for c in cycles:
            if all((x >> e) & 1 for e in c):
                target[x] = 1
                break
    return target, cycles


def at_most_k(lits, k, newvar, clauses):
    """sequential counter encoding of 'at most k of lits are true'."""
    m = len(lits)
    if k >= m:
        return
    if k < 0:
        clauses.append(lits)
        return
    s = [[newvar() for _ in range(k)] for _ in range(m + 1)]
    for i in range(m):
        clauses.append([-lits[i], s[i + 1][0]])
        clauses.append([-s[i][0], s[i + 1][0]])
        for j in range(1, k):
            clauses.append([-lits[i], -s[i][j - 1], s[i + 1][j]])
            clauses.append([-s[i][j], s[i + 1][j]])
    clauses.append([-lits[m - 1], -s[m - 1][k - 1]])


def at_least_k(lits, k, newvar, clauses):
    """at least k of lits are true  <=>  at most len(lits) - k of them are false"""
    negs = [-l for l in lits]
    at_most_k(negs, len(lits) - k, newvar, clauses)


def build_range_cnf(K, target, rows, types=("and", "or", "not"), min_not=3,
                    min_and=12, max_and=17):
    """a circuit of exactly K gates with the profile of the range"""
    clauses, nv, info = build_cnf(N, K, target, rows, types)
    # build_cnf numbers its own variables; rebuild a counter on top of them
    def newvar():
        nonlocal nv
        nv += 1
        return nv

    notvars = [info["tid"]["not"][g] for g in range(K)]
    andvars = [info["tid"]["and"][g] for g in range(K)]
    at_most_k(notvars, K - min_not, newvar, clauses)          # at least min_not NOT gates
    at_least_k(andvars, min_and, newvar, clauses)             # at least min_and AND gates
    at_most_k(andvars, max_and, newvar, clauses)              # at most max_and AND gates
    return clauses, nv, info


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 1800
    target, cycles = five_cycle_target()
    rows = list(range(1 << N))
    print(f"cycles: {len(cycles)}  true rows: {sum(target)}", flush=True)
    assert len(cycles) == 12, len(cycles)
    # sanity: the target is the function of the twelve cycles
    for x in range(1 << N):
        want = 1 if any(all((x >> e) & 1 for e in c) for c in cycles) else 0
        assert want == target[x]
    witness = None
    verdict = {}
    for K in range(15, 24):
        clauses, nv, info = build_range_cnf(K, target, rows)
        path = f"/workspace/output/hc5_range_K{K}.cnf"
        write_dimacs(clauses, nv, path)
        model, status = run_kissat(path, timeout)
        print(f"K={K}: vars={nv} clauses={len(clauses)} -> {status}", flush=True)
        verdict[K] = status
        if model is not None:
            gates = decode(model, N, K, info, ("and", "or", "not"))
            ok, bad = verify(gates, N, target, rows)
            print("   verified on all 1024 inputs:", ok, flush=True)
            if ok:
                witness = gates
                break
        os.remove(path)
    if witness:
        print("WITNESS", len(witness), "gates:", witness, flush=True)
        json.dump({"n": N, "gates": witness, "output": N + len(witness) - 1,
                   "name": "hc5_23"}, open("/workspace/output/hc5_witness.json", "w"))
        print("saved /workspace/output/hc5_witness.json", flush=True)
    else:
        print("RANGE EMPTY (exhausted):", verdict, flush=True)
        json.dump({"verdict": verdict, "empty": True},
                  open("/workspace/output/hc5_range_verdict.json", "w"))


if __name__ == "__main__":
    main()
