#!/usr/bin/env python3
"""Exhaustive search for L-meta-18625.

The step asks for a circuit of AND and OR gates of fan-in at most two, with at
most 9 gates, that is right on every input with one or two 1s: false on the seven
inputs with a single 1, and on the twenty-one inputs with two 1s true exactly
when the two vertices are joined on the seven-cycle.

The program asks the SAT solver whether such a circuit exists, for every size
from 9 down to 1.  The output gate may be taken to be the last gate, so the
sizes cover every circuit of at most 9 gates.  A SAT answer is a witness and is
checked on the 28 inputs; UNSAT for every size means the step's statement cannot
be satisfied.

Usage:  python3 search_7cycle_9.py [timeout per size]
"""
import subprocess
import sys
import os
import json
import hashlib

KISSAT = "/workspace/pnp/kissat"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sat_search import build_cnf, write_dimacs, run_kissat, decode, verify  # noqa: E402

N = 7        # the vertices of the seven-cycle
SIDES = 7


def rows_and_target():
    """the 28 promised inputs and the wanted value on each of them"""
    rows = []
    target = [0] * (1 << N)
    for v in range(SIDES):                     # one 1
        x = 1 << v
        rows.append(x)
        target[x] = 0
    for a in range(SIDES):                     # two 1s
        for b in range(a + 1, SIDES):
            x = (1 << a) | (1 << b)
            rows.append(x)
            adjacent = (b == (a + 1) % SIDES) or (a == (b + 1) % SIDES)
            target[x] = 1 if adjacent else 0
    return rows, target


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    rows, target = rows_and_target()
    print(f"rows: {len(rows)}  true rows: {sum(target[r] for r in rows)}", flush=True)
    verdict = {}
    for K in range(9, 0, -1):
        clauses, nv, info = build_cnf(N, K, target, rows, ("and", "or"))
        path = f"/workspace/output/c7_K{K}.cnf"
        write_dimacs(clauses, nv, path)
        model, status = run_kissat(path, timeout)
        print(f"K={K}: vars={nv} clauses={len(clauses)} -> {status}", flush=True)
        verdict[K] = status
        os.remove(path)
        if model is not None:
            gates = decode(model, N, K, info, ("and", "or"))
            ok, bad = verify(gates, N, target, rows)
            print("   witness:", gates, "verified:", ok, flush=True)
            if ok:
                json.dump({"n": N, "gates": gates, "output": N + K - 1},
                          open("/workspace/output/c7_witness.json", "w"))
                print("SAVED WITNESS", flush=True)
                return
    print("VERDICT:", json.dumps(verdict), flush=True)
    with open(os.path.abspath(__file__), "rb") as fh:
        digest = hashlib.sha256(fh.read()).hexdigest()
    print("sha256 of this program:", digest, flush=True)
    json.dump({"verdict": verdict, "empty": all(v == "UNSAT" for v in verdict.values())},
              open("/workspace/output/c7_verdict.json", "w"))
    if all(v == "UNSAT" for v in verdict.values()):
        print("NO CIRCUIT OF AT MOST 9 GATES EXISTS: the statement of L-meta-18625 is false",
              flush=True)


if __name__ == "__main__":
    main()
