#!/usr/bin/env python3
"""Exhaustive search for the range of L-meta-18791.

The step asks for a circuit of exactly 10 AND, OR and NOT gates of fan-in at most
two that computes the seven-cycle function

    (x 0 && x 1) || (x 1 && x 2) || ... || (x 6 && x 0)

and in which the input x_0 is listed by exactly one gate, that gate is an OR, a
later AND gate reads it, and that gate is true at some input where x_0, x_1 and
x_6 are all false.

The desk hands out the nine shards of this search separately: shard i asks for
the gate that lists x_0 to be gate i.  The program below searches every shard in
turn: for each i it asks the SAT solver (`kissat`) whether such a circuit
exists, and it checks a witness by evaluating it on all 128 inputs.

The output gate may be taken to be the last gate, so ten gates cover every
circuit of at most ten gates.

Usage:  python3 search_7cycle_shape.py [timeout per shard]
"""
import subprocess
import sys
import os
import json
import hashlib

KISSAT = "/workspace/pnp/kissat"
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sat_search import build_cnf, write_dimacs, run_kissat, decode, verify  # noqa: E402

N = 7        # the seven edges of the seven-cycle, in order
GATES = 10   # the size of the circuits the step asks for


def target_table():
    """the seven-cycle function on all 128 inputs"""
    t = [0] * (1 << N)
    for x in range(1 << N):
        for i in range(N):
            if (x >> i) & 1 and (x >> ((i + 1) % N)) & 1:
                t[x] = 1
                break
    return t


def build_shard_cnf(shard, target, rows, types=("and", "or", "not")):
    """the instance for one shard: the gate listing x_0 is the gate at `shard`"""
    clauses, nv, info = build_cnf(N, GATES, target, rows, types)

    def newvar():
        nonlocal nv
        nv += 1
        return nv

    selA, selB, tid, V = info["selA"], info["selB"], info["tid"], info["V"]
    wire_x0 = 0            # the input wire x_0
    wire_g = N + shard     # the wire written by the gate at `shard`

    # (a) the gate at `shard` lists x_0, and no other gate does
    clauses.append([selA[shard][wire_x0]])
    for g in range(GATES):
        if g == shard:
            continue
        for s in (selA[g], selB[g]):
            if wire_x0 < len(s):
                clauses.append([-s[wire_x0]])

    # (b) the gate at `shard` is an OR
    for t in types:
        if t != "or":
            clauses.append([-tid[t][shard]])
    clauses.append([tid["or"][shard]])

    # (c) some later AND gate reads the wire of the gate at `shard`
    later = []
    for k in range(shard + 1, GATES):
        if wire_g < len(selA[k]):
            pick = newvar()
            # pick <-> (tAND[k] and (selA[k][wire_g] or selB[k][wire_g]))
            clauses.append([-pick, tid["and"][k]])
            clauses.append([-pick, selA[k][wire_g]])
            clauses.append([-pick, selB[k][wire_g]])
            clauses.append([pick, -tid["and"][k], -selA[k][wire_g], -selB[k][wire_g]])
            later.append(pick)
    if later:
        clauses.append(later)
    else:
        clauses.append([])      # unsatisfiable: no later gate exists

    # (d) the gate at `shard` is true at some input with x_0 = x_1 = x_6 = false
    cand = [r for r in rows if (r & 0b1000011) == 0]     # bits 0, 1 and 6 clear
    picks = []
    for r in cand:
        q = newvar()
        picks.append(q)
        clauses.append([-q, V[shard][r]])                # q -> the gate is true there
    clauses.append(picks)                                # some such row is chosen
    return clauses, nv, info


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 1800
    target = target_table()
    rows = list(range(1 << N))
    print(f"function: seven-cycle on {N} edges, {len(rows)} inputs, {GATES} gates", flush=True)
    verdict = {}
    for shard in range(9):
        clauses, nv, info = build_shard_cnf(shard, target, rows)
        path = f"/workspace/output/c7shape_{shard}.cnf"
        write_dimacs(clauses, nv, path)
        model, status = run_kissat(path, timeout)
        print(f"shard {shard}: vars={nv} clauses={len(clauses)} -> {status}", flush=True)
        verdict[shard] = status
        if model is not None:
            gates = decode(model, N, GATES, info, ("and", "or", "not"))
            ok, bad = verify(gates, N, target, rows)
            print("   witness:", gates, "verified:", ok, flush=True)
            if ok:
                json.dump({"n": N, "gates": gates, "output": N + GATES - 1},
                          open("/workspace/output/c7shape_witness.json", "w"))
                print("SAVED WITNESS for shard", shard, flush=True)
                break
        os.remove(path)
    with open(os.path.abspath(__file__), "rb") as fh:
        digest = hashlib.sha256(fh.read()).hexdigest()
    print("VERDICT:", json.dumps(verdict), flush=True)
    print("sha256 of this program:", digest, flush=True)
    json.dump({"verdict": verdict, "sha256": digest},
              open("/workspace/output/c7shape_verdict.json", "w"))


if __name__ == "__main__":
    main()
