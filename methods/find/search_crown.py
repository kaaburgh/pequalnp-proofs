#!/usr/bin/env python3
"""Exact search for a monotone AND/OR circuit with at most 22 gates that
represents the 7 by 7 crown graph (L-meta-18259).

The step is promise-style: the circuit is judged on the 49 inputs that have
exactly one vertex on each side.  For a monotone circuit the value on the input
"left vertex u, right vertex v" is 1 iff the output's monomial set holds a
monomial inside {x_u, y_v}.  So the output must hold all 42 pairs {x_u, y_v}
with u != v, must not hold a diagonal pair {x_i, y_i} and must not hold a
singleton, while pairs of two left or two right vertices are free (they never
change a promised value).  A minimum circuit has no monomial of size three or
more (such a monomial cannot help produce a pair and only adds a useless
gate), so the candidate set is the 14 singletons and the 84 non-diagonal pairs.

Symmetry: the crown is invariant under a permutation of the 7 indices, acting
on x_i and y_i together.  The first gate of a circuit reads input wires only,
so its monomial set is a singleton (x side or y side) or a pair (left-left,
right-right or left-right); those are the five orbits below, and each orbit
with both operations gives one variant, so ten variants cover every circuit.

Usage:  python3 search_crown.py [timeout_per_instance] [out.json] [shards]
"""
import json
import sys
import time

from mono_sat import decode, encode, run_kissat

SIDE = 7         # the crown is SIDE by SIDE
N = 2 * SIDE     # x_0..x_{SIDE-1} then y_0..y_{SIDE-1}
K = 22
SHARDS = [(0, 3), (4, 6), (7, 10), (11, 22)]
VARIANTS = [
    ("and", (0, 1)),      # AND of two left vertices
    ("or", (0, 1)),       # OR of two left vertices
    ("and", (7, 8)),      # AND of two right vertices
    ("or", (7, 8)),       # OR of two right vertices
    ("and", (0, 8)),      # AND of a left and a right vertex, different index
    ("or", (0, 8)),       # OR of a left and a right vertex, different index
    ("or", (0, 7)),       # OR of the two vertices of one index (the ladder's z_i)
    ("or", (0, 0)),       # OR of one vertex with itself, left
    ("and", (0, 0)),
    ("or", (7, 7)),       # OR of one vertex with itself, right
    ("and", (7, 7)),
]


def pairs_of(i, j):
    return (1 << i) | (1 << (SIDE + j))


def required_pairs():
    return {pairs_of(i, j) for i in range(SIDE) for j in range(SIDE) if i != j}


def diagonal_pairs():
    return {pairs_of(i, i) for i in range(SIDE)}


def singletons():
    return {1 << i for i in range(N)}


def candidate_set():
    """14 singletons and the 84 pairs that are not diagonal.  A pair of two
    left vertices (or of two right vertices) never changes a promised value,
    and the ladder construction needs them, so they are candidates too; the
    diagonal pairs are excluded because a circuit holding {x_i, y_i} would be
    wrong on the input (u = v, i)."""
    out = set(singletons())
    for i in range(SIDE):
        for j in range(SIDE):
            if i != j:
                out.add(pairs_of(i, j))
    for i in range(SIDE):
        for j in range(i + 1, SIDE):
            out.add((1 << i) | (1 << j))          # two left vertices
            out.add((1 << (SIDE + i)) | (1 << (SIDE + j)))   # two right vertices
    return out


def check_crown(gates):
    """the circuit must be right on all 49 one-vertex-per-side inputs"""
    for u in range(SIDE):
        for v in range(SIDE):
            x = (1 << u) | (1 << (SIDE + v))
            bank = [(x >> i) & 1 for i in range(N)]
            for kind, ins in gates:
                va = bank[ins[0]] if ins[0] is not None else 0
                vb = bank[ins[1]] if ins[1] is not None else 0
                bank.append(int(va and vb) if kind == "and" else int(va or vb))
            got = bank[N + len(gates) - 1]
            want = 1 if u != v else 0
            if got != want:
                return False, f"wrong on the input (u={u}, v={v}): {got} != {want}"
    return True, "ok"


def main():
    global SIDE, N, K
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 3600
    outfile = sys.argv[2] if len(sys.argv) > 2 else os.path.join(OUTDIR, "crown_verdict.json")
    only = [int(a) for a in sys.argv[3].split(",")] if len(sys.argv) > 3 else None
    vsel = [int(a) for a in sys.argv[4].split(",")] if len(sys.argv) > 4 else None
    if len(sys.argv) > 5:
        SIDE = int(sys.argv[5]); N = 2 * SIDE
    if len(sys.argv) > 6:
        K = int(sys.argv[6])
    req = required_pairs()
    forb = diagonal_pairs() | singletons()
    cand = candidate_set()
    print(f"crown {SIDE}x{SIDE}: {len(req)} required pairs, {len(cand)} candidates",
          flush=True)
    verdict = {"required": len(req), "candidates": len(cand), "K": K,
               "shards": {}, "circuit": None, "sat": False}
    for si, (lo, hi) in enumerate(SHARDS):
        if only is not None and si not in only:
            continue
        key = f"{lo}-{hi}"
        t0 = time.time()
        print(f"--- shard {key}: at most {K} gates, {lo}..{hi} AND gates ---", flush=True)
        shard = {"lo": lo, "hi": hi, "status": "unknown", "variants": {}}
        for vi, vfirst in enumerate(VARIANTS):
            if vsel is not None and vi not in vsel:
                continue
            vname = vfirst[0]
            tag = f"{vname}:{vfirst[1][0]},{vfirst[1][1]}"
            # no_dead is without loss of generality: a circuit with a gate
            # nobody reads can be shortened, so in a minimum circuit every
            # gate reaches the output
            c, clist, op, selA, selB, X = encode(
                N, K, req, lo, hi, first_gate=vfirst, cand_set=cand,
                out_required=req, out_forbidden=forb, no_dead=True)
            path = os.path.join(OUTDIR, f"crown_k{K}_{lo}_{hi}_{vname}{vfirst[1][0]}{vfirst[1][1]}.cnf")
            nv, nc = c.dimacs(path)
            model, st = run_kissat(path, timeout)
            print(f"  variant {tag}: vars={nv} clauses={nc} -> {st} "
                  f"({time.time() - t0:.0f}s)", flush=True)
            shard["variants"][tag] = {"status": st, "vars": nv, "clauses": nc}
            if st == "SAT":
                gates = decode(model, N, K, clist, op, selA, selB)
                ok, why = check_crown(gates)
                if not ok:
                    print(f"  decoded circuit FAILED the check ({why}); ignoring", flush=True)
                    shard["variants"][tag]["check"] = "failed: " + str(why)
                    continue
                print(f"  FOUND a circuit with {K} gates:\n  {gates}", flush=True)
                shard["status"] = "SAT"
                verdict["sat"] = True
                verdict["circuit"] = {"gates": gates, "and_count":
                                      sum(1 for k, _ in gates if k == "and"),
                                      "shard": key}
                break
            if st == "UNSAT":
                shard["status"] = "UNSAT"
        if shard["status"] != "SAT":
            shard["status"] = "UNSAT" if all(
                v["status"] == "UNSAT" for v in shard["variants"].values()) else "unknown"
        verdict["shards"][key] = shard
        print(f"shard {key}: {shard['status']} ({time.time() - t0:.0f}s)", flush=True)
        with open(outfile, "w") as fh:
            json.dump(verdict, fh, indent=1)
        if shard["status"] == "SAT":
            break
    print("VERDICT:", "SAT" if verdict["sat"] else
          ("all shards UNSAT" if all(s["status"] == "UNSAT" for s in verdict["shards"].values())
           else "inconclusive"), flush=True)
    with open(outfile, "w") as fh:
        json.dump(verdict, fh, indent=1)


if __name__ == "__main__":
    main()
