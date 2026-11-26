#!/usr/bin/env python3
"""Exact search for a monotone AND/OR circuit with at most 13 gates computing
perfect matching in the 3 x 3 bipartite graph.

The desk's range rule for L-meta-17390 splits the search by the number of AND
gates:

    shard 0: at most 13 gates, no NOT gate, 0 to 3 AND gates
    shard 1: at most 13 gates, no NOT gate, 4 to 6 AND gates
    shard 2: at most 13 gates, no NOT gate, 7 to 9 AND gates
    shard 3: at most 13 gates, no NOT gate, 10 to 13 AND gates

so this program runs one exact search per shard.  A shard is decided when
kissat answers UNSAT (no circuit in that range exists) or SAT (here is one).
"Exactly 13 gates" and "at most 13 gates" agree because a shorter circuit can
be padded to 13 gates by inserting OR(x_i, x_i) gates, which do not change the
number of AND gates.

Usage:  python3 search_pm33.py [timeout_per_shard] [out.json]
"""
import json
import sys
import time

from mono_sat import (candidate_monomials, check_circuit, decode, encode,
                      run_kissat, mono_sets)

N = 9
PERMS = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
SHARDS = [(0, 3), (4, 6), (7, 9), (10, 13)]
K = 13
# the four symmetry-broken variants: the first gate of a circuit reads only
# input wires, so its monomial set is a singleton or a pair, and both are one
# orbit of the row/column permutation group of the 3x3 grid
# The first gate of a circuit reads input wires only.  Its monomial set is
# either a singleton (both reads are the same wire) or the pair of singletons
# it reads (for OR), or the pair monomial it multiplies (for AND).  Under the
# row/column permutation group of the 3x3 grid the two-wire reads fall into
# three orbits -- same row, same column, different row and column -- and the
# singleton reads into one, so four (OR) plus two (AND) variants cover every
# circuit.  An AND of two variables of the same row or column is impossible:
# that pair lies in no perfect matching, so it could never reach the output.
VARIANTS = [("and", (0, 4)),    # AND of two variables, different row and column
            ("or", (0, 4)),     # OR of two variables, different row and column
            ("or", (0, 1)),     # OR of two variables of the same row
            ("or", (0, 3)),     # OR of two variables of the same column
            ("or", (0, 0)),     # OR of one variable with itself
            ("and", (0, 0))]    # AND of one variable with itself


def targets():
    out = set()
    for p in PERMS:
        m = 0
        for i, c in enumerate(p):
            m |= 1 << (3 * i + c)
        out.add(m)
    return out


def is_pm(x):
    for p in PERMS:
        if all((x >> (3 * i + p[i])) & 1 for i in range(3)):
            return 1
    return 0


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 3600
    outfile = sys.argv[2] if len(sys.argv) > 2 else os.path.join(OUTDIR, "pm33_verdict.json")
    only = [int(a) for a in sys.argv[3].split(",")] if len(sys.argv) > 3 else None
    vsel = [int(a) for a in sys.argv[4].split(",")] if len(sys.argv) > 4 else None
    tgt = targets()
    cand = candidate_monomials(tgt, N)
    print(f"target: {len(tgt)} perfect matchings, {len(cand)} candidate monomials",
          flush=True)
    verdict = {"target": sorted(tgt), "candidates": len(cand), "K": K,
               "shards": {}, "circuit": None, "sat": False}
    for si, (lo, hi) in enumerate(SHARDS):
        if only is not None and si not in only:
            continue
        key = f"{lo}-{hi}"
        t0 = time.time()
        print(f"--- shard {key}: at most {K} gates, {lo}..{hi} AND gates ---",
              flush=True)
        shard = {"lo": lo, "hi": hi, "status": "unknown", "variants": {}}
        for vi, vfirst in enumerate(VARIANTS):
            if vsel is not None and vi not in vsel:
                continue
            vname = vfirst[0]
            tag = f"{vname}:{vfirst[1][0]},{vfirst[1][1]}"
            # out_is_or and no_dead are without loss of generality: the output
            # has to carry all six matchings and an AND gate holds at most
            # two of them, so the output gate is an OR; and a circuit with a
            # gate nobody reads can be shortened, so in a minimum circuit every
            # gate reaches the output
            c, clist, op, selA, selB, X = encode(N, K, tgt, lo, hi, first_gate=vfirst,
                                               out_is_or=True, no_dead=True)
            path = os.path.join(OUTDIR, f"pm33_k{K}_{lo}_{hi}_{vname}{vfirst[0]}{vfirst[1]}.cnf")
            nv, nc = c.dimacs(path)
            model, st = run_kissat(path, timeout)
            print(f"  variant {tag}: vars={nv} clauses={nc} -> {st} "
                  f"({time.time() - t0:.0f}s)", flush=True)
            shard["variants"][tag] = {"status": st, "vars": nv, "clauses": nc,
                                      "cnf": path}
            if st == "SAT":
                gates = decode(model, N, K, clist, op, selA, selB)
                ok, why = check_circuit(gates, N, tgt)
                if not ok:
                    print(f"  decoded circuit FAILED the check ({why}); ignoring",
                          flush=True)
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
        if not shard["status"] in ("SAT",):
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
