#!/usr/bin/env python3
"""PM 3x3 monotone circuit search (self-contained: encoder + driver).

This file is the program that was released with the lease for L-meta-17390.
It decides, exactly, whether a monotone AND/OR circuit with at most 13 gates
computes perfect matching in the 3x3 bipartite graph, split the way the desk
splits it: by the number of AND gates (0-3, 4-6, 7-9, 10-13).

    python3 pm33_search.py [timeout_per_instance] [verdict.json] [shards] [variants]

Part 1 is the monomial-set SAT encoder (exact for monotone circuits).
Part 2 is the shard driver.
"""

import itertools
import os
import subprocess

KISSAT = os.environ.get("KISSAT", "kissat")
OUTDIR = os.environ.get("PNP_OUT", ".")


class CNF:
    def __init__(self):
        self.clauses = []
        self.nv = 0

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, *lits):
        self.clauses.append(list(lits))

    def dimacs(self, path):
        with open(path, "w") as fh:
            fh.write(f"p cnf {self.nv} {len(self.clauses)}\n")
            buf = []
            for cl in self.clauses:
                buf.append(" ".join(map(str, cl)) + " 0\n")
                if len(buf) >= 200000:
                    fh.writelines(buf)
                    buf = []
            fh.writelines(buf)
        return self.nv, len(self.clauses)


def all_subsets(mon, n):
    """all non-empty subsets of the monomial `mon` (bitmask over n variables)"""
    vs = [v for v in range(n) if (mon >> v) & 1]
    out = []
    for r in range(1, len(vs) + 1):
        for comb in itertools.combinations(vs, r):
            m = 0
            for v in comb:
                m |= 1 << v
            out.append(m)
    return out


def candidate_monomials(targets, n):
    cand = set()
    for t in targets:
        cand.update(all_subsets(t, n))
    return sorted(cand)


def atmost(lits, k, c):
    """sequential-counter encoding of 'at most k of lits are true'."""
    n = len(lits)
    if k >= n:
        return
    if k < 0:
        c.add(*lits)
        return
    s = [[c.var() for _ in range(k + 1)] for _ in range(n)]
    for i in range(n):
        c.add(-lits[i], s[i][0])
        if i > 0:
            for j in range(1, k + 1):
                c.add(-s[i - 1][j], s[i][j])
                c.add(-lits[i], -s[i - 1][j - 1], s[i][j])
    c.add(-s[n - 1][k])


def card_range(lits, lo, hi, c):
    """'lo <= number of true lits <= hi'."""
    n = len(lits)
    hi = min(hi, n)
    atmost(lits, hi, c)
    if lo > 0:
        atmost([-l for l in lits], n - lo, c)


def encode(n, K, targets, lo, hi, first_gate=None, out_required=None,
           out_forbidden=None, cand_set=None, complete=False,
           out_is_or=False, no_dead=False):
    """CNF for 'there is a monotone AND/OR circuit with exactly K gates whose
    output monomial set is exactly `targets`, with between lo and hi AND gates'.

    first_gate: optional ("and"|"or", (i, j)) fixing gate 0 to read input wires
    i and j with that operation (symmetry breaking).
    """
    if complete:
        # track every monomial of size at most three; monomials of size four
        # or more are invisible to the encoding, but they cannot change the
        # value of a minimal term, so the tracked part stays exact
        cand = []
        for v in range(n):
            cand.append(1 << v)
        for v in range(n):
            for w in range(v + 1, n):
                cand.append((1 << v) | (1 << w))
        for v in range(n):
            for w in range(v + 1, n):
                for u in range(w + 1, n):
                    cand.append((1 << v) | (1 << w) | (1 << u))
        cand = sorted(set(cand))
    elif cand_set is None:
        cand = candidate_monomials(targets, n)
    else:
        cand = sorted(cand_set)
    cidx = {m: i for i, m in enumerate(cand)}
    cand_set = set(cand)
    pairs_for = {}
    for m in cand:
        lst = []
        for s1 in cand:
            for s2 in cand:
                if (s1 | s2) == m:
                    lst.append((cidx[s1], cidx[s2]))
        pairs_for[cidx[m]] = lst
    # pairs whose product leaves the candidate set: a minimal circuit cannot
    # contain them, so they are forbidden at every AND gate (in the complete
    # mode nothing is forbidden: products of size four or more are simply
    # invisible)
    escape = [] if complete else [
        (cidx[s1], cidx[s2]) for s1 in cand for s2 in cand
        if (s1 | s2) not in cand_set]

    c = CNF()
    op = [c.var() for _ in range(K)]          # true = AND, false = OR
    X = [[c.var() for _ in cand] for _ in range(K)]
    selA, selB = [], []
    for g in range(K):
        wires = n + g
        sa = [c.var() for _ in range(wires)]
        sb = [c.var() for _ in range(wires)]
        selA.append(sa)
        selB.append(sb)
        c.add(*sa)
        c.add(*sb)
        for i in range(len(sa)):
            for j in range(i + 1, len(sa)):
                c.add(-sa[i], -sa[j])
            for j in range(i + 1, len(sb)):
                c.add(-sb[i], -sb[j])

    # monomial sets of the selected input wires: aLit[g][i] / bLit[g][i]
    aLit = [[None] * len(cand) for _ in range(K)]
    bLit = [[None] * len(cand) for _ in range(K)]
    for g in range(K):
        wires = n + g
        for i in range(len(cand)):
            a = c.var()
            b = c.var()
            aLit[g][i] = a
            bLit[g][i] = b
            for w in range(wires):
                if w < n:
                    truth = (cand[i] == (1 << w))
                    c.add(-selA[g][w], a if truth else -a)
                    c.add(-selB[g][w], b if truth else -b)
                else:
                    x = X[w - n][i]
                    c.add(-selA[g][w], -a, x)
                    c.add(-selA[g][w], a, -x)
                    c.add(-selB[g][w], -b, x)
                    c.add(-selB[g][w], b, -x)

    # gate semantics, conditional on the operation
    for g in range(K):
        for i in range(len(cand)):
            lits = []
            for (j1, j2) in pairs_for[i]:
                z = c.var()
                c.add(-z, aLit[g][j1])
                c.add(-z, bLit[g][j2])
                c.add(z, -aLit[g][j1], -bLit[g][j2])
                lits.append(z)
            # AND branch: op[g] -> X[g][i] <-> OR of the pair literals
            c.add(-op[g], -X[g][i], *lits)
            for z in lits:
                c.add(-op[g], X[g][i], -z)
            # OR branch: not op[g] -> X[g][i] <-> aLit[i] | bLit[i]
            c.add(op[g], -X[g][i], aLit[g][i], bLit[g][i])
            c.add(op[g], X[g][i], -aLit[g][i])
            c.add(op[g], X[g][i], -bLit[g][i])
        # an AND gate may not multiply two monomials whose product leaves the
        # candidate set (such a monomial would reach the output and could not
        # be a minimal term of the target)
        for (j1, j2) in escape:
            c.add(-op[g], -aLit[g][j1], -bLit[g][j2])

    # the output gate (the last one) carries exactly the target monomials
    out = K - 1
    req = set(targets) if out_required is None else set(out_required)
    forb = set() if out_forbidden is None else set(out_forbidden)
    for i, m in enumerate(cand):
        if m in req:
            c.add(X[out][i])
        elif m in forb:
            c.add(-X[out][i])
        elif out_required is None and out_forbidden is None:
            c.add(-X[out][i])

    card_range(op, lo, hi, c)

    if out_is_or:
        # the output gate carries all the target monomials; an AND gate can
        # hold at most two of them (a pair P inside a matching fixes the third
        # edge, and an edge lies in at most two perfect matchings), so the
        # output is an OR
        c.add(-op[K - 1])

    if no_dead:
        # every gate but the last one is read by a later gate: in a minimal
        # circuit every gate reaches the output, so this loses nothing and it
        # forbids gates that nobody reads
        for g in range(K - 1):
            lits = []
            for g2 in range(g + 1, K):
                lits.append(selA[g2][n + g])
                lits.append(selB[g2][n + g])
            c.add(*lits)

    if first_gate is not None:
        kind, (i, j) = first_gate
        if kind == "and":
            c.add(op[0])
        else:
            c.add(-op[0])
        c.add(selA[0][i])
        c.add(selB[0][j])
    return c, cand, op, selA, selB, X


def run_kissat(path, timeout=3600):
    try:
        p = subprocess.run([KISSAT, path], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, "timeout"
    out = p.stdout
    if "s SATISFIABLE" in out:
        model = {}
        for line in out.splitlines():
            if line.startswith("v "):
                for tok in line[2:].split():
                    v = int(tok)
                    if v:
                        model[abs(v)] = v > 0
        return model, "SAT"
    if "s UNSATISFIABLE" in out:
        return None, "UNSAT"
    return None, "unknown"


def decode(model, n, K, cand, op, selA, selB):
    gates = []
    for g in range(K):
        kind = "and" if model.get(op[g]) else "or"
        a = next((w for w in range(n + g) if model.get(selA[g][w])), None)
        b = next((w for w in range(n + g) if model.get(selB[g][w])), None)
        gates.append((kind, [a, b]))
    return gates


def evaluate(gates, n, x):
    bank = [(x >> i) & 1 for i in range(n)]
    for kind, ins in gates:
        va = bank[ins[0]] if ins[0] is not None else 0
        vb = bank[ins[1]] if ins[1] is not None else 0
        bank.append(int(va and vb) if kind == "and" else int(va or vb))
    return bank[n + len(gates) - 1]


def mono_sets(gates, n):
    """monomial set of every wire"""
    sets = [{1 << i} for i in range(n)]
    for kind, ins in gates:
        s1 = sets[ins[0]] if ins[0] is not None else set()
        s2 = sets[ins[1]] if ins[1] is not None else set()
        if kind == "and":
            sets.append({a | b for a in s1 for b in s2})
        else:
            sets.append(set(s1) | set(s2))
    return sets


def check_circuit(gates, n, targets):
    """A decoded circuit is accepted only if it is right on every input and
    stays inside the candidate set everywhere (a circuit that leaves the
    candidate set computes something else than the target)."""
    sets = mono_sets(gates, n)
    cand = set(candidate_monomials(targets, n))
    for w, s in enumerate(sets):
        if not s <= cand:
            return False, f"wire {w} has monomials outside the candidate set: {sorted(s)}"
    if sets[n + len(gates) - 1] != set(targets):
        return False, "the output monomial set is not the target"
    for x in range(1 << n):
        want = 0
        for m in targets:
            if all((x >> v) & 1 for v in range(n) if (m >> v) & 1):
                want = 1
                break
        if evaluate(gates, n, x) != want:
            return False, f"wrong value on input {x}"
    return True, "ok"



import json
import sys
import time


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
