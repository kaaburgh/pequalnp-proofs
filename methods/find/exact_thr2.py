#!/usr/bin/env python3
"""Exact SAT search for a small monotone circuit computing "at least 2 of n".

Same exact encoding as exact_crown.py (one boolean per promised row per
gate, one-hot selectors for the two operand wires, conditional equality
instead of a mux), but the rows are the full truth table of n variables and
the target is "at least two variables are true".

The fleet's 23-gate crown ladder is  n  ladder gates (z_i = x_i | y_i)  plus
a "two of n" circuit on the z_i;  if "two of seven" fits in 15 gates the
crown fits in 22 and the gap L-meta-18259 is answered.

Symmetry: the threshold function is invariant under S_n, so the first gate
(reading two input wires) has one orbit of operand pairs and two operations.
"""
import itertools
import json
import os
import subprocess
import sys

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
                if len(buf) >= 500000:
                    fh.writelines(buf)
                    buf = []
            fh.writelines(buf)
        return self.nv, len(self.clauses)


def at_most_one(lits, c):
    for a, b in itertools.combinations(lits, 2):
        c.add(-a, -b)


def encode(n, K, first=None):
    """rows: all 2^n assignments; target = (weight >= 2)."""
    c = CNF()
    nrows = 1 << n
    rows = []
    for r in range(nrows):
        rows.append([1 if (r >> i) & 1 else 0 for i in range(n)])

    sel, isand, val, aux = [], [], [], []
    for g in range(K):
        avail = list(range(n + g))
        s1 = [c.var() for _ in avail]
        s2 = [c.var() for _ in avail]
        c.add(*s1)
        c.add(*s2)
        at_most_one(s1, c)
        at_most_one(s2, c)
        ia = c.var()
        vals = [c.var() for _ in range(nrows)]
        auxs = [(c.var(), c.var()) for _ in range(nrows)]
        if g == 0 and first is not None:
            fa, fw1, fw2 = first
            c.add(ia if fa else -ia)
            for idx, w in enumerate(avail):
                c.add(s1[idx] if w == fw1 else -s1[idx])
                c.add(s2[idx] if w == fw2 else -s2[idx])
        for r in range(nrows):
            A, B = auxs[r]
            for idx, w in enumerate(avail):
                if w >= n:
                    lit = val[w - n][r]
                else:
                    lit = None if rows[r][w] else False
                for selvar, tgt in ((s1[idx], A), (s2[idx], B)):
                    if lit is None:
                        c.add(-selvar, tgt)
                    elif lit is False:
                        c.add(-selvar, -tgt)
                    else:
                        c.add(-selvar, -lit, tgt)
                        c.add(-selvar, lit, -tgt)
            v = vals[r]
            c.add(-ia, -A, -B, v)
            c.add(-ia, -v, A)
            c.add(-ia, -v, B)
            c.add(ia, -A, v)
            c.add(ia, -B, v)
            c.add(ia, -v, A, B)
        sel.append((s1, s2))
        isand.append(ia)
        val.append(vals)
        aux.append(auxs)

    for r in range(nrows):
        want = 1 if sum(rows[r]) >= 2 else 0
        if want:
            c.add(val[K - 1][r])
        else:
            c.add(-val[K - 1][r])
    return c, sel, isand, val, n


def run_kissat(path, timeout):
    try:
        p = subprocess.run([KISSAT, path], capture_output=True, text=True,
                           timeout=timeout)
        out = p.stdout
    except subprocess.TimeoutExpired as e:
        out = e.stdout if isinstance(e.stdout, str) else ""
        return "UNKNOWN", {}
    if "s SATISFIABLE" in out:
        model = {}
        for line in out.splitlines():
            if line.startswith("v "):
                for tok in line.split()[1:]:
                    t = int(tok)
                    if t > 0:
                        model[t] = 1
                    elif t < 0:
                        model[-t] = 0
        return "SAT", model
    if "s UNSATISFIABLE" in out:
        return "UNSAT", {}
    return "UNKNOWN", {}


def decode(model, sel, isand, n):
    gates = []
    for g in range(len(sel)):
        s1, s2 = sel[g]
        w1 = w2 = None
        for idx in range(len(s1)):
            if model.get(s1[idx], 0) == 1:
                w1 = idx
            if model.get(s2[idx], 0) == 1:
                w2 = idx
        gates.append(("and" if model.get(isand[g], 0) == 1 else "or", w1, w2))
    return gates


def verify(gates, n):
    for (op, w1, w2) in gates:
        if w1 is None or w2 is None or op not in ("and", "or"):
            return False, "bad gate"
    for r in range(1 << n):
        w = [1 if (r >> i) & 1 else 0 for i in range(n)]
        for (op, w1, w2) in gates:
            a, b = w[w1], w[w2]
            w.append(1 if (a and b) else 0 if op == "and" else 1 if (a or b) else 0)
        want = 1 if bin(r).count("1") >= 2 else 0
        if w[n + len(gates) - 1] != want:
            return False, f"row {r} wrong"
    return True, "ok"


def main():
    n = int(sys.argv[1])
    K = int(sys.argv[2])
    timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 3600
    outjson = sys.argv[4] if len(sys.argv) > 4 else None
    only = int(sys.argv[5]) if len(sys.argv) > 5 and sys.argv[5] != "" else None
    variants = [(0, 0, 1), (1, 0, 1)]
    cnf_path = os.path.join(OUTDIR, f"thr2_{n}_k{K}.cnf")
    results = []
    for vi, v in enumerate(variants):
        if only is not None and vi != only:
            continue
        c, sel, isand, val, ninp = encode(n, K, first=v)
        nv, nc = c.dimacs(cnf_path)
        print(f"variant {vi} {v}: vars={nv} clauses={nc}", flush=True)
        status, model = run_kissat(cnf_path, timeout)
        print(f"  -> {status} ({timeout}s)", flush=True)
        rec = {"variant": vi, "first": v, "status": status, "vars": nv, "clauses": nc}
        if status == "SAT":
            gates = decode(model, sel, isand, n)
            ok, why = verify(gates, n)
            rec.update({"verified": ok, "why": why, "gates": gates})
            print(f"  gates={gates}", flush=True)
            print(f"  verified={ok} ({why})", flush=True)
        results.append(rec)
        if status == "SAT" and rec.get("verified"):
            break
        if outjson:
            with open(outjson, "w") as fh:
                json.dump(results, fh, indent=1)
    if outjson:
        with open(outjson, "w") as fh:
            json.dump(results, fh, indent=1)
    print("VERDICT:", results)


if __name__ == "__main__":
    main()
