#!/usr/bin/env python3
"""Exact circuit search (SAT) for promise-style functions.

build_cnf(n, K, target, rows, types):
  n       : number of inputs
  K       : number of gates (the last one is the output)
  target  : list of booleans indexed by assignment mask (2^n entries) -- only the
            entries at `rows` are used
  rows    : list of assignment masks on which the output must equal the target
  types   : set of allowed gate ops ("and", "or", "not")

Only the values on the checked rows are encoded, so promise instances stay small.
"""
import subprocess

KISSAT = "/workspace/pnp/kissat"
OPS = {"and": 0, "or": 1, "not": 2}


def build_cnf(n, K, target, rows, types=("and", "or", "not")):
    clauses = []
    nv = 0

    def newvar():
        nonlocal nv
        nv += 1
        return nv

    tid = {t: [] for t in types}
    selA, selB = [], []
    V, A, B = [], [], []
    for g in range(K):
        for t in types:
            tid[t].append(newvar())
        sa, sb = [], []
        for w in range(n + g):
            sa.append(newvar()); sb.append(newvar())
        selA.append(sa); selB.append(sb)
        V.append([newvar() for _ in rows])
        A.append([newvar() for _ in rows])
        B.append([newvar() for _ in rows])

    def exactly_one(lits):
        clauses.append(list(lits))
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                clauses.append([-lits[i], -lits[j]])

    for g in range(K):
        exactly_one([tid[t][g] for t in types])
        exactly_one(selA[g])
        exactly_one(selB[g])

    def wire_val_lit(w, ri):
        if w < n:
            x = rows[ri]
            return None if (x >> w) & 1 else False
        return V[w - n][ri]

    def mux(g, ri, sel, aux):
        sels = sel[g]
        true_sel, false_sel = [], []
        for wi, w in enumerate(range(n + g)):
            lit = wire_val_lit(w, ri)
            if lit is None:
                clauses.append([-sels[wi], aux]); true_sel.append(sels[wi])
            elif lit is False:
                clauses.append([-sels[wi], -aux]); false_sel.append(sels[wi])
            else:
                clauses.append([-sels[wi], -aux, lit])
                clauses.append([-sels[wi], aux, -lit])
                true_sel.append(sels[wi]); false_sel.append(sels[wi])
        clauses.append([-aux] + true_sel)
        clauses.append([aux] + false_sel)

    for g in range(K):
        for ri in range(len(rows)):
            mux(g, ri, selA, A[g][ri])
            mux(g, ri, selB, B[g][ri])
            a, b, v = A[g][ri], B[g][ri], V[g][ri]
            if "and" in types:
                clauses.append([-tid["and"][g], -a, -b, v])
                clauses.append([-tid["and"][g], a, -v])
                clauses.append([-tid["and"][g], b, -v])
            if "or" in types:
                clauses.append([-tid["or"][g], -a, v])
                clauses.append([-tid["or"][g], -b, v])
                clauses.append([-tid["or"][g], a, b, -v])
            if "not" in types:
                clauses.append([-tid["not"][g], a, v])
                clauses.append([-tid["not"][g], -a, -v])
    out = V[K - 1]
    for ri, x in enumerate(rows):
        clauses.append([out[ri]] if target[x] else [-out[ri]])
    return clauses, nv, dict(tid=tid, selA=selA, selB=selB, V=V)


def write_dimacs(clauses, nv, path):
    with open(path, "w") as fh:
        fh.write(f"p cnf {nv} {len(clauses)}\n")
        buf = []
        for c in clauses:
            buf.append(" ".join(map(str, c)) + " 0\n")
            if len(buf) >= 200000:
                fh.writelines(buf); buf = []
        fh.writelines(buf)


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


def decode(model, n, K, info, types):
    gates = []
    for g in range(K):
        op = None
        for t in types:
            if model.get(info["tid"][t][g]):
                op = t
        a = next((w for w, v in enumerate(info["selA"][g]) if model.get(v)), None)
        b = next((w for w, v in enumerate(info["selB"][g]) if model.get(v)), None)
        ins = [a] if op == "not" else sorted([a, b])
        gates.append((op, ins))
    return gates


def evaluate(gates, n, x):
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


def verify(gates, n, target, rows):
    for x in rows:
        if evaluate(gates, n, x) != (1 if target[x] else 0):
            return False, x
    return True, None


def at_least_two_of_seven():
    n = 7
    target = [0] * 128
    for x in range(128):
        target[x] = 1 if bin(x).count("1") >= 2 else 0
    return n, target, list(range(128))


def crown(n_side=7):
    n = 2 * n_side
    target = [0] * (1 << n)
    rows = []
    for u in range(n_side):
        for v in range(n_side):
            x = (1 << u) | (1 << (n_side + v))
            rows.append(x)
            target[x] = 1 if u != v else 0
    return n, target, rows


def rect35(mask=3581, nl=3, nr=5):
    n = nl + nr
    target = [0] * (1 << n)
    rows = []
    for u in range(nl):
        for v in range(nr):
            x = (1 << u) | (1 << (nl + v))
            rows.append(x)
            target[x] = 1 if (mask >> (nr * u + v)) & 1 else 0
    return n, target, rows


def pm33_rows():
    """perfect matching in a 3 by 3 bipartite graph: all 512 assignments."""
    n = 9
    target = [0] * 512
    perms = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
    for x in range(512):
        for p in perms:
            if all((x >> (3 * i + p[i])) & 1 for i in range(3)):
                target[x] = 1
                break
    return n, target, list(range(512))


def main():
    import sys, json
    which = sys.argv[1]
    K = int(sys.argv[2])
    timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 1800
    types = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ("and", "or")
    if which == "t2_7":
        n, target, rows = at_least_two_of_seven()
        name = "t2_7"
    elif which.startswith("rect"):
        parts = which[4:].split("_")
        nl = int(parts[0]); nr = int(parts[1]); mask = int(parts[2])
        n, target, rows = rect35(mask, nl, nr)
        name = which
    elif which.startswith("crown"):
        side = int(which[5:] or 7)
        n, target, rows = crown(side)
        name = which
    else:
        raise SystemExit("unknown target")
    clauses, nv, info = build_cnf(n, K, target, rows, types)
    path = f"/workspace/output/{name}_k{K}.cnf"
    write_dimacs(clauses, nv, path)
    print(f"{name} K={K} types={types}: vars={nv} clauses={len(clauses)} rows={len(rows)}", flush=True)
    model, status = run_kissat(path, timeout)
    print("kissat:", status, flush=True)
    if model is None:
        return
    gates = decode(model, n, K, info, types)
    ok, bad = verify(gates, n, target, rows)
    print("verified on all rows:", ok, flush=True)
    if not ok:
        print("FAILED at", bad, flush=True)
        return
    print("gates:", gates, flush=True)
    json.dump({"n": n, "gates": gates, "output": n + K - 1, "name": name},
              open(f"/workspace/output/{name}_k{K}.json", "w"))
    print("saved", flush=True)


if __name__ == "__main__":
    main()
