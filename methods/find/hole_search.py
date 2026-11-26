#!/usr/bin/env python3
"""One-hole search: take a known circuit, drop one gate, and let the SAT solver
rebuild that gate (type and operands) so that the whole circuit still computes the
target on the checked rows.

The wire numbering keeps the hole: gate i < h writes wire n+i, gate i > h writes
wire n+i+1.
"""
import subprocess
import sys
import json

KISSAT = "/workspace/pnp/kissat"


def remap(w, h, n):
    """a wire of the new circuit -> the wire of the template (or None if it is the hole)"""
    if w < n:
        return w
    gi = w - n                      # index of the gate in the new circuit
    j = gi if gi < h else gi - 1    # index of the gate in the template
    if j == h:
        return None                 # the hole cannot be read
    return n + j


def build_cnf_hole(n, K, target, rows, types, template, h):
    """template: list of (op, inputs) of length K+1; index h is dropped."""
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
        for w in range(n + g + (1 if g >= h else 0)):
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
        idx = w - n
        return V[idx][ri]

    def mux(g, ri, sel, aux):
        sels = sel[g]
        true_sel, false_sel = [], []
        for wi, w in enumerate(range(n + g + (1 if g >= h else 0))):
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

    # fix all the gates but the hole
    for g in range(K):
        ti = g if g < h else g + 1
        op, ins = template[ti]
        for t in types:
            if t == op:
                clauses.append([tid[t][g]])
            else:
                clauses.append([-tid[t][g]])
        for wi in range(n + g + (1 if g >= h else 0)):
            ref = remap(wi, h, n)
            want = ref is not None and ref in ins
            if want:
                clauses.append([selA[g][wi]])
                clauses.append([selB[g][wi]])
            else:
                clauses.append([-selA[g][wi]])
                clauses.append([-selB[g][wi]])

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


def run_kissat(path, timeout=600):
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


def decode_hole(model, n, K, info, types, h):
    """rebuild the gate list of the new circuit (K gates)."""
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


def verify(gates, n, target, rows):
    for x in rows:
        if eval_circuit(gates, n, x) != (1 if target[x] else 0):
            return False, x
    return True, None


def hole_search(n, target, rows, template, types=("and", "or"), timeout=600, log=print):
    """template has K+1 gates; look for a K-gate circuit by dropping each gate."""
    K = len(template) - 1
    for h in range(len(template)):
        clauses, nv, info = build_cnf_hole(n, K, target, rows, types, template, h)
        path = f"/workspace/output/hole_{h}.cnf"
        write_dimacs(clauses, nv, path)
        model, status = run_kissat(path, timeout)
        log(f"  hole {h}: {status}")
        if model is None:
            continue
        gates = decode_hole(model, n, K, info, types, h)
        ok, bad = verify(gates, n, target, rows)
        log(f"    verified={ok}")
        if ok:
            return gates
    return None


def main():
    import sat_search as S
    import optimize_circuit as O
    which = sys.argv[1]
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    if which == "rect3_5":
        n, target, rows = S.rect35(3581, 3, 5)
        template = [("or", [5, 6]), ("or", [7, 8]), ("and", [2, 4]), ("or", [4, 8]),
                    ("and", [0, 9]), ("or", [1, 10]), ("or", [3, 12]), ("and", [11, 13]),
                    ("or", [14, 15])]
    elif which == "crown7":
        n, target, rows = S.crown(7)
        template = O.crown23(n)
    elif which == "t2_7":
        n, target, rows = S.at_least_two_of_seven()
        template = O.t2_7_sixteen(n)
    elif which == "pm33":
        n, target, rows = S.pm33_rows()
        template = pm33_fourteen()
    else:
        raise SystemExit("unknown target")
    print(f"{which}: template {len(template)} gates, n={n}, rows={len(rows)}", flush=True)
    print("template wrong rows:", sum(
        1 for x in rows if eval_circuit(template, n, x) != (1 if target[x] else 0)), flush=True)
    gates = hole_search(n, target, rows, template, timeout=timeout)
    if gates:
        print("FOUND", len(gates), "gates:", gates, flush=True)
        json.dump({"n": n, "gates": gates, "output": n + len(gates) - 1, "name": which},
                  open(f"/workspace/output/{which}_hole.json", "w"))
    else:
        print("no smaller circuit found by one-hole search", flush=True)


def pm33_fourteen():
    """the 14-gate circuit for the perfect matching in a 3 by 3 bipartite graph."""
    return [("and", [4, 8]), ("and", [5, 7]), ("or", [9, 10]),
            ("and", [3, 8]), ("and", [5, 6]), ("or", [12, 13]),
            ("and", [3, 7]), ("and", [4, 6]), ("or", [15, 16]),
            ("and", [0, 11]), ("and", [1, 14]), ("and", [2, 17]),
            ("or", [18, 19]), ("or", [21, 20])]


if __name__ == "__main__":
    main()
