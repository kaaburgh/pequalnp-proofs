#!/usr/bin/env python3
"""Two-hole (and k-hole) search: drop k gates of a known circuit and let the SAT
solver rebuild all of them, so that the circuit still computes the target on the
checked rows.

New position g of the shorter circuit holds the template gate ti(g), where the
template indices of the dropped gates are replaced by free gates in place.  A
wire of the new circuit is matched back to the template wire it stands for, so a
fixed gate keeps exactly the operands it had.
"""
import subprocess
import sys
import json

KISSAT = "/workspace/pnp/kissat"


def positions_of(template, holes):
    """for every position of the new circuit: ('fixed', template index) or ('free',)"""
    hs = set(holes)
    pos = []
    for ti in range(len(template)):
        if ti in hs:
            pos.append(("free", ti))
        else:
            pos.append(("fixed", ti))
    return pos


def build_cnf_kholes(n, K, target, rows, types, template, holes):
    pos = positions_of(template, holes)
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

    # the template wire that a new wire stands for
    def to_template(w):
        if w < n:
            return w
        g = w - n
        kind, ti = pos[g]
        return n + ti

    # fix the gates that are not free
    for g in range(K):
        kind, ti = pos[g]
        if kind == "free":
            continue
        op, ins = template[ti]
        for t in types:
            clauses.append([tid[t][g]] if t == op else [-tid[t][g]])
        for wi in range(n + g):
            ref = to_template(wi)
            if ref in ins:
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


def main():
    import itertools
    which = sys.argv[1]
    nholes = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    import sat_search as S
    import optimize_circuit as O
    if which == "pm33":
        n, target, rows = S.pm33_rows()
        template = [("and", [4, 8]), ("and", [5, 7]), ("or", [9, 10]),
                    ("and", [3, 8]), ("and", [5, 6]), ("or", [12, 13]),
                    ("and", [3, 7]), ("and", [4, 6]), ("or", [15, 16]),
                    ("and", [0, 11]), ("and", [1, 14]), ("and", [2, 17]),
                    ("or", [18, 19]), ("or", [21, 20])]
        types = ("and", "or", "not")
    elif which == "hc5":
        import search_5cycle_range as R
        n = 10
        rows = list(range(1024))
        target, _ = R.five_cycle_target()
        template = [("and", (2, 8)), ("and", (3, 7)), ("or", (10, 11)), ("and", (0, 4)),
                    ("and", (13, 9)), ("and", (5, 6)), ("and", (15, 1)), ("or", (14, 16)),
                    ("and", (17, 12)), ("and", (1, 9)), ("or", (19, 11)), ("and", (0, 5)),
                    ("and", (21, 8)), ("and", (4, 6)), ("and", (23, 2)), ("or", (22, 24)),
                    ("and", (25, 20)), ("or", (10, 19)), ("and", (0, 6)), ("and", (28, 7)),
                    ("and", (4, 5)), ("and", (30, 3)), ("or", (29, 31)), ("and", (32, 27)),
                    ("or", (18, 26)), ("or", (34, 33))]
        types = ("and", "or", "not")
    elif which == "crown7":
        n, target, rows = S.crown(7)
        template = O.crown23(n)
        types = ("and", "or")
    elif which == "rect3_5":
        n, target, rows = S.rect35(3581, 3, 5)
        template = [("or", [5, 6]), ("or", [7, 8]), ("and", [2, 4]), ("or", [4, 8]),
                    ("and", [0, 9]), ("or", [1, 10]), ("or", [3, 12]), ("and", [11, 13]),
                    ("or", [14, 15])]
        types = ("and", "or")
    else:
        raise SystemExit("unknown")
    L = len(template)
    K = L - nholes
    print(f"{which}: template {L} gates, search for {K} gates, types {types}", flush=True)
    for holes in itertools.combinations(range(L), nholes):
        clauses, nv, info = build_cnf_kholes(n, K, target, rows, types, template, holes)
        path = f"/workspace/output/kh_{'_'.join(map(str, holes))}.cnf"
        write_dimacs(clauses, nv, path)
        model, status = run_kissat(path, timeout)
        if model is None:
            continue
        gates = decode(model, n, K, info, types)
        ok, bad = verify(gates, n, target, rows)
        if ok:
            print(f"FOUND holes={holes}: {gates}", flush=True)
            json.dump({"n": n, "gates": gates, "output": n + K - 1, "name": which},
                      open(f"/workspace/output/{which}_kh{nholes}.json", "w"))
            return
    print("no solution found", flush=True)


if __name__ == "__main__":
    main()
