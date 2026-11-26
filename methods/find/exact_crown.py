#!/usr/bin/env python3
"""Exact SAT search for a small monotone circuit computing the crown graph.

Target
------
The n x n crown K_{n,n} minus the perfect matching, in the "promised input"
form used by the desk:  the 14 (or 2n) input wires carry  u_0..u_{n-1}  on the
left and  v_0..v_{n-1}  on the right, and the circuit is judged only on the
2n^2 inputs that have exactly one left vertex and one right vertex set.
Row (i,j) means  u_i = 1  and  v_j = 1;  the target value is  [i != j].

Encoding (exact)
-----------------
A circuit with K gates is a list of gates; gate g reads two earlier wires and
is AND or OR; the output is the last gate.  For every gate we keep one
Boolean per promise row ("the wire is 1 on this row") plus a one-hot selector
for each of the two operand wires.  The value of a wire on a row is a
*constant* for input wires and a variable for gate wires, so the conditional
equality "if wire w is selected then the operand has the value of w on row r"
costs two clauses and needs no auxiliary variables.  Semantics per (gate,row):
AND -> A and B, OR -> A or B.

Size: about 4*W clauses per (gate,row) plus 6, i.e. ~160k clauses and ~5k
variables for n = 7, K = 22 - roughly 40x smaller than the monomial-set
encoding it replaces, and exact (no restriction on the size of intermediate
monomials).

Symmetry
--------
The automorphism group of the promised problem is (S_n x S_n restricted to the
same permutation on both sides) together with the left/right swap.  The first
gate of any circuit reads two input wires, and the orbits of such pairs are
{left-left or right-right}, {u_i,v_i}, {u_i,v_j} with i != j}; each with two
possible ops.  Fixing the first gate to a representative of each orbit covers
every circuit, so the variants below are exhaustive.
"""
import itertools
import json
import os
import subprocess
import sys

KISSAT = "/workspace/pnp/kissat"
OUT_OR = False


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


def at_least_k(lits, k, c):
    """sum(lits) >= k  (sequential counter)."""
    n = len(lits)
    if k <= 0:
        return
    if k > n:
        c.add(*lits)  # unsatisfiable marker; caller handles
        c.add(-lits[0])
        return
    # s[i][j] = "at least j+1 of lits[0..i]"
    s = [[c.var() for _ in range(k)] for _ in range(n)]
    c.add(-lits[0], s[0][0])
    for j in range(1, k):
        c.add(-s[0][j])
    for i in range(1, n):
        c.add(-lits[i], s[i][0])
        c.add(-s[i - 1][0], s[i][0])
        for j in range(1, k):
            c.add(-s[i - 1][j], s[i][j])
            c.add(-lits[i], -s[i - 1][j - 1], s[i][j])
    c.add(*[s[n - 1][j] for j in range(k)])


def encode(n, K, and_lo=None, and_hi=None, first=None, out_is_or=False):
    """first = (is_and, w1, w2) fixing gate 1's op and operand wires."""
    c = CNF()
    ninp = 2 * n
    nrows = n * n

    def row_input_value(w, r, vals):
        """Value of wire w on row r: None = constant 1, False = constant 0,
        otherwise the variable holding the gate wire's value."""
        i, j = divmod(r, n)
        if w < n:                      # left wire u_w
            return None if w == i else False
        if w < 2 * n:                  # right wire v_{w-n}
            return None if (w - n) == j else False
        return vals[w - 2 * n][r]      # gate wire (already built)

    sel = []      # sel[g] = (sel1 list, sel2 list)
    isand = []
    val = []      # val[g][r]
    aux = []      # aux[g][r] = (A, B)

    for g in range(K):
        avail = list(range(ninp + g))
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
            c.add(ia if fa else -ia)          # force op (fa=1 -> AND)
            for idx, w in enumerate(avail):
                if w == fw1:
                    c.add(s1[idx])
                else:
                    c.add(-s1[idx])
                if w == fw2:
                    c.add(s2[idx])
                else:
                    c.add(-s2[idx])

        for r in range(nrows):
            A, B = auxs[r]
            for idx, w in enumerate(avail):
                lit = row_input_value(w, r, val)
                for selvar, tgt in ((s1[idx], A), (s2[idx], B)):
                    if lit is None:
                        c.add(-selvar, tgt)
                    elif lit is False:
                        c.add(-selvar, -tgt)
                    else:
                        c.add(-selvar, -lit, tgt)
                        c.add(-selvar, lit, -tgt)
            v = vals[r]
            # isAnd -> v = (A and B);  not isAnd -> v = (A or B)
            # AND gate (isAnd):  v <-> (A and B)
            c.add(-ia, -A, -B, v)     # A and B -> v
            c.add(-ia, -v, A)         # v -> A
            c.add(-ia, -v, B)         # v -> B
            # OR gate (not isAnd):  v <-> (A or B)
            c.add(ia, -A, v)          # A -> v
            c.add(ia, -B, v)          # B -> v
            c.add(ia, -v, A, B)       # v -> A or B
        sel.append((s1, s2))
        isand.append(ia)
        val.append(vals)
        aux.append(auxs)

    # AND-count window:  and_lo <= #{AND gates} <= and_hi
    if and_lo is not None and and_lo > 0:
        at_least_k(isand, and_lo, c)
    if and_hi is not None and and_hi < len(isand):
        neg = []
        for x in isand:
            v = c.var()
            c.add(-x, -v)
            c.add(x, v)
            neg.append(v)
        # "at most and_hi true"  <=>  "at least len-and_hi false"
        at_least_k(neg, len(neg) - and_hi, c)

    if out_is_or:
        # Sound: the output gate cannot be an AND.  Its monomial set would be
        # the unions of the monomials of its two operands, and to carry all 42
        # cross pairs {x_i, y_j} (i != j) the first operand would have to carry
        # every {x_i} and the second every {y_j}; then the pair {x_i, y_i}
        # would also be a monomial and the circuit would be wrong on the
        # diagonal input.  So the output gate is an OR.
        c.add(-isand[K - 1])
    # output = last gate must equal target
    for r in range(nrows):
        i, j = divmod(r, n)
        if i != j:
            c.add(val[K - 1][r])
        else:
            c.add(-val[K - 1][r])
    return c, sel, isand, val, ninp


def run_kissat(path, timeout):
    try:
        p = subprocess.run([KISSAT, path], capture_output=True, text=True,
                           timeout=timeout)
        out = p.stdout
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or "") if isinstance(e.stdout, str) else ""
        if isinstance(out, bytes):
            out = out.decode("utf8", "ignore")
        return "UNKNOWN", {}
    if "\ns SATISFIABLE" in out or out.startswith("s SATISFIABLE"):
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


def decode(model, sel, isand, val, ninp, n):
    gates = []
    for g in range(len(sel)):
        s1, s2 = sel[g]
        w1 = w2 = None
        for idx in range(len(s1)):
            if model.get(s1[idx], 0) == 1:
                w1 = idx
            if model.get(s2[idx], 0) == 1:
                w2 = idx
        op = "and" if model.get(isand[g], 0) == 1 else "or"
        gates.append((op, w1, w2))
    return gates


def evaluate(gates, n):
    """Return list of (row -> value) for all promise rows."""
    nrows = n * n
    ninp = 2 * n
    wires = []
    for r in range(nrows):
        i, j = divmod(r, n)
        vals = []
        for k in range(n):
            vals.append(1 if k == i else 0)
        for k in range(n):
            vals.append(1 if (n + k) == (n + j) else 0)
        wires.append(vals)
    for (op, w1, w2) in gates:
        for r in range(nrows):
            a = wires[r][w1]
            b = wires[r][w2]
            if op == "and":
                wires[r].append(1 if (a and b) else 0)
            else:
                wires[r].append(1 if (a or b) else 0)
    return [wires[r][ninp + len(gates) - 1] for r in range(nrows)]


def verify(gates, n):
    if gates is None:
        return False, "no gates"
    for (op, w1, w2) in gates:
        if w1 is None or w2 is None:
            return False, "unselected operand"
        if op not in ("and", "or"):
            return False, "bad op"
    vals = evaluate(gates, n)
    nrows = n * n
    for r in range(nrows):
        i, j = divmod(r, n)
        want = 1 if i != j else 0
        if vals[r] != want:
            return False, f"row ({i},{j}) got {vals[r]} want {want}"
    return True, "ok"


def variants(n):
    """(is_and, w1, w2) representatives of the orbits of the first gate."""
    out = []
    for ia in (0, 1):
        out.append((ia, 0, 1))                 # both left, distinct
        out.append((ia, 0, n))                 # matching cross u_0,v_0
        out.append((ia, 0, n + 1))             # non-matching cross u_0,v_1
    return out


def main():
    n = int(sys.argv[1])
    K = int(sys.argv[2])
    timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 3600
    outjson = sys.argv[4] if len(sys.argv) > 4 else None
    and_lo = int(sys.argv[5]) if len(sys.argv) > 5 and sys.argv[5] != "" else None
    and_hi = int(sys.argv[6]) if len(sys.argv) > 6 and sys.argv[6] != "" else None
    only = int(sys.argv[7]) if len(sys.argv) > 7 and sys.argv[7] != "" else None
    global OUT_OR
    OUT_OR = len(sys.argv) > 8 and sys.argv[8] == "or"

    cnf_path = f"/workspace/output/crown_{n}x{n}_k{K}_{and_lo}_{and_hi}.cnf"
    results = []
    for vi, v in enumerate(variants(n)):
        if only is not None and vi != only:
            continue
        c, sel, isand, val, ninp = encode(n, K, and_lo, and_hi, first=v, out_is_or=OUT_OR)
        nv, nc = c.dimacs(cnf_path)
        print(f"variant {vi} {v}: vars={nv} clauses={nc}", flush=True)
        status, model = run_kissat(cnf_path, timeout)
        print(f"  -> {status} ({timeout}s)", flush=True)
        rec = {"variant": vi, "first": v, "status": status, "vars": nv, "clauses": nc}
        if status == "SAT":
            gates = decode(model, sel, isand, val, ninp, n)
            ok, why = verify(gates, n)
            rec["verified"] = ok
            rec["why"] = why
            rec["gates"] = gates
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
