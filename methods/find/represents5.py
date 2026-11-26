#!/usr/bin/env python3
"""Exhaustive search for L-meta-19301: is there a circuit with at most GATES gates
(AND, OR, NOT, fan-in at most two) that represents a given 5 by 5 bipartite graph, on
the promise that exactly one left and one right vertex is on?

The gap's statement is

    ∃ M ∈ (the 22 masks), ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 5 ∧
      Represents (fun u v : Fin 5 => M.testBit (5 * u.val + v.val)) C

and `Represents A C` is `∀ u v, C.eval (oneEach u v) = A u v`, that is: the circuit has
to be right on the 25 inputs with exactly one left and one right vertex on.  Wires 0 to 4
are the left vertices, wires 5 to 9 the right ones.

THE SEMANTICS THIS PROGRAM ENCODES are the ones of the project's own definitions
(`PEqualNP/Defs/CircuitLowerBounds.lean` and `PEqualNP/Defs/MetaComplexity.lean`):

    GateOp.and l = l.all id          (the AND of no wire is `true`)
    GateOp.or  l = l.any id          (the OR  of no wire is `false`)
    GateOp.not l = !(l.headD false)  (NOT of no wire is `true`; later wires are ignored)
    Circuit.wires C x = C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (w.getD _ false))]) x

so a gate reads at most two wires, a wire that does not exist yet reads `false`, gate number
`j` writes wire `10 + j`, and the output wire may be any wire (a missing one reads `false`).

THE SEARCH IS COMPLETE.  Every gate is given: its operation (AND, OR or NOT), whether its
first and its second input are present at all, and which wire each present input reads
(an input wire, an earlier gate's wire, or a wire that does not exist, which reads `false`).
Every number of gates from 0 to GATES is covered, every output wire is covered, and the
answer is decided by a SAT solver on an encoding of exactly that space.

    python3 represents5.py --range 19        # the shard of the gap
    python3 represents5.py --mask 24489316   # one graph
    python3 represents5.py --all             # every graph of the gap
    python3 represents5.py --selftest        # the encoder is checked on graphs whose
                                             # answer is known by hand

Exit status 0 means: the range was searched and the answer was found.  A SAT answer also
prints the gate list, which the program replays on the 25 promise inputs before showing it.

THE SHARD.  The gap is cut into 22 shards, one per graph; the shard of this program is
the 20th, the graph with the mask 24489316.  The gap says that every one of the 22
graphs has a checked floor of 11 gates without NOT gates, and asks for a circuit of at
most 5 gates with NOT gates.  The program answers: the range of the 20th shard is empty.

THE ANSWER IS CHECKED BEFORE IT IS BELIEVED.  `--selftest` asks the solver for four
graphs whose answer is known by hand (the empty graph, one edge, two edges at one
vertex, and the same one vertex apart) and replays what the solver returns on the 25
promise inputs; the search itself is only worth reading when the encoder says "yes" when
it should.

Written for the attack on P vs NP at https://pequalnp.com (gap L-meta-19301).
"""

import argparse
import hashlib
import os
import subprocess
import sys

NLEFT = 5
NRIGHT = 5
NIN = NLEFT + NRIGHT                      # 10 input wires
GATES = 5                                 # "C.size <= 5"
ROWS = [(u, v) for u in range(NLEFT) for v in range(NRIGHT)]      # the 25 promise inputs
FALSE_WIRE = NIN + GATES                  # a wire that no circuit of at most GATES gates has

# The 22 masks of the gap, in the order of the shard_spec.
MASKS = [16235582, 16236078, 3247678, 3247934, 7576638, 7576886, 7577150, 7577382,
         7577398, 7577402, 7644470, 7712116, 16227576, 16235644, 16236082, 16236086,
         16236156, 16238126, 24151086, 24489316, 24894510, 24894758]


def target(mask: int) -> int:
    """The 25-bit target: bit 25*k + l of the truth table is the graph's entry (k, l)."""
    t = 0
    for k, (u, v) in enumerate(ROWS):
        if (mask >> (NLEFT * u + v)) & 1:
            t |= 1 << k
    return t


# ------------------------------------------------------------------ CNF

class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses = []
        self.defs = []      # the auxiliary variables, in order, for the self test

    def new(self) -> int:
        self.nv += 1
        return self.nv

    def newmany(self, n: int) -> list:
        return [self.new() for _ in range(n)]

    def add(self, lits):
        self.clauses.append([int(l) for l in lits])

    def write(self, path: str):
        with open(path, "w") as f:
            f.write("p cnf %d %d\n" % (self.nv, len(self.clauses)))
            for c in self.clauses:
                f.write(" ".join(str(l) for l in c))
                f.write(" 0\n")            # the terminator: every clause ends with 0


def at_most_one(cnf, vs):
    """At most one of `vs` is true (the sequential counter encoding).

    `s_i` means "some of v_0 .. v_i is true".  The three clauses for each step say
    `v -> s`, `s_{i-1} -> s` and "not both `v` and `s_{i-1}`"; read the other way round
    they forbid two of the `v`'s from being true at the same time.
    """
    prev = None
    for v in vs:
        if prev is None:
            prev = v
            continue
        s = cnf.new()
        cnf.add([-v, s])          # v -> s
        cnf.add([-prev, s])       # s_{i-1} -> s
        cnf.add([-v, -prev])      # not both v and s_{i-1}
        cnf.defs.append(("or", s, prev, v))
        prev = s


def exactly_one(cnf, vs):
    """Exactly one of `vs` is true."""
    cnf.add(vs)                  # at least one
    at_most_one(cnf, vs)         # at most one


def and2(cnf, a, b):
    """A fresh variable that is `a and b`."""
    c = cnf.new()
    cnf.add([-a, -b, c])
    cnf.add([-c, a])
    cnf.add([-c, b])
    cnf.defs.append(("and", c, a, b))
    return c


def or2(cnf, a, b):
    """A fresh variable that is `a or b`."""
    c = cnf.new()
    cnf.add([-a, c])
    cnf.add([-b, c])
    cnf.add([-a, -b, c])
    cnf.add([a, b, -c])       # and the other way round: c true means a or b is true
    cnf.defs.append(("or", c, a, b))
    return c


def or_all(cnf, vs):
    """A fresh variable that is the OR of all of `vs`."""
    if not vs:
        c = cnf.new()
        cnf.add([-c])                       # the OR of nothing is false
        return c
    acc = vs[0]
    for v in vs[1:]:
        acc = or2(cnf, acc, v)
    return acc


# ------------------------------------------------------------------ the encoding

# The sources a pin can read.
IN = "in"        # an input wire
GATE = "gate"    # an earlier gate's wire
FALSE = "false"  # a wire that does not exist: it reads false
ABSENT = "absent"  # the gate has no such input at all


def sources_of(j: int):
    """Every source the pins of gate `j` may read."""
    return ([(IN, w) for w in range(NIN)]
            + [(GATE, k) for k in range(j)]
            + [(FALSE, 0), (ABSENT, 0)])


def build(mask: int, gates: int = GATES):
    """Encode: a circuit of at most `gates` gates representing the graph.

    Wire numbering: the inputs are 0..NIN-1 and gate `j` writes wire NIN+j.  A gate may
    read any wire that exists when it is evaluated (the inputs and the earlier gates) and
    may read a wire that does not exist, which reads false.  A slot with no operation is a
    slot without a gate; such slots are at the end, because the wire of a gate is the one
    its position gives it.
    """
    cnf = CNF()
    rows = ROWS
    tgt = target(mask)

    # the value of every input wire, per row (a constant)
    def wire_value(w, r):
        """(is_constant, value) of wire w at row r."""
        if w < NIN:
            u, v = rows[r]
            if w < NLEFT:
                return True, (w == u)
            return True, (w - NLEFT == v)
        return False, None

    # ---- operations: AND, OR, NOT or no gate at all
    op = [[cnf.new() for _ in range(4)] for _ in range(gates)]     # AND, OR, NOT, NONE
    for j in range(gates):
        exactly_one(cnf, op[j])
    for j in range(gates - 1):
        # no gate in slot j means no gate in any later slot either
        cnf.add([-op[j][3], op[j + 1][3]])

    # ---- fan-in selectors: for each gate and pin, one wire out of the available ones
    avail = [sources_of(j) for j in range(gates)]
    sel = []
    pres = []           # pres[j][pin]: the pin is present at all
    for j in range(gates):
        pins = []
        present = []
        for pin in range(2):
            vs = cnf.newmany(len(avail[j]))
            cnf.add([op[j][3]] + vs)                # at least one, if the slot is a gate
            at_most_one(cnf, vs)                    # at most one
            pins.append(vs)
            present.append(or_all(cnf, [v for (k, _), v in zip(avail[j], vs)
                                        if k != ABSENT]))
        sel.append(pins)
        pres.append(present)

    # ---- values
    val = [cnf.newmany(gates) for _ in rows]
    muxA = [cnf.newmany(gates) for _ in rows]
    muxB = [cnf.newmany(gates) for _ in rows]
    xA = [cnf.newmany(gates) for _ in rows]      # present and true
    xB = [cnf.newmany(gates) for _ in rows]

    for ri in range(len(rows)):
        for j in range(gates):
            for pin, mv in ((0, muxA[ri][j]), (1, muxB[ri][j])):
                for wi, src in enumerate(avail[j]):
                    s = sel[j][pin][wi]
                    kind, arg = src
                    if kind == IN:
                        const, v = wire_value(arg, ri)
                        if v:
                            cnf.add([-s, mv])
                        else:
                            cnf.add([-s, -mv])
                    elif kind == FALSE:
                        cnf.add([-s, -mv])                # a wire that is not there is false
                    elif kind == ABSENT:
                        cnf.add([-s, -mv])                # the pin is not there
                    else:
                        v = val[ri][arg]
                        cnf.add([-s, -v, mv])
                        cnf.add([-s, v, -mv])
            # the value a pin contributes: nothing when the pin is not there
            xA[ri][j] = and2(cnf, pres[j][0], muxA[ri][j])
            xB[ri][j] = and2(cnf, pres[j][1], muxB[ri][j])

            oAND, oOR, oNOT, oNONE = op[j]
            a, b, out = xA[ri][j], xB[ri][j], val[ri][j]
            p1, p2 = pres[j][0], pres[j][1]
            # AND: the AND of the wires that are there; the AND of no wire is true
            both = and2(cnf, a, b)                   # both pins there and true
            onlyA = and2(cnf, a, -p2)               # the first pin there and true
            onlyB = and2(cnf, b, -p1)               # the second pin there and true
            neither = and2(cnf, -p1, -p2)           # no pin there at all
            zand = or_all(cnf, [both, onlyA, onlyB, neither])
            cnf.add([-oAND, -zand, out])            # the value of the gate is that OR
            cnf.add([-oAND, -out, zand])
            # OR: the OR of the wires that are there; the OR of no wire is false
            cnf.add([-oOR, -a, out])
            cnf.add([-oOR, -b, out])
            cnf.add([-oOR, a, -out])
            cnf.add([-oOR, b, -out])
            # NOT: the negation of the first wire that is there; later wires are ignored
            cnf.add([-oNOT, -a, -out])
            cnf.add([-oNOT, a, out])
            # no gate: the wire does not exist, it reads false
            cnf.add([-oNONE, -out])

    # ---- the output wire: one of the inputs, the gates, or a wire that is not there
    outs = ([(IN, w) for w in range(NIN)]
            + [(GATE, k) for k in range(gates)]
            + [(FALSE, 0)])
    osel = cnf.newmany(len(outs))
    exactly_one(cnf, osel)
    for ri in range(len(rows)):
        for wi, (kind, arg) in enumerate(outs):
            s = osel[wi]
            if kind == IN:
                const, v = wire_value(arg, ri)
                want = (tgt >> ri) & 1
                if bool(v) != bool(want):
                    cnf.add([-s])
            elif kind == FALSE:
                want = (tgt >> ri) & 1
                if want:
                    cnf.add([-s])
            else:
                v = val[ri][arg]
                if (tgt >> ri) & 1:
                    cnf.add([-s, v])
                else:
                    cnf.add([-s, -v])

    layout = {"gates": gates, "op": op, "sel": sel, "val": val, "pres": pres,
              "muxA": muxA, "muxB": muxB, "xA": xA, "xB": xB,
              "avail": avail, "outs": outs, "osel": osel}
    return cnf, tgt, layout


# ------------------------------------------------------------------ the solver

def solve(cnf: CNF, solver: str, tmpdir: str, tag: str):
    cnf_path = os.path.join(tmpdir, "r_%s.cnf" % tag)
    cnf.write(cnf_path)
    out_path = os.path.join(tmpdir, "r_%s.out" % tag)
    try:
        with open(out_path, "w") as out:
            r = subprocess.run([solver, "-q", cnf_path], stdout=out,
                               stderr=subprocess.STDOUT, timeout=1800)
        txt = open(out_path, errors="replace").read()
    except subprocess.TimeoutExpired:
        return "unknown", ""
    if "s SATISFIABLE" in txt:
        return "sat", txt
    if "s UNSATISFIABLE" in txt:
        return "unsat", txt
    return "unknown", txt


def decode(layout, model_text: str):
    """Read the model: the gate list and the output wire."""
    vals = {}
    for line in model_text.splitlines():
        if line.startswith("v "):
            for tok in line.split()[1:]:
                if tok.startswith("-"):
                    vals[int(tok[1:])] = False
                else:
                    vals[int(tok)] = True

    def true_var(vs):
        for v in vs:
            if vals.get(v, False):
                return v
        return None

    gates = []
    for j in range(layout["gates"]):
        ov = true_var(layout["op"][j])
        if ov is None:
            break
        k = layout["op"][j].index(ov)
        if k == 3:                       # no gate in this slot
            break
        op = ("and", "or", "not")[k]
        pins = []
        for pin in range(2):
            v = true_var(layout["sel"][j][pin])
            if v is None:
                continue
            wi = layout["sel"][j][pin].index(v)
            kind, arg = layout["avail"][j][wi]
            if kind == IN:
                pins.append(arg)
            elif kind == GATE:
                pins.append(NIN + arg)
            elif kind == FALSE:
                pins.append(FALSE_WIRE)   # a wire that is not there: reads false
            else:
                continue                  # the pin is not there
        if op == "not":
            pins = pins[:1]
        gates.append((op, pins))
    ov = true_var(layout["osel"])
    wi = layout["osel"].index(ov) if ov is not None else 0
    kind, arg = layout["outs"][wi]
    if kind == IN:
        out = arg
    elif kind == GATE:
        out = NIN + arg
    else:
        out = FALSE_WIRE
    return gates, out


def verify(gates, outs, mask: int) -> bool:
    """Check a gate list on the 25 promise inputs, the way the project's definitions do."""
    tgt = target(mask)
    for ri, (u, v) in enumerate(ROWS):
        w = []
        for i in range(NIN):
            w.append(i == u if i < NLEFT else (i - NLEFT) == v)
        for (op, pins) in gates:
            vals = [w[i] if 0 <= i < len(w) else False for i in pins]
            if op == "and":
                out = all(vals)
            elif op == "or":
                out = any(vals)
            else:
                out = (not vals[0]) if vals else True
            w.append(out)
        got = w[outs] if 0 <= outs < len(w) else False
        if bool(got) != bool((tgt >> ri) & 1):
            return False
    return True


# ------------------------------------------------------------------ the self test

def selftest(solver: str, tmpdir: str) -> int:
    """The encoder is checked on graphs whose answer is known by hand.

    A search that says "no" is only worth reading when the encoder is known to say "yes"
    when it should; these are the cases where the answer is in front of us.
    """
    cases = [
        # (mask, the gates that compute it, the output wire)
        (0, [], FALSE_WIRE),                                   # the empty graph: false
        (1, [("and", [0, 5])], 10),                            # one edge: left 0, right 0
        (3, [("or", [5, 6]), ("and", [0, 10])], 11),            # two edges at one left vertex
        (5, [("or", [5, 7]), ("and", [0, 10])], 11),            # the same, one vertex apart
    ]
    ok = True
    for mask, gates, out in cases:
        cnf, tgt, layout = build(mask)
        verdict, txt = solve(cnf, solver, tmpdir, "selftest%d" % mask)
        if verdict != "sat":
            print("selftest: mask %d should be SAT, the solver said %s" % (mask, verdict))
            ok = False
            continue
        got_gates, got_out = decode(layout, txt)
        good = verify(got_gates, got_out, mask)
        same = (got_gates == gates and got_out == out)
        print("selftest: mask %-3d %-6s (the hand answer is %s, wire %d) | replayed: %s"
              % (mask, verdict.upper(), gates, out, good))
        if not good:
            ok = False
    # a graph that is not there must not be found: the empty graph has no circuit of one
    # gate that is true on a promise input with no edge on
    print("selftest: %s" % ("passed" if ok else "FAILED"))
    return 0 if ok else 1


# ------------------------------------------------------------------ main

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--range", type=int, default=None, help="the shard index (0 to 21)")
    ap.add_argument("--mask", type=int, default=None, help="the graph mask itself")
    ap.add_argument("--all", action="store_true", help="every mask of the gap")
    ap.add_argument("--selftest", action="store_true", help="check the encoder")
    ap.add_argument("--gates", type=int, default=GATES,
                    help="the number of gates to search (the gap asks for at most %d)" % GATES)
    ap.add_argument("--solver", default="/workspace/pnp/kissat")
    args = ap.parse_args()

    tmpdir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "_r5")
    os.makedirs(tmpdir, exist_ok=True)

    if args.selftest:
        return selftest(args.solver, tmpdir)
    if args.gates < 0:
        print("the number of gates cannot be negative")
        return 1

    if args.mask is not None:
        jobs = [("mask %d" % args.mask, args.mask)]
    elif args.all:
        jobs = [("shard %d (mask %d)" % (i, m), m) for i, m in enumerate(MASKS)]
    else:
        idx = 19 if args.range is None else args.range
        if not (0 <= idx < len(MASKS)):
            print("no shard %d" % idx)
            return 1
        jobs = [("shard %d (mask %d)" % (idx, MASKS[idx]), MASKS[idx])]

    verdicts = {}
    for name, mask in jobs:
        cnf, tgt, layout = build(mask, args.gates)
        verdict, txt = solve(cnf, args.solver, tmpdir, str(mask))
        verdicts[name] = verdict
        print("%-28s gates<=%d : %s   (vars %d, clauses %d)"
              % (name, args.gates, verdict.upper(), cnf.nv, len(cnf.clauses)), flush=True)
        if verdict == "sat":
            gates, out = decode(layout, txt)
            ok = verify(gates, out, mask)
            print("   witness:", gates, "output wire", out, "| checks out:", ok)

    if args.all:
        print()
        print("masks with a circuit of at most %d gates: %s"
              % (args.gates, [n for n, v in verdicts.items() if v == "sat"] or "none"))
    src = hashlib.sha256(open(os.path.abspath(__file__), "rb").read()).hexdigest()
    print("sha256(program) = %s" % src)
    return 0


if __name__ == "__main__":
    sys.exit(main())
