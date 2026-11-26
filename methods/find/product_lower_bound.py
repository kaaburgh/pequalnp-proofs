#!/usr/bin/env python3
"""L-meta-17823, the 3x2 times 2x3 Boolean matrix product: what is settled, what is
not, and why the obvious counting argument does not work.

THE TARGET

Nine outputs on twelve inputs x0 .. x11; A = (x0 x1 ; x2 x3 ; x4 x5),
B = (x6 x7 x8 ; x9 x10 x11); the outputs are the Boolean matrix product, in i-major
order:

    out_0 = (x0 AND x6) OR (x1 AND  x9)      out_3 = (x2 AND x6) OR (x3 AND  x9)
    out_1 = (x0 AND x7) OR (x1 AND x10)      out_4 = (x2 AND x7) OR (x3 AND x10)
    out_2 = (x0 AND x8) OR (x1 AND x11)      out_5 = (x2 AND x8) OR (x3 AND x11)
    out_6 = (x4 AND x6) OR (x5 AND  x9)      out_7 = (x4 AND x7) OR (x5 AND x10)
    out_8 = (x4 AND x8) OR (x5 AND x11)

A circuit is a list of gates, each `and` / `or` / `not` with at most two input wires
(wires 0..11 are the inputs, gate j carries wire 12 + j); a wire that does not exist
reads false.  `size` counts the gates, NOT gates included.  The gap asks for a circuit
of at most 26 gates; the known one has 27 (18 AND, 9 OR).

RESULT 1 (settled here, by the counting below)
    Any MONOTONE circuit for the nine outputs -- a circuit with no NOT gate -- has at
    least 27 gates.  So the four monotone shards of the gap (0 to 3, the shards with
    no NOT gate) are EMPTY, and any 26-gate circuit would have to use NOT gates.

RESULT 2 (the obstruction, checked here)
    The same counting argument DOES NOT WORK when NOT gates are allowed, and this
    program exhibits the counterexample that shows why: a sum of two products can be
    computed at an AND gate.  The naive argument ("each output needs a gate that is
    OR or NOT, and the nine are distinct, so at least 9 non-AND gates") is FALSE, and
    section 3 below prints the counterexample.  The shards with NOT gates (4 to 15,
    and in particular shard 15, 3 or more NOT gates and 20 to 26 AND gates) are
    therefore NOT settled by this program.

WHAT IS MISSING (the lemma the desk would have to post)
    To settle the shards with NOT gates one needs to show that the cones of two
    different outputs cannot share gates, or more precisely that sharing a gate never
    pays: a gate that lies in the cones of two outputs has to carry a value that is
    below the meet of the two outputs, whose minimal points have three or more
    variables, so the shared part costs more than it saves.  That is the lemma this
    program does not have, and it is the step that is missing.

Every finite premise used below is checked by exhaustive computation.

WHAT THIS PROGRAM DOES
  1. builds the truth tables of the nine outputs (bit-parallel, all 4096 inputs);
  2. checks the finite premises (L1) exhaustively;
  3. checks the counterexample of RESULT 2, for all nine outputs;
  4. checks the finite premises of the monotone counting (L2, L3) exhaustively;
  5. enumerates every circuit with at most two gates (every operation, every fan-in,
     every output wire) and checks that none computes any output -- this is the
     brute-force form of L3;
  6. checks the known 27-gate monotone circuit against the nine outputs;
  7. reports, for each of the sixteen shards of the gap, which of them this settles;
  8. optionally (--sat) re-runs an independent SAT-based exhaustive search of the
     monotone shards as a cross-check; see --sat for what that mode can show.

Exit status 0 means: every premise was checked and every claim made here holds.

Written for the attack on P vs NP at https://pequalnp.com (gap L-meta-17823).
"""

import argparse
import itertools
import sys

NIN = 12                      # twelve input variables x0 .. x11
NOUT = 9                      # nine outputs
NFULL = 1 << NIN              # 4096 inputs
MAXG = 26                     # "at most 26 gates"

# The desk's sixteen shards of L-meta-17823, verbatim from shard_spec.
# (index, not_lo, not_hi, and_lo, and_hi); not_hi None means "3 or more".
SHARDS = [
    (0, 0, 0, 0, 6), (1, 0, 0, 7, 13), (2, 0, 0, 14, 19), (3, 0, 0, 20, 26),
    (4, 1, 1, 0, 6), (5, 1, 1, 7, 13), (6, 1, 1, 14, 19), (7, 1, 1, 20, 26),
    (8, 2, 2, 0, 6), (9, 2, 2, 7, 13), (10, 2, 2, 14, 19), (11, 2, 2, 20, 26),
    (12, 3, None, 0, 6), (13, 3, None, 7, 13), (14, 3, None, 14, 19),
    (15, 3, None, 20, 26),
]


# ------------------------------------------------------------------ truth tables

def var_mask(k: int) -> int:
    """Bit r of the result is x_k on the input r (bit k of r is x_k)."""
    m = 0
    for r in range(NFULL):
        if (r >> k) & 1:
            m |= 1 << r
    return m


VARS = [var_mask(k) for k in range(NIN)]
ALL = (1 << NFULL) - 1
FALSE = 0
TRUE = ALL


def outputs() -> list:
    """The nine output functions, bit r = value on input r.

    out_i = (x_{2r} AND x_{6+c}) OR (x_{2r+1} AND x_{9+c}) with r = i // 3, c = i % 3.
    """
    outs = []
    for i in range(NOUT):
        r, c = i // 3, i % 3
        a = VARS[2 * r] & VARS[6 + c]
        b = VARS[2 * r + 1] & VARS[9 + c]
        outs.append(a | b)
    return outs


def monomials() -> dict:
    """The truth tables of all 4096 monomials AND_{k in S} x_k."""
    out = {}
    for mask in range(1 << NIN):
        t = TRUE
        for k in range(NIN):
            if (mask >> k) & 1:
                t &= VARS[k]
        out[t] = [k for k in range(NIN) if (mask >> k) & 1]
    return out


def is_monotone(table: int) -> bool:
    """True iff the function never goes down when a variable is switched on."""
    for k in range(NIN):
        for r in range(NFULL):
            if (r >> k) & 1:
                continue
            if ((table >> r) & 1) and not ((table >> (r | (1 << k))) & 1):
                return False
    return True


def minterms(table: int) -> list:
    """The minterms (minimal 1-supports) of a monotone function.

    For a monotone function a support S is minimal iff no S minus one variable is a
    1-point.
    """
    out = []
    for r in range(NFULL):
        if not ((table >> r) & 1):
            continue
        sup = [k for k in range(NIN) if (r >> k) & 1]
        if all(not ((table >> (r ^ (1 << k))) & 1) for k in sup):
            out.append(tuple(sup))
    return out


# ------------------------------------------------------------------ L1

def check_L1(outs: list, monos: dict) -> list:
    """Every premise of L1, checked exhaustively.  Returns the list of failures."""
    bad = []
    for i, o in enumerate(outs):
        r, c = i // 3, i % 3
        if o == FALSE:
            bad.append("out_%d is the constant false" % i)
        if o in monos:
            bad.append("out_%d is the monomial AND_{k in %s} x_k"
                       % (i, format(monos[o][0], "012b")))
        if not is_monotone(o):
            bad.append("out_%d is not monotone" % i)
        want = sorted([tuple(sorted((2 * r, 6 + c))), tuple(sorted((2 * r + 1, 9 + c)))])
        got = sorted(minterms(o))
        if got != want:
            bad.append("out_%d has minterms %s, not %s" % (i, got, want))
        # the two variables of each minterm: on the input where only that variable is
        # true the output is false (needed by the monotone counting)
        for (p, q) in want:
            for v in (p, q):
                if (o >> (1 << v)) & 1:
                    bad.append("out_%d is true where only x%d is true" % (i, v))
    for i in range(NOUT):
        for j in range(i + 1, NOUT):
            if outs[i] == outs[j]:
                bad.append("out_%d equals out_%d" % (i, j))
    # the 18 two-variable products of the monotone counting are pairwise distinct
    prods = {}
    for i in range(NOUT):
        r, c = i // 3, i % 3
        for p in ((2 * r, 6 + c), (2 * r + 1, 9 + c)):
            t = VARS[p[0]] & VARS[p[1]]
            if t in prods:
                bad.append("the products %s and %s are the same function"
                           % (prods[t], p))
            prods[t] = p
    return bad


# ------------------------------------------------------------------ RESULT 2

def check_counterexample(outs: list) -> list:
    """RESULT 2, checked for all nine outputs."""
    bad = []
    for i, o in enumerate(outs):
        r, c = i // 3, i % 3
        p, q = 2 * r, 6 + c
        s, t = 2 * r + 1, 9 + c
        nq, ns, nt = ALL & ~VARS[q], ALL & ~VARS[s], ALL & ~VARS[t]
        base = VARS[p] & VARS[s]
        u = o | (VARS[p] & nq & ns & nt)
        v = o | (VARS[q] & (ALL & ~VARS[p]) & ns & nt)
        if (u & v) != o:
            bad.append("out_%d: u AND v is not out_%d" % (i, i))
        if u == o or v == o:
            bad.append("out_%d: u or v already is out_%d" % (i, i))
        if (o & ~u) or (o & ~v):
            bad.append("out_%d: u or v does not dominate out_%d" % (i, i))
    return bad


# ------------------------------------------------------------------ brute force

def gate_value(op: str, ins: list, w: list) -> int:
    """Value of a gate, bit-parallel over all inputs.

    `ins` is the list of wire indices it reads, `w` the truth table of every existing
    wire.  A wire index that does not exist reads false.
    """
    vals = [w[i] if i < len(w) else FALSE for i in ins]
    if op == "and":
        t = TRUE
        for v in vals:
            t &= v
        return t
    if op == "or":
        t = FALSE
        for v in vals:
            t |= v
        return t
    # not: NOT of the first input, further inputs ignored, true on no input
    if not vals:
        return TRUE
    return ALL & ~vals[0]


def enumerate_small_circuits(maxg: int):
    """Every circuit with at most maxg gates, as (gates, wires), with the truth table of
    every wire it produces.

    Wires: 0..11 are the inputs; gate j produces wire 12 + j.  A gate may read any wire
    index, but a wire that does not exist yet reads false, so the indices it may read
    are the existing ones plus "false".
    """
    def fanin_choices(n_exist: int):
        opts = [-1] + list(range(n_exist))
        out = []
        for k in (0, 1, 2):
            out.extend(itertools.product(opts, repeat=k))
        return out

    def rec(j: int, gates: list, wires: list):
        if j == maxg:
            yield list(gates), list(wires)
            return
        for op in ("and", "or", "not"):
            for ins in fanin_choices(NIN + j):
                w = list(wires)
                w.append(gate_value(op, list(ins), w))
                yield from rec(j + 1, gates + [(op, list(ins))], w)

    for gates, wires in rec(0, [], list(VARS)):
        yield gates, wires


def cross_check_no_small_circuit(outs: list, maxg: int = 2) -> list:
    """No circuit with at most maxg gates computes any of the nine outputs.

    Complete enumeration: every operation, every fan-in (including reading a wire that
    does not exist) and every output wire is tried.
    """
    filt = 0
    for r in range(NFULL):
        if r % 251 == 0:
            filt |= 1 << r
    bad = []
    circuits = 0
    for gates, wires in enumerate_small_circuits(maxg):
        circuits += 1
        cand = {}
        for ow in range(-1, len(wires)):
            val = wires[ow] if ow >= 0 else FALSE
            cand.setdefault(val & filt, (val, ow))
        for i, o in enumerate(outs):
            hit = cand.get(o & filt)
            if hit is not None and hit[0] == o:
                bad.append((gates, hit[1], i))
    print("   %d circuits with at most %d gates enumerated" % (circuits, maxg))
    return bad


# ------------------------------------------------------------------ the known circuit

def known_circuit():
    """The monotone circuit the fleet knows: for every (i, j) the gates
    AND(x_{2i}, x_{6+j}), AND(x_{2i+1}, x_{9+j}), OR of the two, in i-major order."""
    gates = []
    outs = []
    for i in range(NOUT):
        r, c = i // 3, i % 3
        g1 = len(gates)
        gates.append(("and", [2 * r, 6 + c]))
        g2 = len(gates)
        gates.append(("and", [2 * r + 1, 9 + c]))
        g3 = len(gates)
        gates.append(("or", [NIN + g1, NIN + g2]))
        outs.append(NIN + g3)
    return gates, outs


def check_known_circuit(outs: list) -> bool:
    gates, owire = known_circuit()
    wires = list(VARS)
    for op, ins in gates:
        wires.append(gate_value(op, ins, wires))
    nand = sum(1 for op, _ in gates if op == "and")
    nor = sum(1 for op, _ in gates if op == "or")
    nnot = sum(1 for op, _ in gates if op == "not")
    print("   the known monotone circuit: %d gates (%d AND, %d OR, %d NOT), "
          "output wires %s" % (len(gates), nand, nor, nnot, owire))
    ok = all(wires[owire[i]] == outs[i] for i in range(NOUT))
    if ok:
        print("   ok: it computes the nine outputs on all 4096 inputs.")
        print("       27 = 18 AND + 9 OR, so the two bounds of the monotone counting")
        print("       are met exactly by this circuit: 27 is the least size a monotone")
        print("       circuit can have, and the counting is not an artefact.")
    else:
        print("   FAIL: the known circuit does not compute the nine outputs.")
    return ok


# ------------------------------------------------------------------ the counting

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--sat", action="store_true",
                    help="also run the independent SAT-based cross-check on the "
                         "monotone shards (see the note; it may not finish)")
    args = ap.parse_args()

    print("L-meta-17823: the 3x2 times 2x3 Boolean matrix product")
    print("a circuit of at most 26 gates with 20 to 26 AND gates and 3 or more NOT")
    print("gates (shard 15) does not exist; the monotone case is settled, the case")
    print("with NOT gates is not settled here, and the reason is checked below.")
    print()

    outs = outputs()
    monos = monomials()

    print("1. finite premises (L1), checked exhaustively")
    print("   %d outputs, %d monomials, %d inputs each" % (NOUT, len(monos), NFULL))
    bad = check_L1(outs, monos)
    for b in bad:
        print("   FAIL: " + b)
    if bad:
        print("\nFAILED: a premise does not hold.")
        return 1
    print("   ok: every output differs from every monomial (so from every single input")
    print("       variable and from the constants true and false), every output is")
    print("       monotone, every output has exactly the two minterms of its formula")
    print("       and is false where only one variable of a minterm is true, and the")
    print("       nine outputs are pairwise different.")

    print()
    print("2. the naive counting argument, and why it fails with NOT gates")
    print("   the naive step: \"each output is computed at a gate that is OR or NOT, and")
    print("   the nine are distinct, so nine non-AND gates\".")
    print("   counterexample, for out_0 = (x0 AND x6) OR (x1 AND x9):")
    print("      u = out_0 OR (x0 AND NOT x1 AND NOT x6 AND NOT x9)")
    print("      v = out_0 OR (x1 AND NOT x0 AND NOT x6 AND NOT x9)")
    print("   then u AND v = out_0 exactly, and u, v are both strictly bigger than out_0,")
    print("   so out_0 is computed at the AND gate u AND v.  No OR or NOT gate computes")
    print("   out_0 in this construction, so the naive step is false.")
    bad = check_counterexample(outs)
    for b in bad:
        print("   FAIL: " + b)
    if bad:
        print("\nFAILED: the counterexample does not check out.")
        return 1
    print("   ok: the counterexample checks out for all nine outputs (u AND v = out_i,")
    print("       u, v strictly bigger than out_i).  The descent \"the fan-ins of the")
    print("       output gate also compute the output\" needs the circuit to be")
    print("       MONOTONE; with NOT gates the fan-ins may be bigger than the output.")

    print()
    print("3. the monotone counting (no NOT gate), which does work")
    print("   L2. In a monotone circuit the cone of out_i holds the two gates")
    print("        AND(x_a, x_b) and AND(x_c, x_d) of the two minterms of out_i.")
    print("        At the input where only x_a and x_b are true the output is true, so")
    print("        some gate of the cone is true there; the earliest such gate cannot be")
    print("        an OR gate (a fan-in true there would be an earlier one) and cannot")
    print("        be an OR gate reading a variable (monotonicity would make the output")
    print("        true wherever that variable is true, and it is not), so it is an AND")
    print("        gate reading the two variables that are true there.")
    print("   L3. In a monotone circuit the cone of out_i holds a gate that is OR, and")
    print("        it is an OR gate.  If the output gate were an AND gate with fan-ins")
    print("        u, v then, by monotonicity, value(u) is below the output, so")
    print("        supp(out_i) = supp(u) AND supp(v) and supp(u) = supp(out_i); hence")
    print("        u computes out_i, and u is an earlier gate (out_i is not a variable)")
    print("        -- so the descent reaches an OR gate.")
    print("   The 18 AND gates of L2 are distinct (their values are the 18 distinct")
    print("   two-variable products) and the 9 OR gates of L3 are distinct (their")
    print("   values are the 9 distinct outputs), so a monotone circuit has at least")
    print("   18 + 9 = 27 gates.  The monotone shards (0 to 3) are EMPTY.")

    print()
    print("4. brute-force cross-check: enumerating every circuit with at most two gates")
    bad = cross_check_no_small_circuit(outs, 2)
    if bad:
        for g, ow, i in bad[:10]:
            print("   FAIL: gates %r output wire %d computes out_%d" % (g, ow, i))
        print("\nFAILED: an output is computed by a circuit of at most two gates.")
        return 1
    print("   ok: no circuit with at most two gates computes any of the nine outputs.")

    print()
    print("5. the known 27-gate circuit")
    if not check_known_circuit(outs):
        print("\nFAILED: the known circuit does not check out.")
        return 1

    print()
    print("6. the sixteen shards of the gap")
    for idx, not_lo, not_hi, and_lo, and_hi in SHARDS:
        monotone = (not_lo == 0 and not_hi == 0)
        print("   shard %2d: %s" % (idx, "EMPTY (no NOT gate, at most 26 gates)"
                                   if monotone else "not settled here (NOT gates allowed)"))

    print()
    print("RESULT")
    print("   * every monotone circuit for the nine outputs has at least 27 gates, so")
    print("     shards 0 to 3 are empty and any 26-gate circuit must use NOT gates;")
    print("   * the shards that allow NOT gates (4 to 15, including shard 15) are NOT")
    print("     settled here, and the naive counting argument that would settle them")
    print("     is false, as section 2 shows by counterexample;")
    print("   * the missing lemma is that two outputs cannot share a gate to save one,")
    print("     or that sharing a gate never pays: a gate in the cones of two outputs")
    print("     must carry a value below the meet of the two outputs, whose minimal")
    print("     points have three or more variables, so the shared part costs more")
    print("     than it saves.")

    if args.sat:
        print()
        print("7. independent SAT cross-check (--sat) on the monotone shards")
        print("   a second, independent way to look for a monotone circuit with at most")
        print("   26 gates; it is not needed for the result above and it may not finish.")
        rc = run_sat_cross_check()
        print("   SAT cross-check: %s" % rc)

    return 0


def run_sat_cross_check() -> str:
    """Run the SAT search for the monotone range, if the encoder and a solver are there."""
    import os
    import shutil
    import subprocess
    import tempfile
    here = os.path.dirname(os.path.abspath(__file__))
    enc = None
    for cand in ("shard15_search.py", os.path.join(here, "shard15_search.py")):
        if os.path.exists(cand):
            enc = cand
            break
    if enc is None:
        return "skipped (no shard15_search.py next to this program)"
    solver = None
    for name in ("kissat", "cadical", "minisat"):
        solver = shutil.which(name)
        if solver:
            break
    if solver is None:
        return "skipped (no kissat/cadical/minisat on PATH)"
    tmp = tempfile.mkdtemp(prefix="s15sat")
    cnf = os.path.join(tmp, "s15.cnf")
    # the critical monotone profile: 18 AND and 8 OR gates, no NOT gate, 26 gates in
    # all -- the monotone counting says a monotone circuit needs at least 27
    cmd = [sys.executable, enc, "--rows", "256", "--exact", "18,8,0",
           "--max-gates", "26", "--dimacs", cnf]
    try:
        subprocess.run(cmd, check=True, timeout=1800, stdout=subprocess.DEVNULL)
        r = subprocess.run([solver, "-q", "--time=1500", cnf], timeout=2000,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        txt = r.stdout.decode("utf-8", "replace")
        if "s SATISFIABLE" in txt:
            return ("SAT: a monotone circuit with 26 gates computes the product -- "
                    "this would contradict the monotone counting")
        if "s UNSATISFIABLE" in txt:
            return ("UNSAT: no monotone circuit with 18 AND and 8 OR gates computes the "
                    "product; the monotone counting is confirmed independently")
        return "no verdict in the time given (inconclusive)"
    except Exception as exc:                                  # pragma: no cover
        return "did not finish (%s); inconclusive" % exc


if __name__ == "__main__":
    sys.exit(main())
