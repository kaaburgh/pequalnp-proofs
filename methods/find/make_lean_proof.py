#!/usr/bin/env python3
"""Generate a Lean proof file for one gap of the P vs NP attack.

    python3 make_lean_proof.py <gap-id> <n> <size> <gates.py-json>

The statement is taken verbatim from the desk row of the gap, the circuit from a
JSON file holding the gate list and the output wire.  The proof follows the
technique of PEqualNP/Outside/L_meta_17391.lean: the input bits and the wanted
output are packed into BitVec tables of 2 ^ n rows, and the kernel checks that
the gate list turns the first into the second.

The file obeys the rules of CONTRIBUTING.md: one import line, one namespace
block with the helpers, one theorem last, no sorry, no string literals, no
commands, only the four allowed options.
"""

import json
import sys
import urllib.request

DECK = "https://pequalnp.com/desk/row?gap="

HEADER = """import PEqualNP.Defs

namespace {ns}

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hcsGateVal {{rows : Nat}} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {{rows : Nat}} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {{rows : Nat}} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {{rows : Nat}} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {{rows : Nat}} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {{rows : Nat}} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({{PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not}} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {{rows : Nat}} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({{PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not}} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {{p : Nat → Bool}} {{k s i : Nat}}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

def hcsBitsNat : {{k : Nat}} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, x => (if x 0 then 1 else 0) + 2 * hcsBitsNat (fun i : Fin k => x i.succ)

theorem hcsBitsNat_lt : ∀ {{k : Nat}} (x : Fin k → Bool), hcsBitsNat x < 2 ^ k
  | 0, _ => by simp [hcsBitsNat]
  | k + 1, x => by
    have ih := hcsBitsNat_lt (fun i : Fin k => x i.succ)
    simp only [hcsBitsNat, Nat.pow_succ]
    cases x 0
    · simp; omega
    · simp; omega

theorem hcsBitsNat_testBit : ∀ {{k : Nat}} (x : Fin k → Bool) (i : Fin k),
    (hcsBitsNat x).testBit i.val = x i
  | 0, _, i => Fin.elim0 i
  | k + 1, x, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [hcsBitsNat, Fin.val_zero]
      cases x 0
      · simp [Nat.testBit_zero]
      · have hmod : (1 + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) % 2 = 1 := by omega
        simp [Nat.testBit_zero, hmod]
    · intro j
      have ih := hcsBitsNat_testBit (fun m : Fin k => x m.succ) j
      have hdiv : ((if x 0 then 1 else 0) + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) / 2 =
          hcsBitsNat (fun m : Fin k => x m.succ) := by
        cases x 0
        · simp
        · simp; omega
      simpa only [hcsBitsNat, Fin.val_succ, Nat.testBit_succ, hdiv] using ih

theorem hcsWitnessEval {{n : Nat}} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0 = goal) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  let r := hcsBitsNat x
  have hr : r < 2 ^ n := hcsBitsNat_lt x
  have hx : x = fun j : Fin n => r.testBit j.val := by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank : raw.map (fun v => v.getLsbD r) = List.ofFn fun j : Fin n => r.testBit j.val :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hfg : goal.getLsbD r = f (fun j : Fin n => r.testBit j.val) :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hbits := hcsFoldBits raw ⟨r, hr⟩ C.gates hfan
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn fun j : Fin n => r.testBit j.val)).getD C.output false =
      f (fun j : Fin n => r.testBit j.val)
  rw [← hbank, ← hbits, ← hcsGetDBit, hEval, hfg]

theorem hcsWitness {{n : Nat}} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Nat) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hsz : C.size ≤ s)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0 = goal) :
    PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  exact ⟨C, hfan, hsz, hcsWitnessEval raw goal C f hfan hRaw hGoal hEval⟩

def witness : Circuit :=
  ⟨[
{gates}], {output}⟩

theorem basis : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with {cases} <;> subst g <;> simp

def words (xs : List ℕ) : BitVec {rows} :=
  BitVec.ofNat {rows} (xs.foldr (fun w rest => w + rest * 2 ^ 64) 0)

set_option maxRecDepth 1000000 in
def inputTables : List (BitVec {rows}) := [
{tables}]

set_option maxRecDepth 1000000 in
def outputTable : BitVec {rows} := words [{outwords}]

end {ns}

open {ns} in
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem {ns} : {statement} := by
  exact hcsWitness (n := {n}) inputTables outputTable witness {size} _ basis
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
"""


def words_of_bits(bits, width=64):
    """Pack a list of bits (index 0 first) into words of 64 bits."""
    out = []
    for start in range(0, len(bits), width):
        chunk = bits[start:start + width]
        val = 0
        for j, b in enumerate(chunk):
            if b:
                val |= 1 << j
        out.append(val)
    return out


def evaluate_circuit(gates, n, x):
    """x: list of n input bits; returns the output bit of the circuit."""
    bank = list(x)
    for op, ins in gates:
        vals = [bank[i] for i in ins]
        if op == "and":
            bank.append(int(all(vals)))
        elif op == "or":
            bank.append(int(any(vals)))
        elif op == "not":
            bank.append(1 - vals[0])
        else:
            raise ValueError(op)
    return bank[n + len(gates) - 1]


def hexw(v):
    return "0x%016x" % v


def main():
    gap = sys.argv[1]
    n = int(sys.argv[2])
    size = int(sys.argv[3])
    circ = json.load(open(sys.argv[4]))
    gates = circ["gates"]
    output = circ["output"]

    ns = "PEqualNP.Outside." + gap.replace("-", "_")
    mod = "lean/PEqualNP/Outside/" + gap.replace("-", "_") + ".lean"

    with urllib.request.urlopen(DECK + gap) as fh:
        row = json.load(fh)["gaps"][0]
    statement = row["statement"]

    rows = 1 << n
    # the input tables: bit b of the table of input i is (b >> i) & 1
    tabs = []
    for i in range(n):
        bits = [(b >> i) & 1 for b in range(rows)]
        w = words_of_bits(bits)
        tabs.append("  words [" + ", ".join(hexw(x) for x in w) + "]" + ("," if i < n - 1 else ""))
    # the output table: the value of the circuit on every assignment
    obits = []
    for b in range(rows):
        xb = [(b >> i) & 1 for i in range(n)]
        obits.append(evaluate_circuit(gates, n, xb))
    ow = words_of_bits(obits)

    glines = []
    for k, (op, ins) in enumerate(gates):
        comma = "," if k < len(gates) - 1 else ""
        glines.append("    ⟨.%s, [%s]⟩%s" % (op, ", ".join(str(i) for i in ins), comma))

    body = HEADER.format(
        ns=ns, rows=rows, gates="\n".join(glines), output=output,
        cases="|".join(["h"] * len(gates)),
        tables="\n".join(tabs),
        outwords=", ".join(hexw(x) for x in ow),
        statement=statement, n=n, size=size)

    with open(mod, "w") as fh:
        fh.write(body)
    print("wrote", mod, "gates:", len(gates), "bytes:", len(body))


if __name__ == "__main__":
    main()
