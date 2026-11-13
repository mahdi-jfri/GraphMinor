module

public import GraphMinor.Compute.GM06Alg34InducedSizeBounds
import Mathlib.Tactic.Ring

/-!
# A finite capacity and word budget for deletion serialization

The output budget reserves the old endpoint size, one maximal boundary
record for every supplied cell and one extra record, and the original
cuff and division section sizes. This covers every serialization pass.
A cubic capacity in the original array size bounds that budget and is
computed directly from the supplied vertex count and array length.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Space budget covering all intermediate output cursors of serialization. -/
def gm06SerializationBudget (x : GM06DrawingData) : ℕ :=
  3 + 2 * x.ends.length + (x.cellCount + 1) * (2 + x.n + x.ends.length) +
    x.cuffWords.length + x.divisionWords.length

/-- A uniform reserved capacity, computed from the original finite input size. -/
def gm06PayloadCapacity (x : GM06DrawingData) : ℕ := (x.size + 2) ^ 3

private theorem cubic_capacity (n : ℕ) : n + (n + 1) * (n + 2) ≤ (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The serialization budget fits in the reserved cubic output capacity. -/
theorem gm06SerializationBudget_le_capacity (x : GM06DrawingData) :
    gm06SerializationBudget x ≤ gm06PayloadCapacity x := by
  have hwords := x.words_length
  have hsize := x.words_length_le_size
  have hN := x.cellCount_le_size
  have hM : 2 + x.n + x.ends.length ≤ x.size + 2 := by
    dsimp only [GM06DrawingData.cellCount] at hN
    omega
  have hprod := Nat.mul_le_mul (Nat.add_le_add_right hN 1) hM
  have hh : gm06SerializationBudget x ≤ x.size + (x.size + 1) * (x.size + 2) := by
    unfold gm06SerializationBudget
    omega
  exact hh.trans (cubic_capacity x.size)

/-- The complete new word array fits the budget used by serialization. -/
theorem gm06Induced_words_le_serializationBudget (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.inducedData vs).words.length ≤ gm06SerializationBudget x := by
  have hr := gm06Induced_regionWords_length_le x vs
  have hc := gm06Induced_cuffWords_length_le x vs
  have hd := gm06Induced_divisionWords_length_le x vs
  have he : (x.inducedData vs).ends.length ≤ x.ends.length := by
    rw [x.inducedData_ends_length, ← gm06EdgeMask_sum]
    exact gm06EdgeMask_sum_le x vs
  have hw := (x.inducedData vs).words_length
  unfold gm06SerializationBudget
  rw [Nat.add_mul x.cellCount 1 (2 + x.n + x.ends.length), Nat.one_mul]
  omega

/-- The reserved output capacity fits a logarithmic RAM word. -/
theorem gm06PayloadCapacity_lt_wordSize (x : GM06DrawingData) {c : ℕ} (hc : 3 ≤ c) :
    gm06PayloadCapacity x < 2 ^ wordSize c x.size := by
  apply lt_two_pow_wordSize_of_lt_pow (by omega)
  exact Nat.pow_le_pow_right (by omega) hc

/-- Compute the cubic output capacity from header vertex count and input length. -/
def gm06PayloadCapacityExpr : Expr :=
  let base := Expr.op .add (.op .add (.reg 100) (.len 0)) (.const 2)
  .op .mul (.op .mul base base) base

/-- The capacity expression reads only supplied array data and returns
the exact finite capacity, with every intermediate value within a word. -/
theorem gm06PayloadCapacityExpr_eval (x : GM06DrawingData) {c : ℕ} (hc : 3 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) (hn : s.regs 100 = x.n) :
    gm06PayloadCapacityExpr.eval (wordSize c x.size) s = some (gm06PayloadCapacity x) := by
  have hcap := gm06PayloadCapacity_lt_wordSize x hc
  have hbase : x.size + 2 < 2 ^ wordSize c x.size :=
    (Nat.le_self_pow (by decide : 3 ≠ 0) (x.size + 2)).trans_lt hcap
  have hsquare := sq_lt_two_pow_wordSize (n := x.size) (by omega : 2 ≤ c)
  have hsize : x.size < 2 ^ wordSize c x.size := by omega
  have hnw := x.counts_le_size.1.trans_lt hsize
  have hlen := x.words_length_le_size.trans_lt hsize
  have htwo : 2 < 2 ^ wordSize c x.size := by omega
  simp only [gm06PayloadCapacity, Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at hcap
  simp only [GM06DrawingData.size] at hcap hbase hsquare hsize hnw hlen htwo
  simp [gm06PayloadCapacityExpr, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hinput, hn,
    hnw, hlen, hsize, htwo, hbase, hsquare, hcap, gm06PayloadCapacity, Nat.pow_succ, Nat.pow_zero,
    Nat.one_mul, GM06DrawingData.size]

end GraphMinor.Compute
