module

public import GraphMinor.Compute.GM06SuccessorDegreeScan
import Mathlib.Tactic.Linarith

/-!
# Polynomial time for the initial-cuff incidence scan

The size includes the vertex count and the finite input length. For
ordinary labels bounded by that size, logarithmic RAM words hold all
input entries and row lengths. Loading the input and testing every
initial vertex then takes quadratic time in this size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Size of the ordinary finite successor input, including isolated vertices. -/
def gm06SuccessorInputSize (x : GM06SuccessorInput) : ℕ :=
  x.vertexCount + (gm06EncodeSuccessorInput x).length

/-- The initial-cuff scan runs in quadratic time with logarithmic RAM words. -/
theorem gm06SuccessorDegreeScan_computes :
    ComputesRelInTime gm06SuccessorInputSize
      (fun x s => s.arrs 0 = gm06EncodeSuccessorInput x ∧
        ∀ v ∈ gm06EncodeSuccessorInput x, v ≤ gm06SuccessorInputSize x + 1)
      (fun x s =>
        (s.regs 27 = 0 ∧ ∀ j (hj : j < x.innerCuff.length),
          x.endpoints.count x.innerCuff[j] ≠ 1) ∨
        (s.regs 27 = 1 ∧ ∃ (j : ℕ) (hj : j < x.innerCuff.length),
          s.regs 28 = j ∧ x.endpoints.count x.innerCuff[j] = 1))
      gm06SuccessorDegreeScanProg (fun n => (n + 1) ^ 2) := by
  refine ⟨70, 1, by decide, le_rfl, ?_⟩
  intro x s hs
  let n := gm06SuccessorInputSize x
  have hsize : (gm06EncodeSuccessorInput x).length ≤ n := Nat.le_add_left _ _
  have hw : 1 < 2 ^ wordSize 1 n := lt_two_pow_wordSize_of_le le_rfl (by omega)
  have hn : (gm06EncodeSuccessorInput x).length < 2 ^ wordSize 1 n :=
    lt_two_pow_wordSize_of_le le_rfl (by omega)
  have hwords : ∀ v ∈ gm06EncodeSuccessorInput x, v < 2 ^ wordSize 1 n :=
    fun v hv => lt_two_pow_wordSize_of_le le_rfl (hs.2 v hv)
  obtain ⟨s', t, he, ht, _, hd⟩ := gm06SuccessorDegreeScanProg_exec x s hw hs.1 hn hwords
  have hrow : ∀ row ∈ gm06SuccessorRows x, row.length ≤ n + 1 := by
    intro row hr
    exact hs.2 _ (gm06RowLength_mem_code hr)
  have hends : x.endpoints.length ≤ n + 1 := hrow _ (by simp [gm06SuccessorRows])
  have hcuff : x.innerCuff.length ≤ n + 1 := hrow _ (by simp [gm06SuccessorRows])
  have hmul := Nat.mul_le_mul hcuff (Nat.add_le_add_left (Nat.mul_le_mul_left 14 hends) 24)
  have htime : t ≤ 70 * (n + 1) ^ 2 := by
    calc
      t ≤ 10 + 22 * (gm06EncodeSuccessorInput x).length +
          x.innerCuff.length * (24 + 14 * x.endpoints.length) := ht
      _ ≤ 10 + 22 * n + (n + 1) * (24 + 14 * (n + 1)) :=
        Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 22 hsize) 10) hmul
      _ ≤ 70 * (n + 1) ^ 2 := by nlinarith
  exact ⟨s', t, he, htime, hd⟩

end GraphMinor.Compute
