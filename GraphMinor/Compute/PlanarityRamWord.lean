module

public import GraphMinor.Compute.Basic

/-!
# A logarithmic word bound for linear arenas

A fixed linear multiple of the input size fits in logarithmic words by
increasing the constant multiplying the logarithm. This accommodates the
solver's word constant as well as all search and bucket capacities.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- A word constant depending only on A addresses A times the input size. -/
theorem linear_word_bound (A size w : ℕ) (hw : wordSize (A + 2) size ≤ w) :
    A * size < 2 ^ w := by
  have ha : A ≤ (size + 2) ^ A :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := A))).trans (Nat.pow_le_pow_left (by omega) A)
  have hs : size ≤ (size + 2) ^ 2 :=
    (Nat.le_add_right size 2).trans (Nat.le_self_pow (by decide) (size + 2))
  have hprod : A * size ≤ (size + 2) ^ (A + 2) := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul ha hs
  have hbound := lt_two_pow_wordSize_of_lt_pow (c := A + 2) (n := size) (by omega) hprod
  exact Nat.lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by decide) hw)

/-- The handshaking relation converts the solver's incidence-size bound
and the bucket capacity bound to the graph-size logarithmic convention. -/
theorem assembly_word_bounds (K E N M w : ℕ) (hM : M = 2 * E)
    (hw : wordSize (2 * K + 6) (E + N + 1) ≤ w) :
    wordSize 2 (E + N + 1) ≤ w ∧
    2 * (N + M + 1) < 2 ^ w ∧ K * (N + M + 1) < 2 ^ w := by
  have hlarge : (2 * K + 4) * (E + N + 1) < 2 ^ w :=
    linear_word_bound (2 * K + 4) (E + N + 1) w hw
  have hsize : N + M + 1 ≤ 2 * (E + N + 1) := by omega
  have hK := Nat.mul_le_mul_left K hsize
  have hsmall := Nat.mul_le_mul_right (E + N + 1) (show 2 * K ≤ 2 * K + 4 by omega)
  refine ⟨(wordSize_mono_left (by omega) _).trans hw, ?_, ?_⟩
  · have hfour := Nat.mul_le_mul_right (E + N + 1) (show 4 ≤ 2 * K + 4 by omega)
    omega
  · rw [← Nat.mul_assoc] at hK
    exact Nat.lt_of_le_of_lt (hK.trans (by simpa only [Nat.mul_comm K 2] using hsmall)) hlarge

end GraphMinor.Compute.PlanarityRam
