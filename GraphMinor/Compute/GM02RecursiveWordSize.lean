module

public import GraphMinor.Compute.GM02RecursiveMemory
public import GraphMinor.Compute.GM02SavedFrameBounds

/-!
# A common logarithmic word size for the recursion

The width parameter fixes the exhaustive-table bounds and catalogue
range. Include those constants in one word-size coefficient. The same
coefficient covers the fifth-power stack-capacity bound and polynomial
words in the root vertex count. It therefore serves every smaller
recursive instance without changing the machine's word size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A fixed coefficient covering the recursive machine's width-dependent constants. -/
noncomputable def gm02RecursiveWordConstant (q : ℕ) : ℕ :=
  (4 + 2 * ((4 * q) * (4 * q)) + 4 * q) +
    (gm02RecursiveBoundaryBound q * gm02RecursiveBoundaryBound q + gm02RecursiveBoundaryBound q + 2) +
    (3 + 3 * gm02RecursiveBoundaryBound q) + gm02RecursiveCodeBound q + 20 * q + 40

/-- A fixed coefficient and exponent fit a logarithmic word size depending only on them. -/
theorem gm02FixedPolynomialWordBound {D d c n w : ℕ} (hc : D + d + 1 ≤ c)
    (hw : wordSize c n ≤ w) : D * (n + 2) ^ d < 2 ^ w := by
  have hD : D ≤ (n + 2) ^ D := (Nat.le_of_lt (Nat.lt_two_pow_self (n := D))).trans
    (Nat.pow_le_pow_left (by omega) D)
  have hprod : D * (n + 2) ^ d ≤ (n + 2) ^ (D + d) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hD
  have hp : (n + 2) ^ (D + d) ≤ (n + 2) ^ c :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact ((hprod.trans hp).trans_lt (pow_lt_two_pow_wordSize (by omega) n)).trans_le
    (Nat.pow_le_pow_right (by decide) hw)

/-- The common coefficient exceeds the separator exponent and all fixed boundary bounds. -/
theorem gm02RecursiveWordConstant_bounds (q : ℕ) :
    q + 6 ≤ gm02RecursiveWordConstant q ∧ 5 ≤ gm02RecursiveWordConstant q ∧
      4 + 2 * ((4 * q) * (4 * q)) + 4 * q ≤ gm02RecursiveWordConstant q ∧
      gm02RecursiveBoundaryBound q * gm02RecursiveBoundaryBound q + gm02RecursiveBoundaryBound q + 2 ≤
        gm02RecursiveWordConstant q ∧
      3 + 3 * gm02RecursiveBoundaryBound q ≤ gm02RecursiveWordConstant q ∧
      gm02RecursiveCodeBound q + 1 ≤ gm02RecursiveWordConstant q ∧
      gm02RecursiveBoundaryBound q + 1 ≤ gm02RecursiveWordConstant q ∧
      (10 + 14 * q) + 2 + 1 ≤ gm02RecursiveWordConstant q := by
  unfold gm02RecursiveWordConstant gm02RecursiveBoundaryBound
  omega

/-- All fixed table bounds, catalogue words, and stack cursors fit one root-size word range. -/
theorem gm02Recursive_fixed_wordBounds (q n w : ℕ)
    (hw : wordSize (gm02RecursiveWordConstant q) n ≤ w) :
    4 < 2 ^ w ∧ (4 + 2 * ((4 * q) * (4 * q)) + 4 * q) < 2 ^ w ∧
      gm02RecursiveBoundaryBound q * gm02RecursiveBoundaryBound q + gm02RecursiveBoundaryBound q + 2 < 2 ^ w ∧
      3 + 3 * gm02RecursiveBoundaryBound q < 2 ^ w ∧ gm02RecursiveCodeBound q + 1 < 2 ^ w ∧
      gm02RecursiveBoundaryBound q + 1 < 2 ^ w ∧ 2 ^ gm02RecursiveCodeBound q ≤ 2 ^ w ∧
      gm02SavedFrameCapacity n < 2 ^ w := by
  have hb := gm02RecursiveWordConstant_bounds q
  have hcw : gm02RecursiveWordConstant q ≤ w := by
    apply le_trans _ hw
    unfold wordSize
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hfixed : gm02RecursiveWordConstant q < 2 ^ w :=
    (Nat.lt_two_pow_self (n := gm02RecursiveWordConstant q)).trans_le
      (Nat.pow_le_pow_right (by decide) hcw)
  refine ⟨(by omega : 4 ≤ gm02RecursiveWordConstant q).trans_lt hfixed,
    hb.2.2.1.trans_lt hfixed, hb.2.2.2.1.trans_lt hfixed,
    hb.2.2.2.2.1.trans_lt hfixed, hb.2.2.2.2.2.1.trans_lt hfixed,
    hb.2.2.2.2.2.2.1.trans_lt hfixed, ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact (gm02SavedFrameCapacity_lt_wordSize hb.2.1 n).trans_le
      (Nat.pow_le_pow_right (by decide) hw)

end GraphMinor.Compute
