module

public import GraphMinor.Compute.GM02RecursiveWordSize
public import GraphMinor.Compute.GM02TerminatedEncoding
import GraphMinor.Compute.GM02BalancedComplexity
import Mathlib.Tactic.Linarith

/-!
# Word bounds for every recursive input below the root size

A simple graph has at most the square of its vertex count many edges,
and a termination uses at most half the vertices. These facts bound the
plain encoding and separator work. The fixed boundary bound similarly
controls the selected child's pair words. All fit the one word size
chosen from width and root size.
-/

public section
namespace GraphMinor.Compute

/-- One root word size supplies every separator, encoding, and selected-child word bound. -/
theorem gm02Recursive_instance_wordBounds (q n w : ℕ) (x : GM02SimpleTerminatedInput)
    (hx : x.n ≤ n) (hw : wordSize (gm02RecursiveWordConstant q) n ≤ w) :
    x.n < 2 ^ w ∧ x.enc.length < 2 ^ w ∧
      2 + 2 * (edgeListOf x.G).length + x.n < 2 ^ w ∧
      3 * x.n < 2 ^ w ∧ x.n + 1 < 2 ^ w ∧ (x.n + 1) ^ q < 2 ^ w ∧
      ∀ k ≤ gm02RecursiveBoundaryBound q,
        8 + 2 * (edgeListOf x.G).length + 2 * k < 2 ^ w := by
  have hc := gm02RecursiveWordConstant_bounds q
  have hword : wordSize (q + 6) x.n ≤ w :=
    (wordSize_mono_right (q + 6) hx).trans ((wordSize_mono_left hc.1 n).trans hw)
  have hm := gm02EdgeList_length_le_sq x.G
  obtain ⟨_, hsep, hn, hb, hp⟩ := gm02Balanced_wordBounds q x.n (edgeListOf x.G).length hm
  have hmono := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hword
  have hsep' := hsep.trans_le hmono
  have hn' := hn.trans_le hmono
  have hb' := hb.trans_le hmono
  have hp' := hp.trans_le hmono
  have henc : x.enc.length < 2 ^ w := by
    have hlen := x.enc_length_le hx
    have hpoly : 3 + 2 * (n * n) + n ≤ (n + 2) ^ 3 := by nlinarith [Nat.zero_le (n * n * n)]
    have hpow : (n + 2) ^ 3 ≤ (n + 2) ^ gm02RecursiveWordConstant q :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact ((hlen.trans hpoly).trans hpow).trans_lt
      ((pow_lt_two_pow_wordSize (by omega : 1 ≤ gm02RecursiveWordConstant q) n).trans_le
        (Nat.pow_le_pow_right (by decide) hw))
  refine ⟨(by omega : x.n < 2 ^ w), henc, hsep', hn', hb', hp', ?_⟩
  intro k hk
  have hmN : (edgeListOf x.G).length ≤ n * n := hm.trans (Nat.mul_le_mul hx hx)
  have hkq : k ≤ 7 * q := hk
  have hsq1 : 1 ≤ (n + 2) ^ 2 := Nat.one_le_pow 2 (n + 2) (by omega)
  have hsqn : n * n ≤ (n + 2) ^ 2 := by nlinarith
  have hpoly : 8 + 2 * (edgeListOf x.G).length + 2 * k ≤ (10 + 14 * q) * (n + 2) ^ 2 := by
    calc
      8 + 2 * (edgeListOf x.G).length + 2 * k ≤ (8 + 14 * q) + 2 * (n * n) := by omega
      _ ≤ (8 + 14 * q) * (n + 2) ^ 2 + 2 * (n + 2) ^ 2 :=
        Nat.add_le_add (Nat.le_mul_of_pos_right _ hsq1) (Nat.mul_le_mul_left _ hsqn)
      _ = (10 + 14 * q) * (n + 2) ^ 2 := by rw [← Nat.add_mul]; congr 1; omega
  exact hpoly.trans_lt (gm02FixedPolynomialWordBound hc.2.2.2.2.2.2.2 hw)

end GraphMinor.Compute
