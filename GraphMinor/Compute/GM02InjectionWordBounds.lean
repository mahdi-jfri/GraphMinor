module

public import GraphMinor.Compute.GM02InjectionSizeBounds
public import GraphMinor.Compute.GM02TopologicalWordBounds
import GraphMinor.Compute.GM02AdditiveWordSize
import GraphMinor.Compute.GM02RecursiveWordSize

/-!
# One logarithmic word size for the complete injection search

Absorb the fixed pattern size in the labelled program's word
coefficient. Fixed linear bounds cover the constructed input, while a
fixed power covers the candidate range. These supply every numerical
word premise of the complete plain-host execution theorem.
-/

public section
namespace GraphMinor.Compute

/-- The word coefficient covers the labelled call, fixed headers, and the injection range. -/
@[expose] noncomputable def gm02InjectionWordCoefficient (q : ℕ) (H : GM02EdgeListInput) : ℕ :=
  gm02TopologicalWordCoefficient q H.edges.length * (H.size + 1) +
    (6 + H.n + 2 * H.edges.length) + (1 + 2 * H.edges.length) + H.n + 8

/-- The common word coefficient is positive, even for an empty pattern. -/
theorem gm02InjectionWordCoefficient_ge_two (q : ℕ) (H : GM02EdgeListInput) :
    2 ≤ gm02InjectionWordCoefficient q H := by unfold gm02InjectionWordCoefficient; omega

/-- All root word premises follow from one fixed logarithmic word size in the plain host size. -/
theorem gm02Injection_wordBounds (q : ℕ) (G H : GM02EdgeListInput) :
    let W := wordSize (gm02InjectionWordCoefficient q H) G.size
    3 < 2 ^ W ∧ G.n + 1 < 2 ^ W ∧ G.edges.length < 2 ^ W ∧
      1 + 2 * H.edges.length < 2 ^ W ∧ gm02InjectedInputLength G H < 2 ^ W ∧
      (G.n + 1) ^ H.n < 2 ^ W ∧
      wordSize (gm02TopologicalWordCoefficient q H.edges.length) (G.size + H.size) ≤ W := by
  let C := gm02InjectionWordCoefficient q H
  let W := wordSize C G.size
  have hc2 : 2 ≤ C := gm02InjectionWordCoefficient_ge_two q H
  have hn : G.n + 1 < 2 ^ W := lt_two_pow_wordSize_of_le (by omega)
    (by unfold GM02EdgeListInput.size; omega)
  have hm : G.edges.length < 2 ^ W := lt_two_pow_wordSize_of_le (by omega)
    (by unfold GM02EdgeListInput.size; omega)
  have h3 : 3 < 2 ^ W := by
    have hc : 3 + 0 + 1 ≤ C := by unfold C gm02InjectionWordCoefficient; omega
    simpa only [pow_zero, Nat.mul_one] using
      (gm02FixedPolynomialWordBound (D := 3) (d := 0) (n := G.size) hc (w := W) le_rfl)
  have hcap : 1 + 2 * H.edges.length < 2 ^ W := by
    have hc : (1 + 2 * H.edges.length) + 0 + 1 ≤ C := by unfold C gm02InjectionWordCoefficient; omega
    simpa only [pow_zero, Nat.mul_one] using
      (gm02FixedPolynomialWordBound (D := 1 + 2 * H.edges.length) (d := 0) (n := G.size) hc (w := W) le_rfl)
  have hlen : gm02InjectedInputLength G H < 2 ^ W := by
    have hlinear := gm02InjectedInputLength_le_linear G H
    have hc : (6 + H.n + 2 * H.edges.length) + 1 + 1 ≤ C := by unfold C gm02InjectionWordCoefficient; omega
    have hbound := gm02FixedPolynomialWordBound (D := 6 + H.n + 2 * H.edges.length)
      (d := 1) (n := G.size) hc (w := W) le_rfl
    simp only [pow_one] at hbound
    exact hlinear.trans_lt ((Nat.mul_le_mul_left _ (Nat.le_succ (G.size + 1))).trans_lt hbound)
  have hpow : (G.n + 1) ^ H.n < 2 ^ W := by
    have hp : H.n ≤ C := by unfold C gm02InjectionWordCoefficient; omega
    have hbase : G.n + 1 ≤ G.size + 2 := by unfold GM02EdgeListInput.size; omega
    exact ((Nat.pow_le_pow_left hbase H.n).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ G.size + 2) hp)).trans_lt (pow_lt_two_pow_wordSize (by omega) G.size)
  have hcall : wordSize (gm02TopologicalWordCoefficient q H.edges.length) (G.size + H.size) ≤ W := by
    have hc : gm02TopologicalWordCoefficient q H.edges.length * (H.size + 1) ≤ C := by
      unfold C gm02InjectionWordCoefficient
      omega
    exact (gm02WordSize_add_le _ G.size H.size).trans (wordSize_mono_left hc G.size)
  exact ⟨h3, hn, hm, hcap, hlen, hpow, hcall⟩

end GraphMinor.Compute
