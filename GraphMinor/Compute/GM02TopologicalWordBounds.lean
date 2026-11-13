module

public import GraphMinor.Compute.GM02FullPortGraph
public import GraphMinor.Compute.GM02RecursiveWordSize
public import GraphMinor.Compute.GM02AdditiveWordSize
import GraphMinor.Compute.GM02TopologicalBasicWords
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One logarithmic word size for the topological decision program

The numeric split graph adds only `2K` positions to the supplied host
size. Absorb this fixed shift in the recursive machine's logarithmic
word coefficient. A fixed quadratic bound covers all constructed input
arrays, while the candidate range has the fixed exponent `2K`. These
bounds supply every numerical premise of the complete execution theorem.
-/

public section
namespace GraphMinor.Compute

/-- The fixed word coefficient covering the shifted path machine, constructed arrays, and candidate range. -/
@[expose] noncomputable def gm02TopologicalWordCoefficient (q K : ℕ) : ℕ :=
  gm02RecursiveWordConstant q * (2 * K + 1) + (5 + 2 * (2 * K + 1) ^ 2) + 2 * K + 6

/-- The common coefficient also covers the plain-input preprocessing bounds. -/
theorem gm02TopologicalWordCoefficient_ge_two (q K : ℕ) : 2 ≤ gm02TopologicalWordCoefficient q K := by
  unfold gm02TopologicalWordCoefficient
  omega

private theorem join_polynomial_bound (s K N m : ℕ) (hN : N ≤ s + 2 * K) (hm : m ≤ s) :
    3 + 2 * (N * N) + 2 * m ≤ (5 + 2 * (2 * K + 1) ^ 2) * (s + 2) ^ 2 := by
  have hlinear : N ≤ (2 * K + 1) * (s + 2) := by nlinarith [Nat.zero_le (K * s)]
  have hsq := Nat.mul_le_mul hlinear hlinear
  nlinarith [Nat.zero_le (s * s)]

/-- Every word premise of the complete plain-input decision program follows from one fixed logarithmic word size. -/
theorem gm02Topological_wordBounds (q K : ℕ) (x : GM02TopologicalInput) :
    let W := wordSize (gm02TopologicalWordCoefficient q K) (gm02TopologicalSize x)
    3 < 2 ^ W ∧ gm02TopologicalSize x < 2 ^ W ∧ x.enc.length < 2 ^ W ∧
      gm02FullPortSize x K < 2 ^ W ∧ x.G.edges.length + 1 < 2 ^ W ∧
      (x.G.edges.length + 1) ^ (2 * K) < 2 ^ W ∧
      3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length < 2 ^ W ∧
      wordSize (gm02RecursiveWordConstant q) (gm02FullPortSize x K) ≤ W := by
  let s := gm02TopologicalSize x
  let C := gm02TopologicalWordCoefficient q K
  let W := wordSize C s
  have hNadd : gm02FullPortSize x K ≤ s + 2 * K := by
    unfold gm02FullPortSize s gm02TopologicalSize GM02EdgeListInput.size
    omega
  have hGsize : x.G.edges.length ≤ s := by unfold s gm02TopologicalSize GM02EdgeListInput.size; omega
  have hHsize : x.edges.length ≤ s := by unfold s gm02TopologicalSize; omega
  have hc2 : 2 ≤ C := gm02TopologicalWordCoefficient_ge_two q K
  have hscale : gm02RecursiveWordConstant q * (2 * K + 1) ≤ C := by
    unfold C gm02TopologicalWordCoefficient
    omega
  have hmachine : wordSize (gm02RecursiveWordConstant q) (gm02FullPortSize x K) ≤ W :=
    (gm02WordSize_le_of_le_add (gm02RecursiveWordConstant q) s (2 * K) hNadd).trans
      (wordSize_mono_left hscale s)
  have hfour := (gm02Recursive_fixed_wordBounds q (gm02FullPortSize x K) W hmachine).1
  obtain ⟨_, hsize, _, henc⟩ := gm02Topological_basicWordBounds x C hc2
  have hcR : 1 ≤ gm02RecursiveWordConstant q := by
    have h := (gm02RecursiveWordConstant_bounds q).2.1
    omega
  have hN : gm02FullPortSize x K < 2 ^ W :=
    (lt_two_pow_wordSize_of_le (c := gm02RecursiveWordConstant q) hcR (Nat.le_succ (gm02FullPortSize x K))).trans_le
      (Nat.pow_le_pow_right (by decide) hmachine)
  have hM : x.G.edges.length + 1 < 2 ^ W := lt_two_pow_wordSize_of_le (by omega) (by omega)
  have hExp : 2 * K ≤ C := by unfold C gm02TopologicalWordCoefficient; omega
  have hpow : (x.G.edges.length + 1) ^ (2 * K) < 2 ^ W :=
    ((Nat.pow_le_pow_left (by omega : x.G.edges.length + 1 ≤ s + 2) (2 * K)).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ s + 2) hExp)).trans_lt (pow_lt_two_pow_wordSize (by omega) s)
  have hjoin := join_polynomial_bound s K (gm02FullPortSize x K) x.edges.length hNadd hHsize
  have hcoef : (5 + 2 * (2 * K + 1) ^ 2) + 2 + 1 ≤ C := by
    unfold C gm02TopologicalWordCoefficient
    omega
  have hjoinword : 3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length < 2 ^ W :=
    hjoin.trans_lt (gm02FixedPolynomialWordBound hcoef le_rfl)
  exact ⟨(by decide : 3 < 4).trans hfour, hsize, henc, hN, hM, hpow, hjoinword, hmachine⟩

end GraphMinor.Compute
