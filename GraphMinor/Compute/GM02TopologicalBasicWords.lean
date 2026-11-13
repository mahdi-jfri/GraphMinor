module

public import GraphMinor.Compute.GM02TopologicalEncoding

/-!
# Logarithmic word bounds for topological preprocessing

The plain input contains two endpoint words per edge and one word per
pattern vertex, plus four header words. Its length is at most twice the
total graph size plus four. A logarithmic word constant of at least two
therefore covers the entire input and all preprocessing counts.
-/

public section
namespace GraphMinor.Compute

/-- One logarithmic word bound covers all plain-input counts and array offsets used by preprocessing. -/
theorem gm02Topological_basicWordBounds (x : GM02TopologicalInput) (c : ℕ) (hc : 2 ≤ c) :
    2 < 2 ^ wordSize c (gm02TopologicalSize x) ∧
      gm02TopologicalSize x < 2 ^ wordSize c (gm02TopologicalSize x) ∧
      x.G.n < 2 ^ wordSize c (gm02TopologicalSize x) ∧
      x.enc.length < 2 ^ wordSize c (gm02TopologicalSize x) := by
  have htwo := two_mul_lt_two_pow_wordSize (n := gm02TopologicalSize x) hc
  have hsize := lt_two_pow_wordSize_of_le (n := gm02TopologicalSize x) (c := c) (k := gm02TopologicalSize x)
    (by omega) (Nat.le_succ _)
  have hn : x.G.n ≤ gm02TopologicalSize x + 1 := by
    unfold gm02TopologicalSize GM02EdgeListInput.size
    omega
  have hnw := lt_two_pow_wordSize_of_le (c := c) (by omega) hn
  have hlen : x.enc.length ≤ 2 * (gm02TopologicalSize x + 2) := by
    rw [x.enc_length]
    unfold gm02TopologicalSize GM02EdgeListInput.size
    omega
  exact ⟨by omega, hsize, hnw, hlen.trans_lt htwo⟩

end GraphMinor.Compute
