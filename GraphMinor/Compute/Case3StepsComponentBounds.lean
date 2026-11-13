module

public import GraphMinor.Compute.Case3StepsCoreMath
public import GraphMinor.Compute.Case3StepsDecodedComponents

/-!
# Bounds for the compact component computation

Compact numbering uses no more vertices or active pairs than the original
input. Thus the component table and its searches fit the time and word bounds
of the case (iii) loop of XIII (9.9), page 104.
-/

public section

namespace GraphMinor.Compute

/-- The compact compass has at most the input's number of active pairs. -/
theorem case3CompactCompass_numActivePairs_le {h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h (G.deleteVertices X))
    (hdisj : Disjoint W.compassFinset X) :
    (case3CompactCompassMultigraph (G.deleteVertices X) W).numActivePairs ≤ G.numActivePairs := by
  have heq := congrArg List.length (case3CompactCompass_enc_eq_of_deleteVertices G X W hdisj)
  rw [MultiDigraph.length_enc, MultiDigraph.length_enc] at heq
  have hc : (case3CompactCompassMultigraph (G.deleteVertices X) W).numActivePairs =
      (G.deleteVerticesCompact W.compassFinsetᶜ).numActivePairs := by omega
  rw [hc, G.numActivePairs_deleteVerticesCompact]
  exact G.numActivePairs_deleteVertices_le _

/-- The component computation is linear in the case (iii) size parameter. -/
theorem case3Component_cost_le {k a n e : ℕ} (hk : k ≤ n) (ha : a ≤ e) :
    k * k + k * (38 * k + 52 * a + 47) + 87 * k + 236 * a + 148 ≤
      1000 * ((n + 1) * (e + n + 1)) := by
  have hkk := Nat.mul_le_mul hk hk
  have hka := Nat.mul_le_mul hk ha
  nlinarith [Nat.zero_le (n * e), Nat.zero_le (n * n)]

/-- The square component table fits the same polynomial word bound. -/
theorem case3Component_square_le {k n e : ℕ} (hk : k ≤ n) :
    k * k ≤ (n + 1) * (e + n + 1) := by
  have hkk := Nat.mul_le_mul hk hk
  nlinarith [Nat.zero_le (n * e)]

/-- Cubic headroom covers the fixed words and linear graph counters. -/
theorem case3Component_word_bounds {k a n e N w : ℕ}
    (hk : k ≤ n) (ha : a ≤ e) (hsize : n + e + 1 ≤ N)
    (hcube : (N + 2) ^ 3 < 2 ^ w) :
    3 < 2 ^ w ∧ k + 1 < 2 ^ w ∧ k * k < 2 ^ w ∧ 2 + 3 * a < 2 ^ w := by
  have hN : N < 2 ^ w := by nlinarith [Nat.zero_le (N ^ 3)]
  have hsquare : k * k ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  refine ⟨?_, by omega, ?_, ?_⟩
  · nlinarith [Nat.zero_le (N ^ 3)]
  · nlinarith [Nat.zero_le (N ^ 3)]
  · nlinarith [Nat.zero_le (N ^ 3)]

/-- Fixed-size key rows fit the same cubic word headroom as the components. -/
theorem case3Attachment_word_bounds {k n e N w : ℕ}
    (hk : k ≤ n) (hsize : n + e + 1 ≤ N) (hcube : (N + 2) ^ 3 < 2 ^ w) :
    4 < 2 ^ w ∧ k * 4 < 2 ^ w := by
  constructor <;> nlinarith [Nat.zero_le (N ^ 3)]

/-- Computing the attachment-key table fits the case (iii) size parameter. -/
theorem case3AttachmentKeys_cost_le {k m n e : ℕ} (hk : k ≤ n) (hm : m ≤ e) :
    k * 4 + k * (76 * k + 19 * (2 * m) + 125) + 10 ≤
      1000 * ((n + 1) * (e + n + 1)) := by
  have hkk := Nat.mul_le_mul hk hk
  have hkm := Nat.mul_le_mul hk hm
  nlinarith [Nat.zero_le (n * e), Nat.zero_le (n * n)]

/-- Group-label words fit under the same cubic headroom. -/
theorem case3GroupLabels_word_bound {k a n e N w : ℕ}
    (hk : k ≤ n) (ha : a ≤ e) (hsize : n + e + 1 ≤ N)
    (hcube : (N + 2) ^ 3 < 2 ^ w) : k + a < 2 ^ w := by
  nlinarith [Nat.zero_le (N ^ 3)]

/-- Component and core-edge grouping together fit the case (iii) size bound. -/
theorem case3GroupLabels_cost_le {k a n e : ℕ} (hk : k ≤ n) (ha : a ≤ e) :
    k + k * (56 * k + 103) + a * (56 * k + 154) + 100 ≤
      1000 * ((n + 1) * (e + n + 1)) := by
  have hkk := Nat.mul_le_mul hk hk
  have hka := Nat.mul_le_mul hk ha
  nlinarith [Nat.zero_le (n * e), Nat.zero_le (n * n)]

end GraphMinor.Compute
