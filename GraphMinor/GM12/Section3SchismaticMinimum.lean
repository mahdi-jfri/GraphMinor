module

public import GraphMinor.GM12.Section3SchismaticCandidate
public import GraphMinor.GM12.Section3Alpha

/-!
# Attaining alpha on a schismatic set

The alternative definition in VII Section 8, page 241, used by XII
(3.1), page 245, is an equality of minima. Choose an alpha candidate
of minimum vertex count and extract a normal schismatic subset. Its
count cannot increase under inclusion. Conversely, the schismatic
subset is an alpha candidate, so its count cannot fall below alpha.
This proves equality, with the extraction input kept explicit.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Once the Section 8 extraction step is available, the minimum
alpha is attained on a normal schismatic set. This proves both count
inequalities, rather than assuming the alternative minimum. -/
theorem exists_normal_schismatic_at_alpha_of_extraction
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (G : Drawing S) (hex : ∃ X : Set S, GM07.IsAlphaCandidate G X)
    (hcontains : ∀ X : Set S, GM07.IsAlphaCandidate G X →
      ∃ Y : Set S, Y ⊆ X ∧ GM07.IsSchismatic Y ∧ G.IsNormal Y) :
    ∃ Y : Set S, GM07.IsSchismatic Y ∧ G.IsNormal Y ∧
      (Y ∩ G.V).ncard = GM07.alpha G := by
  obtain ⟨X, hX, hcount⟩ := exists_alpha_candidate_at_minimum G hex
  obtain ⟨Y, hYX, hY, hn⟩ := hcontains X hX
  have hle : (Y ∩ G.V).ncard ≤ GM07.alpha G := by
    rw [← hcount]
    exact Set.ncard_le_ncard (inter_subset_inter_left G.V hYX)
      (G.finite_V.subset inter_subset_right)
  exact ⟨Y, hY, hn, hle.antisymm (alpha_le_normal_schismatic_count hY hn)⟩

/-- The exact alternative minimum in VII Section 8 after extraction.
Candidate existence is retained because the natural-number infimum of
an empty candidate family is zero in the library definition. -/
theorem alpha_eq_schismatic_minimum_of_extraction
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (G : Drawing S) (hex : ∃ X : Set S, GM07.IsAlphaCandidate G X)
    (hcontains : ∀ X : Set S, GM07.IsAlphaCandidate G X →
      ∃ Y : Set S, Y ⊆ X ∧ GM07.IsSchismatic Y ∧ G.IsNormal Y) :
    GM07.alpha G = sInf {n : ℕ | ∃ Y : Set S,
      GM07.IsSchismatic Y ∧ G.IsNormal Y ∧ (Y ∩ G.V).ncard = n} := by
  obtain ⟨Y, hY, hn, hc⟩ := exists_normal_schismatic_at_alpha_of_extraction G hex hcontains
  apply Nat.le_antisymm
  · have hne : {n : ℕ | ∃ Z : Set S, GM07.IsSchismatic Z ∧ G.IsNormal Z ∧
        (Z ∩ G.V).ncard = n}.Nonempty := ⟨(Y ∩ G.V).ncard, Y, hY, hn, rfl⟩
    obtain ⟨Z, hZ, hZn, hZcount⟩ := csInf_mem hne
    exact (alpha_le_normal_schismatic_count hZ hZn).trans_eq hZcount
  · rw [← hc]
    exact Nat.sInf_le ⟨Y, hY, hn, rfl⟩

end GraphMinor.GM12
