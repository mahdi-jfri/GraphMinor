module

public import GraphMinor.RST94.Section5f

/-!
# A two by two grid with the column rank condition

The proved grid-set theorem of Robertson, Seymour and Thomas applies to sizes
at least three. For size two, merge the last two rows of a three by three grid
and retain its first two columns. Each new column contains the whole old
column, so its tangle rank is still at least two.
-/

public section

namespace GraphMinor.GM10

open Hypergraph RST94 Set

universe u v

/-- Merge the last two rows of a three by three grid-set family. The column
rank condition is preserved because no vertex in either retained column is lost. -/
theorem hasGrid_two_of_three {α : Type u} {β : Type v} {G : Hypergraph α β}
    {T : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (hT : IsTangle G θ T) (h : HasGrid G T θ 3) : HasGrid G T θ 2 := by
  obtain ⟨W, hW⟩ := h
  let U : ℕ → ℕ → Set α := fun i j => if i = 0 then W 0 j else W 1 j ∪ W 2 j
  have hmem : ∀ {i j x}, i < 2 → j < 2 → x ∈ U i j →
      ∃ a, a < 3 ∧ (if i = 0 then a = 0 else a = 1 ∨ a = 2) ∧ x ∈ W a j := by
    intro i j x hi hj hx
    by_cases hzero : i = 0
    · exact ⟨0, by omega, by simp [hzero], by simpa [U, hzero] using hx⟩
    · rcases (show x ∈ W 1 j ∪ W 2 j from by simpa [U, hzero] using hx) with hx | hx
      · exact ⟨1, by omega, by simp [hzero], hx⟩
      · exact ⟨2, by omega, by simp [hzero], hx⟩
  refine ⟨U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj x hx
    obtain ⟨a, ha, -, hx⟩ := hmem hi hj hx
    exact hW.sub a ha j (by omega) hx
  · intro i hi j hj
    by_cases hz : i = 0
    · simpa [U, hz] using hW.conn 0 (by omega) j (by omega)
    · obtain ⟨x, hx, y, hy, hxy⟩ := hW.col 1 (by omega) j (by omega)
      simpa [U, hz] using (hW.conn 1 (by omega) j (by omega)).union_adj
        (hW.conn 2 (by omega) j (by omega)) hx hy hxy
  · intro i hi j hj i' hi' j' hj' hne
    refine disjoint_left.2 ?_
    intro x hx hx'
    obtain ⟨a, ha, hai, hx⟩ := hmem hi hj hx
    obtain ⟨a', ha', hai', hx'⟩ := hmem hi' hj' hx'
    apply disjoint_left.1 (hW.disj a ha j (by omega) a' ha' j' (by omega) ?_) hx hx'
    intro heq
    have haa := (Prod.ext_iff.1 heq).1
    have hjj := (Prod.ext_iff.1 heq).2
    apply hne
    have hii : i = i' := by
      split_ifs at hai hai' <;> omega
    exact congrArg₂ Prod.mk hii (show j = j' from hjj)
  · intro i hi j hj
    have hj0 : j = 0 := by omega
    subst j
    by_cases hz : i = 0
    · simpa [U, hz] using hW.row 0 (by omega) 0 (by omega)
    · obtain ⟨x, hx, y, hy, hxy⟩ := hW.row 1 (by omega) 0 (by omega)
      exact ⟨x, by simp [U, hz, hx], y, by simp [U, hz, hy], hxy⟩
  · intro i hi j hj
    have hi0 : i = 0 := by omega
    subst i
    obtain ⟨x, hx, y, hy, hxy⟩ := hW.col 0 (by omega) j (by omega)
    exact ⟨x, by simpa [U] using hx, y, by simp [U, hy], hxy⟩
  · intro j hj
    apply (show 2 ≤ 3 by omega).trans ((hW.rank j (by omega)).trans (tangleRank_mono hT ?_))
    intro x hx
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.1 hx
    by_cases hz : i = 0
    · exact mem_iUnion₂.2 ⟨0, (show 0 < 2 by omega), by simpa [U, hz] using hx⟩
    · refine mem_iUnion₂.2 ⟨1, (show 1 < 2 by omega), ?_⟩
      have hi' : i = 1 ∨ i = 2 := by change i < 3 at hi; omega
      rcases hi' with rfl | rfl <;> simp [U, hx]

end GraphMinor.GM10
