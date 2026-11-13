module

public import GraphMinor.GM01.CleanBypass

/-!
# The endpoint blocks of a clean bypass

If a proposed block separator fails in Graph Minors I, (4.1), page 55,
the clean bypass has one end in an earlier block and the other in a
later block. Coverage by the finite block family supplies the three-set
cover used by the trimming lemma. Membership in each indexed union
then supplies the two endpoint indices.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The indexed clean-bypass assertion at the start of the proof of
Graph Minors I, (4.1), page 55. It applies to the proved comb-block
partition without assuming any separator conclusion. -/
theorem exists_block_bypass_of_not_separates {α β : Type*} {n : ℕ}
    {G H : Graph α β} (S : Fin n → Set α) (hcover : (⋃ i, S i) = V(H))
    (j : Fin n)
    (hno : ¬ GraphSeparates G (S j) (⋃ i, ⋃ (_ : i < j), S i)
      (⋃ i, ⋃ (_ : j < i), S i)) :
    ∃ i : Fin n, i < j ∧ ∃ k : Fin n, j < k ∧
      ∃ a ∈ S i, ∃ b ∈ S k, ∃ P : Graph α β,
        IsGraphPathWithEnds G P a b ∧ Disjoint V(P) (S j) ∧
        V(P) ∩ V(H) = {a,b} := by
  have hsub : ∀ i, S i ⊆ V(H) := by
    intro i x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hA : (⋃ i, ⋃ (_ : i < j), S i) ⊆ V(H) := by
    intro x hx
    obtain ⟨i, hx⟩ := mem_iUnion.mp hx
    obtain ⟨_, hx⟩ := mem_iUnion.mp hx
    exact hsub i hx
  have hB : (⋃ i, ⋃ (_ : j < i), S i) ⊆ V(H) := by
    intro x hx
    obtain ⟨i, hx⟩ := mem_iUnion.mp hx
    obtain ⟨_, hx⟩ := mem_iUnion.mp hx
    exact hsub i hx
  have hThree : V(H) ⊆ (⋃ i, ⋃ (_ : i < j), S i) ∪ S j ∪
      (⋃ i, ⋃ (_ : j < i), S i) := by
    intro x hx
    rw [← hcover] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hij, hi⟩⟩))
    · exact Or.inl (Or.inr hi)
    · exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hji, hi⟩⟩)
  obtain ⟨a, ha, b, hb, P, hP, havoid, hmeet⟩ :=
    exists_clean_bypass_of_not_graphSeparates hA hB hThree hno
  obtain ⟨i, ha⟩ := mem_iUnion.mp ha
  obtain ⟨hij, ha⟩ := mem_iUnion.mp ha
  obtain ⟨k, hb⟩ := mem_iUnion.mp hb
  obtain ⟨hjk, hb⟩ := mem_iUnion.mp hb
  exact ⟨i, hij, k, hjk, a, ha, b, hb, P, hP, havoid, hmeet⟩

end GraphMinor.GM01
