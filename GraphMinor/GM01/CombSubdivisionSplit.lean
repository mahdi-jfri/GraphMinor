module

public import GraphMinor.GM01.CombShiftRanges
import GraphMinor.GM01.CombIntervalBoundary

/-!
# Splitting a subdivided comb at a cell boundary

The fork contraction in Graph Minors I, (4.12), page 59, keeps the
second end separate from the other cells. Every vertex of the
subdivision is in the initial segment, the final segment, or the
single replacing path between them. For a replacing path this follows
by locating its two source ends. If they lie on different sides,
the source edge is the unique spine edge across the boundary.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The two cell intervals and their boundary replacing path cover the
whole represented comb, as used in GM01 (4.12), page 59. -/
theorem comb_subdivision_split_cover {α β : Type*} {γ L k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) (hsum : k + m = L)
    {D : Graph α β} (c : (pathComb γ L).verts → α)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (edge : (pathComb γ L).coe.edgeSet)
    (hEdge : edge.val = s(⟨Sum.inl ⟨k - 1, by omega⟩, pathComb_spine_mem γ L _⟩,
      ⟨Sum.inl ⟨k, by omega⟩, pathComb_spine_mem γ L _⟩)) :
    V(D) ⊆ combSegmentSupport c P 0 (by omega : 0 + k ≤ L) ∪ V(P edge) ∪
      combSegmentSupport c P k (by omega : k + m ≤ L) := by
  have hkL : k < L := by omega
  have hcentre : ∀ v : (pathComb γ L).verts, c v ∈
      combSegmentSupport c P 0 (by omega : 0 + k ≤ L) ∪
      combSegmentSupport c P k (by omega : k + m ≤ L) := by
    intro v
    have hv := (pathCombSpineIndex v.val).isLt
    by_cases hlo : (pathCombSpineIndex v.val).val < k
    · exact Or.inl ((mem_combSegmentSupport_iff c P 0 (by omega) _).mpr
        (Or.inl ⟨v, Nat.zero_le _, by omega, rfl⟩))
    · exact Or.inr ((mem_combSegmentSupport_iff c P k (by omega) _).mpr
        (Or.inl ⟨v, by omega, by omega, rfl⟩))
  intro x hx
  rw [hV] at hx
  rcases hx with ⟨v, rfl⟩ | hx
  · rcases hcentre v with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · obtain ⟨e, hx⟩ := mem_iUnion.mp hx
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | hf a b =>
      have haL := (pathCombSpineIndex a.val).isLt
      have hbL := (pathCombSpineIndex b.val).isLt
      by_cases ha : (pathCombSpineIndex a.val).val < k
      · by_cases hb : (pathCombSpineIndex b.val).val < k
        · exact Or.inl (Or.inl (path_subset_combSegmentSupport c P 0 (by omega)
            ⟨s(a,b), he⟩ rfl ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ hx))
        · have hcross := pathComb_adj_crosses_interval_boundary hk hkL (a := a.val) (b := b.val) he ha (by omega)
          have haeq : a = ⟨Sum.inl ⟨k - 1, by omega⟩, pathComb_spine_mem γ L _⟩ :=
            Subtype.ext hcross.1
          have hbeq : b = ⟨Sum.inl ⟨k, hkL⟩, pathComb_spine_mem γ L _⟩ :=
            Subtype.ext hcross.2
          have heq : (⟨s(a,b), he⟩ : (pathComb γ L).coe.edgeSet) = edge := by
            apply Subtype.ext
            change s(a,b) = edge.val
            rw [hEdge, haeq, hbeq]
          exact Or.inl (Or.inr (by rw [← heq]; exact hx))
      · by_cases hb : (pathCombSpineIndex b.val).val < k
        · have hcross := pathComb_adj_crosses_interval_boundary hk hkL (a := b.val) (b := a.val)
            ((pathComb γ L).coe.adj_symm he) hb (by omega)
          have hbeq : b = ⟨Sum.inl ⟨k - 1, by omega⟩, pathComb_spine_mem γ L _⟩ :=
            Subtype.ext hcross.1
          have haeq : a = ⟨Sum.inl ⟨k, hkL⟩, pathComb_spine_mem γ L _⟩ :=
            Subtype.ext hcross.2
          have heq : (⟨s(a,b), he⟩ : (pathComb γ L).coe.edgeSet) = edge := by
            apply Subtype.ext
            change s(a,b) = edge.val
            rw [hEdge, haeq, hbeq, Sym2.eq_swap]
          exact Or.inl (Or.inr (by rw [← heq]; exact hx))
        · exact Or.inr (path_subset_combSegmentSupport c P k (by omega)
            ⟨s(a,b), he⟩ rfl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hx)

end GraphMinor.GM01
