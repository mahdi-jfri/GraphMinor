module

public import GraphMinor.GM16.Defs

/-!
# Closing the design sets under subsets

In the location refinement for XVI (1.3), pages 51–52, restoring an
exceptional edge may add a singleton or empty attachment set after the
exceptional vertices are removed. We close the original design sets
under subsets. This changes no torso: all ends lying in a smaller set
already lie in the original larger set, and an edge cannot have all
its ends in the empty set.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph
universe u v

/-- Close the sets of a design under taking subsets, including the
empty set. The underlying graph is unchanged. -/
def designDownwardClosure {α : Type u} {β : Type v} (d : GraphDesign α β) :
    GraphDesign α β :=
  (d.1, {X | (∃ Y ∈ d.2, X ⊆ Y) ∨ X = ∅})

/-- Closing the design sets under subsets preserves their validity. -/
theorem IsGraphDesign.downwardClosure {α : Type u} {β : Type v}
    {d : GraphDesign α β} (h : IsGraphDesign d) : IsGraphDesign (designDownwardClosure d) := by
  refine ⟨h.1, h.2.1, ?_⟩
  rintro X (⟨Y, hY, hXY⟩ | rfl)
  · exact hXY.trans (h.2.2 hY)
  · exact empty_subset _

/-- Taking downward closure of the design sets changes no torso. -/
theorem isTorsoOfDesign_downwardClosure_iff {α : Type u} {β : Type v}
    {d : GraphDesign α β} {H : Graph α β} :
    IsTorsoOfDesign (designDownwardClosure d) H ↔ IsTorsoOfDesign d H := by
  constructor
  · rintro ⟨hV, hle, hEdges⟩
    refine ⟨hV, hle, ?_⟩
    intro e he
    obtain ⟨X, hX, hEnds⟩ := hEdges e he
    rcases hX with ⟨Y, hY, hXY⟩ | rfl
    · exact ⟨Y, hY, fun x hx => hXY (hEnds x hx)⟩
    · obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet he.1
      exact (notMem_empty x (hEnds x ⟨y, hxy⟩)).elim
  · rintro ⟨hV, hle, hEdges⟩
    refine ⟨hV, hle, ?_⟩
    intro e he
    obtain ⟨X, hX, hEnds⟩ := hEdges e he
    exact ⟨X, Or.inl ⟨X, hX, Subset.refl _⟩, hEnds⟩

/-- A singleton belongs to the downward closure when its vertex is
contained in one of the original attachment sets. -/
theorem singleton_mem_designDownwardClosure {α : Type u} {β : Type v}
    {d : GraphDesign α β} {x : α} (h : ∃ X ∈ d.2, x ∈ X) :
    {x} ∈ (designDownwardClosure d).2 := by
  obtain ⟨X, hX, hx⟩ := h
  exact Or.inl ⟨X, hX, singleton_subset_iff.mpr hx⟩

end GraphMinor.GM16
