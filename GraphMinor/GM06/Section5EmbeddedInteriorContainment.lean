module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# A region cannot cross an embedded boundary

For the one-path enclosures in VI (5.5), page 130, embed the cut
disc in the sphere. Its open interior image and the complement
of its closed image are disjoint open sets separated by the boundary.
A preconnected set missing that boundary and meeting the embedded
disc must stay in its interior image.
-/

public section
namespace GraphMinor.GM06
open Set Topology

/-- A preconnected set missing an embedded boundary and meeting
the closed embedded space stays in its open interior image. -/
theorem subset_embedded_interior_of_preconnected
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {j : X → Y} (hj : IsClosedEmbedding j) {B : Set X}
    (hopen : IsOpen (j '' Bᶜ)) {C : Set Y} (hC : IsPreconnected C)
    (hmiss : Disjoint C (j '' B)) (hmeet : (C ∩ range j).Nonempty) :
    C ⊆ j '' Bᶜ := by
  have hcover : C ⊆ (j '' Bᶜ) ∪ (range j)ᶜ := by
    intro y hy
    by_cases hyr : y ∈ range j
    · obtain ⟨x, rfl⟩ := hyr
      exact Or.inl ⟨x, fun hx => disjoint_left.mp hmiss hy (mem_image_of_mem _ hx), rfl⟩
    · exact Or.inr hyr
  have hdis : Disjoint (j '' Bᶜ) (range j)ᶜ := by
    apply disjoint_left.mpr
    rintro y ⟨x, _, rfl⟩ hn
    exact hn (mem_range_self x)
  rcases hC.subset_or_subset hopen hj.isClosed_range.isOpen_compl hdis hcover with h | h
  · exact h
  · obtain ⟨x, hxC, hxr⟩ := hmeet
    exact False.elim (h hxC hxr)

end GraphMinor.GM06
