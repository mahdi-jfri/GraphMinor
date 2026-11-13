module

public import GraphMinor.GM16.Defs
import GraphMinor.Surface.DiscArcs
import GraphMinor.GM14.Section7a

/-!
# Vertices on the arrangement discs

In the torso assembly of XVI (1.3), page 51, the drawn graph uses the
society boundary vertices. Such a vertex lies in a society disc exactly
when it belongs to that society's boundary. Properness also makes the
boundary sets of distinct large societies disjoint.
-/

public section
namespace GraphMinor.GM16
open Set Surface GM09 GM14
universe u v w

/-- An arranged boundary vertex belongs to the closed society disc. -/
theorem arrangement_pt_mem_disc
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} {𝒮 : Set (Society α β)}
    {disc : Society α β → Set S} {pt : α → S}
    (h : IsSurfaceArrangement 𝒮 disc pt)
    {A : Society α β} (hA : A ∈ 𝒮) {x : α} (hx : x ∈ A.Ω.bar) :
    pt x ∈ disc A := by
  have hxBd := (h.isClosedDisc A hA).2 x hx
  exact (h.isClosedDisc A hA).1.isClosed.closure_subset_iff.mpr (Subset.refl _) hxBd.1

/-- Among the society boundary vertices, exactly the vertices of `A`
lie in the disc for `A`. This follows from the arrangement intersection
condition and injectivity of its point map. -/
theorem arrangement_pt_mem_disc_iff
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} {𝒮 : Set (Society α β)}
    {disc : Society α β → Set S} {pt : α → S}
    (h : IsSurfaceArrangement 𝒮 disc pt)
    {A : Society α β} (hA : A ∈ 𝒮) {x : α} (hx : x ∈ segregationVertices 𝒮) :
    pt x ∈ disc A ↔ x ∈ A.Ω.bar := by
  refine ⟨?_, arrangement_pt_mem_disc h hA⟩
  intro hxD
  obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp hx
  by_cases hAB : A = B
  · exact hAB.symm ▸ hxB
  · obtain ⟨y, hy, hpt⟩ := h.inter_discs A hA B hB hAB
      ⟨hxD, arrangement_pt_mem_disc h hB hxB⟩
    have hySeg : y ∈ segregationVertices 𝒮 := mem_iUnion₂.mpr ⟨A, hA, hy.1⟩
    have hyx : y = x := h.injOn_pts hySeg hx hpt
    exact hyx ▸ hy.1

/-- The attachment vertices lie on the intrinsic disc boundary. -/
theorem arrangement_pt_mem_discBd
    {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {𝒮 : Set (Society α β)}
    {disc : Society α β → Set S} {pt : α → S}
    (h : IsSurfaceArrangement 𝒮 disc pt)
    {A : Society α β} (hA : A ∈ 𝒮) {x : α} (hx : x ∈ A.Ω.bar) :
    pt x ∈ discBd (disc A) := by
  rw [← GM14.IsClosedDisc.subBd_eq_discBd hS (h.isClosedDisc A hA).1]
  exact (h.isClosedDisc A hA).2 x hx

/-- A drawn boundary vertex lies on a society disc boundary exactly
when it is one of that society's attachment vertices. -/
theorem arrangement_pt_mem_discBd_iff
    {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {𝒮 : Set (Society α β)}
    {disc : Society α β → Set S} {pt : α → S}
    (h : IsSurfaceArrangement 𝒮 disc pt)
    {A : Society α β} (hA : A ∈ 𝒮) {x : α} (hx : x ∈ segregationVertices 𝒮) :
    pt x ∈ discBd (disc A) ↔ x ∈ A.Ω.bar :=
  ⟨fun hpt => (arrangement_pt_mem_disc_iff h hA hx).mp (discBd_subset _ hpt),
    arrangement_pt_mem_discBd hS h hA⟩

/-- Properness separates the attachment sets of distinct large
societies, and hence separates their ring pieces. -/
theorem proper_arrangement_large_boundaries_disjoint
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} {𝒮 : Set (Society α β)}
    {disc : Society α β → Set S} {pt : α → S}
    (h : IsProperArrangement 𝒮 disc pt)
    {A B : Society α β} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮) (hAB : A ≠ B)
    (hlargeA : 3 < A.Ω.bar.ncard) (hlargeB : 3 < B.Ω.bar.ncard) :
    Disjoint A.Ω.bar B.Ω.bar := by
  refine disjoint_left.mpr ?_
  intro x hxA hxB
  exact disjoint_left.mp (h.2 hA hB hAB hlargeA hlargeB)
    (arrangement_pt_mem_disc h.1 hA hxA) (arrangement_pt_mem_disc h.1 hB hxB)

end GraphMinor.GM16
