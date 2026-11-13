module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.CapMap

/-!
# Extending an embedding across a cap

An embedding that maps one cuff bijectively to another extends to an
embedding after both cuffs are capped. The proved cap-map construction is
injective on the cap. Its interior maps into the new cap interior, which
misses the image of the original surface. This also separates the cap from
the old surface and proves global injectivity. The result is used to
recognize near-planar cylinder sides in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

private theorem cap_range_disjoint_discInt {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] {C : Set S} {j : S → T} {D : Set T}
    (hc : GM07.IsCappedCuff C T j D) : Disjoint (range j) (discInt D) := by
  apply disjoint_left.mpr
  rintro x hxR ⟨hxD, hxBd⟩
  exact hxBd (hc.discBd_eq ▸ hc.inter_eq.subset ⟨hxR, hxD⟩)

private theorem mem_cap_discInt_of_not_range {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] {C : Set S} {j : S → T} {D : Set T}
    (hc : GM07.IsCappedCuff C T j D) {x : T} (hx : x ∉ range j) : x ∈ discInt D := by
  have hxD : x ∈ D := (hc.union_eq.symm ▸ mem_univ x : x ∈ range j ∪ D).resolve_left hx
  refine ⟨hxD, ?_⟩
  rw [hc.discBd_eq]
  exact fun h => hx (image_subset_range _ _ h)

/-- Extend a cuff-preserving embedding across caps. This supplies the cap
extension needed for the cylinder-side case of VIII (18.2), page 286. -/
theorem exists_cap_embedding {Y Y' S S' : Type w}
    [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace S] [TopologicalSpace S']
    (hY : IsSurface Y) {C : Set Y} {C₀ : Set S} {jY : Y → Y'} {DY : Set Y'}
    {j : S → S'} {D : Set S'} (hcY : GM07.IsCappedCuff C Y' jY DY)
    (hcS : GM07.IsCappedCuff C₀ S' j D) {φ : Y → S}
    (hφ : IsEmbedding φ) (hb : BijOn φ C C₀) :
    ∃ Ψ : Y' → S', IsEmbedding Ψ ∧ ∀ y, Ψ (jY y) = j (φ y) := by
  have : CompactSpace Y := hY.1
  have : CompactSpace Y' := hcY.isSurface.1
  have : T2Space Y' := hcY.isSurface.2.1
  have : T2Space S' := hcS.isSurface.2.1
  have hCne : C.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := hcY.cuff
    exact ⟨x, mem_connectedComponentIn hx⟩
  obtain ⟨Ψ, hΨ, hfix, _, hinjD, _, hInt⟩ := GM07.exists_cap_map hcY hcS hφ.continuous hb hCne
  have hsep := cap_range_disjoint_discInt hcS
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    by_cases hxR : x ∈ range jY
    · obtain ⟨a, rfl⟩ := hxR
      by_cases hyR : y ∈ range jY
      · obtain ⟨b, rfl⟩ := hyR
        rw [hfix, hfix] at hxy
        exact congrArg jY (hφ.injective (hcS.isEmbedding.injective hxy))
      · have hyI := hInt (mem_cap_discInt_of_not_range hcY hyR)
        rw [← hxy, hfix] at hyI
        exact (disjoint_left.mp hsep (mem_range_self _) hyI).elim
    · have hxI := hInt (mem_cap_discInt_of_not_range hcY hxR)
      by_cases hyR : y ∈ range jY
      · obtain ⟨b, rfl⟩ := hyR
        rw [hxy, hfix] at hxI
        exact (disjoint_left.mp hsep (mem_range_self _) hxI).elim
      · exact hinjD (mem_cap_discInt_of_not_range hcY hxR).1
          (mem_cap_discInt_of_not_range hcY hyR).1 hxy
  exact ⟨Ψ, (hΨ.isClosedEmbedding hinj).isEmbedding, hfix⟩

end GraphMinor.GM08
