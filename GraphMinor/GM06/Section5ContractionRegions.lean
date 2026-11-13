module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5CutRegionPreimage
import GraphMinor.GM11.Regions
import GraphMinor.GM06.Section5CylinderEdgeIncidence
import GraphMinor.GM06.Section5ContractionNeighbourIncidence
import GraphMinor.GM11.Walks

/-!
# Regions under a cylinder contraction

The regions needed in the Reduction 3 case of VI (5.5), page 130,
pull back to regions of the old drawing. The contraction is closed,
and its fibres over a region are singletons. These facts give a
connected preimage and preserve the image of its closure.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A region pulls back to a region under a cylinder contraction whose
exceptional fibre lies in the drawing. Its closure has the expected image. -/
theorem preimage_region_of_contraction
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S}
    (π : C(S, S)) (s : S)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ s → ∃ x, π x = z)
    (hs : s ∈ G'.U) (hfibre : π ⁻¹' {s} ⊆ G.U)
    (hU : G'.U = π '' G.U)
    {R : Set S} (hR : R ∈ G'.R) :
    π ⁻¹' R ∈ G.R ∧ π '' closure (π ⁻¹' R) = closure R := by
  have hRU : ∀ z ∈ R, z ∉ G'.U := fun z hz => GM11.region_subset hR hz
  have hRs : ∀ z ∈ R, z ≠ s := by
    intro z hz he
    exact hRU z hz (he ▸ hs)
  have honto : R ⊆ range π := by
    intro z hz
    exact hsurj z (hRs z hz)
  have huniq : ∀ x, π x ∈ R → ∀ y, π y ∈ R → π x = π y → x = y := by
    intro x hx y hy he
    exact hinj x y (hRs _ hx) (hRs _ hy) he
  have hconn := preconnected_preimage_of_closed_map_unique_on
    (GM11.region_isPreconnected hR) π.continuous.isClosedMap honto huniq
  have hnotU (x) : π x ∉ G'.U ↔ x ∉ G.U := by
    constructor
    · intro hx hxu
      exact hx (hU ▸ ⟨x, hxu, rfl⟩)
    · intro hx hxu
      have hxs : π x ≠ s := fun he => hx (hfibre he)
      obtain ⟨y, hy, he⟩ := hU ▸ hxu
      have hys : π y ≠ s := he.symm ▸ hxs
      exact hx ((hinj x y hxs hys he.symm).symm ▸ hy)
  obtain ⟨z, hz⟩ := GM11.region_nonempty hR
  obtain ⟨x, hx⟩ := hsurj z (hRs z hz)
  have hxR : x ∈ π ⁻¹' R := by
    change π x ∈ R
    rw [hx]
    exact hz
  obtain ⟨r, hr, hxr⟩ := GM11.exists_region_of_notMem ((hnotU x).1 (hx ▸ hRU z hz))
  have hsub : π ⁻¹' R ⊆ r := GM11.subset_region hr hconn
    (disjoint_left.mpr fun y hy hyU => (hnotU y).1 (hRU _ hy) hyU) hxR hxr
  have himg : π '' r ⊆ R := GM11.subset_region hR
    ((GM11.region_isPreconnected hr).image π π.continuous.continuousOn)
    (disjoint_left.mpr (by
      rintro _ ⟨y, hy, rfl⟩ hyU
      exact (hnotU y).2 (GM11.region_subset hr hy) hyU))
    ⟨x, hxr, hx⟩ hz
  have heq : π ⁻¹' R = r := subset_antisymm hsub (fun y hy => himg ⟨y, hy, rfl⟩)
  refine ⟨heq.symm ▸ hr, ?_⟩
  rw [← π.continuous.isClosedMap.closure_image_eq_of_continuous π.continuous,
    image_preimage_eq_of_subset honto]

/-- A region incident with the contraction value pulls back to an old
region incident with at least one end of the contracted edge. -/
theorem endpoint_mem_closure_preimage_region_of_contraction
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (π : C(ClosedCylinder, ClosedCylinder)) {s v : ClosedCylinder}
    {e : Set ClosedCylinder} (hl : G.toGraph.IsLink e s v)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ s → ∃ x, π x = z)
    (hs : s ∈ G'.U) (hfibre : π ⁻¹' {s} = closure e)
    (hU : G'.U = π '' G.U)
    {R : Set ClosedCylinder} (hR : R ∈ G'.R) (hsR : s ∈ closure R) :
    π ⁻¹' R ∈ G.R ∧
      (s ∈ closure (π ⁻¹' R) ∨ v ∈ closure (π ⁻¹' R)) := by
  have hf : π ⁻¹' {s} ⊆ G.U := by
    rw [hfibre]
    exact G.closure_subset_U hl.1
  obtain ⟨hr, himage⟩ := preimage_region_of_contraction π s hinj hsurj hs hf hU hR
  obtain ⟨x, hxr, hxs⟩ := himage ▸ hsR
  have hxe : x ∈ closure e := by
    rw [← hfibre]
    exact hxs
  exact ⟨hr, endpoint_mem_closure_region_of_closed_edge_contact L hG hl hr ⟨x, hxe, hxr⟩⟩

/-- Every region at a contracted initial vertex lifts to an old
region incident with its old neighbour, as needed in VI (5.5). -/
theorem neighbour_mem_closure_preimage_region_of_contraction
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (π : C(ClosedCylinder, ClosedCylinder))
    {v : ClosedCylinder} {e : Set ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i)
    (hinj : ∀ x y, π x ≠ cylinderM1Point k i →
      π y ≠ cylinderM1Point k i → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ cylinderM1Point k i → ∃ x, π x = z)
    (hs : cylinderM1Point k i ∈ G'.U)
    (hfibre : π ⁻¹' {cylinderM1Point k i} = closure e)
    (hU : G'.U = π '' G.U)
    {R : Set ClosedCylinder} (hR : R ∈ G'.R)
    (hsR : cylinderM1Point k i ∈ closure R) :
    π ⁻¹' R ∈ G.R ∧ v ∈ closure (π ⁻¹' R) := by
  obtain ⟨hr, hs | hvR⟩ := endpoint_mem_closure_preimage_region_of_contraction
    L hG π hl hinj hsurj hs hfibre hU hR hsR
  · exact ⟨hr, neighbour_mem_closure_region_of_initial_valency_one L hG i hval hl hv hr hs⟩
  · exact ⟨hr, hvR⟩

end GraphMinor.GM06
