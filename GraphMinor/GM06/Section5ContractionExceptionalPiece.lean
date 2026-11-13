module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverRegions
import GraphMinor.GM06.Section5ContractionLiftedNeighbourContact
import GraphMinor.GM06.Section5LiftedRegionBridge
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks

/-!
# Replacing a vertex-free interval between exceptional values

For Reduction 3 of VI (5.5), page 130, an interval whose interior
misses the augmented drawing lies in one lifted region. When both
ends are copies of the contracted vertex, its old counterpart joins
the corresponding neighbour lifts through the preimage component.
The component and contact lemmas construct both incidences, so the
replacement retains the required sheet endpoints.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Replace a lifted interval between two exceptional values by
an old curve between the neighbour-section values in their actual sheets. -/
theorem exists_lifted_region_replacement_between_exceptional_values
    {k : ℕ} {G F F' : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hfix : ∀ p, cylinderCoverProjection p ∈ bd ClosedCylinder → Φ p = p)
    (hinj : ∀ x y, π x ≠ cylinderM1Point k i → π y ≠ cylinderM1Point k i → π x = π y → x = y)
    (hsurj : ∀ x, x ≠ cylinderM1Point k i → ∃ y, π y = x)
    (hU : F'.U = π '' F.U) (hs : cylinderM1Point k i ∈ F'.U)
    (hfibre : π ⁻¹' {cylinderM1Point k i} = closure e)
    (ρ : CylinderCover → CylinderCover) (hρ : ∀ q, Φ (ρ q) = q)
    (hρv : ∀ q, cylinderCoverProjection q = cylinderM1Point k i → cylinderCoverProjection (ρ q) = v)
    (f : C(unitInterval, CylinderCover))
    (hf : ∀ t, 0 < t → t < 1 → cylinderCoverProjection (f t) ∉ F'.U)
    (hf0 : cylinderCoverProjection (f 0) = cylinderM1Point k i)
    (hf1 : cylinderCoverProjection (f 1) = cylinderM1Point k i) :
    ∃ g : C(unitInterval, CylinderCover), g 0 = ρ (f 0) ∧ g 1 = ρ (f 1) ∧
      ∀ t, 0 < t → t < 1 → cylinderCoverProjection (g t) ∉ F.U := by
  obtain ⟨Y, hY, hfin, hf0cl, hf1cl⟩ := exists_component_containing_curve_interior f
    (B := cylinderCoverProjection ⁻¹' F'.Uᶜ) hf
  have hFibSub : π ⁻¹' {cylinderM1Point k i} ⊆ F.U := by
    rw [hfibre]
    exact F.closure_subset_U (hGF.2 hl.1)
  have hC := preimage_lifted_component_of_contraction π Φ (cylinderM1Point k i)
    hproj htrans hinj hsurj hU hFibSub hs hY
  have hsbd : cylinderM1Point k i ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    exact Or.inl rfl
  have h0fix : Φ (f 0) = f 0 := hfix _ (hf0 ▸ hsbd)
  have h1fix : Φ (f 1) = f 1 := hfix _ (hf1 ▸ hsbd)
  have h0cl := section_neighbour_mem_closure_preimage_lifted_region hG hGF hFU i
    hval hl hv π Φ hproj htrans hinj hsurj hU hs hfibre ρ hρ hρv (f 0) hf0 h0fix hY hf0cl
  have h1cl := section_neighbour_mem_closure_preimage_lifted_region hG hGF hFU i
    hval hl hv π Φ hproj htrans hinj hsurj hU hs hfibre ρ hρ hρv (f 1) hf1 h1fix hY hf1cl
  obtain ⟨y, hy⟩ : Y.Nonempty := by
    obtain ⟨y, hy, heq⟩ := hY
    exact ⟨y, heq ▸ mem_connectedComponentIn hy⟩
  have hx : ρ y ∈ Φ ⁻¹' Y := by
    change Φ (ρ y) ∈ Y
    rw [hρ]
    exact hy
  obtain ⟨g, hg0, hg1, hg⟩ := exists_curve_between_contraction_neighbour_lifts_through_region
    L hG i hGF hval hl hv hvC (ρ (f 0)) (ρ (f 1)) (hρv _ hf0) (hρv _ hf1)
    hC h0cl h1cl (ρ y) hx
  have hCsub : Φ ⁻¹' Y ⊆ cylinderCoverProjection ⁻¹' F.Uᶜ := by
    obtain ⟨x, _, heq⟩ := hC
    rw [← heq]
    exact connectedComponentIn_subset _ _
  exact ⟨g, hg0, hg1, fun t ht0 ht1 => hCsub (hg t ht0 ht1)⟩

end GraphMinor.GM06
