module

public import GraphMinor.GM06.Section5CutRegionPreimage
import GraphMinor.GM06.Section5CutRegion
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.Surface.DiscNbhd
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.Cuffs
import GraphMinor.GM07.Section11f
import GraphMinor.GM11.Regions

/-!
# An arbitrary cylinder region as a cut-disc drawing region

For VI (5.5), page 131, lift the deleted-edge region and remove the
cut-disc boundary. This leaves a connected open set with the same
closure as the full preimage. Its frontier lies in the pulled-back
drawing or on the adjoined disc boundary, so it is a whole region
of that augmented drawing. The closure still projects onto the
original region closure.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The deleted-edge region, or any region of a drawing retaining
the sole linkage, gives an actual region of the augmented cut-disc
drawing. This is the cut-disc region used in VI (5.5). -/
theorem preimage_arbitrary_region_sdiff_boundary_mem_regions
    {G H : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (hPH : (L.pathDrawing 0).U ⊆ H.U) {R : Set ClosedCylinder} (hR : R ∈ H.R)
    {F : Drawing D}
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' H.U ∪ bd D) :
    let φ : D → ClosedCylinder := fun p => radialCylinderProjection p.1
    (φ ⁻¹' R \ bd D) ∈ F.R ∧ φ '' closure (φ ⁻¹' R \ bd D) = closure R := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  dsimp only
  let φ : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  let Y := φ ⁻¹' R
  let Z := Y \ bd D
  have hS : IsSurface D := by
    have hU : IsClosedDisc (univ : Set D) := by
      obtain ⟨e⟩ := hD
      exact ⟨e.trans (Homeomorph.Set.univ D).symm⟩
    exact ⟨inferInstance, inferInstance, fun p => isManifoldPoint_of_disc hU Filter.univ_mem⟩
  obtain ⟨hYo, hYc, hcl⟩ := preimage_region_on_single_strip L hG hθ hD hBd hstrip hPH hR
  have hZo : IsOpen Z := hYo.sdiff (cuff_statement D hS).1
  have hZp : IsPreconnected Z := GM07.isPreconnected_diff_bd hS hYo hYc.isPreconnected
  have hclZ : closure Z = closure Y := closure_sdiff_boundary_of_isOpen hS hYo
  have hZne : Z.Nonempty := by
    obtain ⟨q, hq⟩ := hYc.nonempty
    have hqZ : q ∈ closure Z := hclZ.symm ▸ subset_closure hq
    exact closure_nonempty_iff.mp ⟨q, hqZ⟩
  have hdis : Disjoint Z F.U := by
    refine disjoint_left.mpr ?_
    intro x hx hxF
    rw [hFU] at hxF
    rcases hxF with hxH | hxbd
    · exact GM11.region_subset hR hx.1 hxH
    · exact hx.2 hxbd
  have hfr : frontier Z ⊆ F.U := by
    intro x hx
    rw [hFU]
    by_cases hxbd : x ∈ bd D
    · exact Or.inr hxbd
    · have hxY : x ∈ closure Y := hclZ ▸ hx.1
      have hxR : φ x ∈ closure R := hcl ▸ mem_image_of_mem φ hxY
      rcases GM11.closure_region_subset hR hxR with hin | hout
      · exact (hx.2 (hZo.interior_eq.symm ▸ ⟨hin, hxbd⟩)).elim
      · exact Or.inl hout
  refine ⟨region_of_connected_open_frontier ⟨hZne, hZp⟩ hZo hdis hfr, ?_⟩
  change φ '' closure Z = closure R
  rw [hclZ]
  exact hcl

end GraphMinor.GM06
