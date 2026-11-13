module

public import GraphMinor.GM06.Section5RadialProjection
public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5LinkageStripCircle
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.Regions
import GraphMinor.Surface.CutComp

/-!
# Lifting an arbitrary region to the one-path cut disc

The deleted-edge region in VI (5.5), page 131, need not contain the
chosen cuff midpoint. Its full preimage in the one-path cut disc is
still connected. Projection is closed and surjective, and each
point off the linkage has a unique preimage. A separation of the
preimage would therefore give a separation of the region. Closedness
also gives the exact image of the preimage closure.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u v

/-- A closed map with unique fibres above a preconnected set has a
preconnected preimage, provided every point of the set has a preimage. -/
theorem preconnected_preimage_of_closed_map_unique_on
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y} (hs : IsPreconnected s) (hf : IsClosedMap f)
    (honto : s ⊆ range f)
    (hunique : ∀ x, f x ∈ s → ∀ y, f y ∈ s → f x = f y → x = y) :
    IsPreconnected (f ⁻¹' s) := by
  apply isPreconnected_closed_iff.mpr
  intro a b ha hb hcover hsa hsb
  have him : f '' (f ⁻¹' s) = s := image_preimage_eq_of_subset honto
  have hsplit : (s ∩ (f '' a ∩ f '' b)).Nonempty := by
    apply isPreconnected_closed_iff.mp hs (f '' a) (f '' b) (hf a ha) (hf b hb)
    · simpa only [him, image_union] using image_mono (f := f) hcover
    · simpa only [image_preimage_inter] using hsa.image f
    · simpa only [image_preimage_inter] using hsb.image f
  obtain ⟨z, hz, ⟨x, hxa, hxz⟩, ⟨y, hyb, hyz⟩⟩ := hsplit
  have hxs : f x ∈ s := hxz.symm ▸ hz
  have hys : f y ∈ s := hyz.symm ▸ hz
  have hxy := hunique x hxs y hys (hxz.trans hyz.symm)
  exact ⟨x, hxs, hxa, hxy.symm ▸ hyb⟩

/-- Any region of a drawing containing the sole linkage lifts to
an open connected part of the cut disc, with exactly the required
closure image. This applies to the deleted-edge region in VI (5.5). -/
theorem preimage_region_on_single_strip
    {G H : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (hPH : (L.pathDrawing 0).U ⊆ H.U) {R : Set ClosedCylinder} (hR : R ∈ H.R) :
    let φ : D → ClosedCylinder := fun p => radialCylinderProjection p.1
    IsOpen (φ ⁻¹' R) ∧ IsConnected (φ ⁻¹' R) ∧
      φ '' closure (φ ⁻¹' R) = closure R := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  dsimp only
  let φ : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hφc : Continuous φ := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hφclosed : IsClosedMap φ := hφc.isClosedMap
  have hφonto := surjective_single_strip_projection L hG hθ hD hBd hstrip
  have honto : R ⊆ range φ := by rw [hφonto.range_eq]; exact subset_univ _
  have huniq : ∀ x, φ x ∈ R → ∀ y, φ y ∈ R → φ x = φ y → x = y := by
    intro x hx y _ hxy
    exact single_strip_projection_inj_off_path L hG hθ hD hBd hstrip
      (fun h => GM11.region_subset hR hx (hPH h)) hxy
  have hpre := preconnected_preimage_of_closed_map_unique_on (GM11.region_isPreconnected hR)
    hφclosed honto huniq
  have hne : (φ ⁻¹' R).Nonempty := (GM11.region_nonempty hR).preimage' honto
  refine ⟨(GM11.region_isOpen hR).preimage hφc, ⟨hne, hpre⟩, ?_⟩
  rw [← hφclosed.closure_image_eq_of_continuous hφc, image_preimage_eq_of_subset honto]

end GraphMinor.GM06
