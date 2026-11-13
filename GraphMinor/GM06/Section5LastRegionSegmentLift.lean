module

public import GraphMinor.GM06.Section5CutCurveLift
import GraphMinor.GM06.Section5CutRegionPreimage
import GraphMinor.GM06.Section5RegionVisit
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.Regions
import GraphMinor.Surface.DiscNbhd
import GraphMinor.Surface.CutComp
import Mathlib.Topology.Subpath

/-!
# Lifting the helix segment after its last earlier vertex hit

VI (5.5), pages 131–132, uses the segment between z₁ and z₂ in the
deleted-edge region. Normality and the absence of intermediate
vertex times put its interior in that region. It therefore misses
the retained linkage and lifts to the closed cut disc. The lifted
endpoint copies lie in the closure of the actual cut face. This
fixes the contact copy before choosing the replacement approach.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Lift the actual last region segment, retaining both contact
copies in the cut-face closure, for VI (5.5), pages 131–132. -/
theorem exists_lift_of_last_region_segment
    {G H : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (hPH : (L.pathDrawing 0).U ⊆ H.U)
    (f : Curve ClosedCylinder) (hf : IsNormalCurve H f)
    {R : Set ClosedCylinder} (hR : R ∈ H.R) {z₁ z₂ : unitInterval}
    (hz : IsGreatest (closure (f ⁻¹' R)) z₂) (hzlt : z₁ < z₂)
    (hno : ∀ t : unitInterval, z₁ < t → t < z₂ → f t ∉ H.V) :
    ∃ q : Curve D,
      (∀ t, radialCylinderProjection (q t).1 = f (Icc.convexComb z₁ z₂ t)) ∧
      ∀ t, q t ∈ closure ((fun p : D => radialCylinderProjection p.1) ⁻¹' R \ bd D) := by
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  have hregion := (curve_between_last_vertex_and_region_visit f hf hR hz hzlt hno).1
  let old : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  let seg := (old.subpath z₁ z₂).toContinuousMap
  have hsegR (t : unitInterval) (ht0 : 0 < t) (ht1 : t < 1) : seg t ∈ R := by
    let u := Icc.convexComb z₁ z₂ t
    have hdiff : (0 : ℝ) < (z₂ : ℝ) - z₁ := sub_pos.mpr hzlt
    have ht0' : (0 : ℝ) < t := ht0
    have ht1' : (t : ℝ) < 1 := ht1
    have hp := mul_pos ht0' hdiff
    have hq := mul_pos (sub_pos.mpr ht1') hdiff
    have hu0 : z₁ < u := by
      change (z₁ : ℝ) < (1 - (t : ℝ)) * z₁ + t * z₂
      nlinarith only [hp]
    have hu1 : u < z₂ := by
      change (1 - (t : ℝ)) * z₁ + t * z₂ < (z₂ : ℝ)
      nlinarith only [hq]
    exact hregion u hu0 hu1
  have hoff : ∀ t : unitInterval, 0 < t → t < 1 → seg t ∉ (L.pathDrawing 0).U := by
    intro t ht0 ht1 htP
    exact GM11.region_subset hR (hsegR t ht0 ht1) (hPH htP)
  obtain ⟨q, hqproj⟩ := exists_curve_lift_to_single_strip L hG hθ hD hBd hstrip seg hoff
  have hS : IsSurface D := by
    let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
    have hU : IsClosedDisc (univ : Set D) := by
      obtain ⟨e⟩ := hD
      exact ⟨e.trans (Homeomorph.Set.univ D).symm⟩
    exact ⟨inferInstance, inferInstance, fun p => isManifoldPoint_of_disc hU Filter.univ_mem⟩
  have hYo := (preimage_region_on_single_strip L hG hθ hD hBd hstrip hPH hR).1
  have hqR : ∀ t : unitInterval, 0 < t → t < 1 →
      q t ∈ (fun p : D => radialCylinderProjection p.1) ⁻¹' R := by
    intro t ht0 ht1
    change radialCylinderProjection (q t).1 ∈ R
    rw [hqproj t]
    exact hsegR t ht0 ht1
  exact ⟨q, hqproj, curve_mem_closure_off_boundary_of_interior_mem hS hYo q hqR⟩

end GraphMinor.GM06
