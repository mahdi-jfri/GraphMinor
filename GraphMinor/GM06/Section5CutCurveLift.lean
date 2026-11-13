module

public import GraphMinor.GM06.Section5CutRegionCoordinates
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5CoverCurvePoint
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5CutSheetComponent

/-!
# Lifting a curve whose interior misses the sole linkage

For VI (5.5), page 131, the last region segment of the helix has
its interior off the linkage. Lift it through a point in the chosen
cut sheet. Connectedness keeps its interior in that sheet. The
closed strip disc contains its endpoint limits as well. The closed
embedding of the disc in the cover then gives a continuous curve
in the disc projecting to the whole original segment.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- A cylinder curve whose interior misses the sole linkage lifts
continuously to the closed cut disc, including both endpoint copies.
This lifts the last region segment in VI (5.5), page 131. -/
theorem exists_curve_lift_to_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (f : Curve ClosedCylinder)
    (hoff : ∀ t : unitInterval, 0 < t → t < 1 → f t ∉ (L.pathDrawing 0).U) :
    ∃ q : Curve D, ∀ t, radialCylinderProjection (q t).1 = f t := by
  let mid : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hmid : mid ∈ Ioo (0 : unitInterval) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  obtain ⟨p, hp⟩ := surjective_single_strip_projection L hG hθ hD hBd hstrip (f mid)
  change radialCylinderProjection p.1 = f mid at hp
  let a : D → CylinderCover := fun p => planeToCylinderCover p.1
  have hpStrip : a p ∈ cylinderCoverStrip L 1 := by
    rw [cylinderCoverStrip_eq_single_strip_sheet L hG hθ hD hBd hstrip]
    refine ⟨⟨p.1, p.2, rfl⟩, ?_⟩
    change radialCylinderProjection p.1 ∉ (L.pathDrawing 0).U
    rw [hp]
    exact hoff mid hmid.1 hmid.2
  obtain ⟨B, hBmid, hBproj⟩ := exists_cover_curve_through_point f mid (a p) hp
  let U := cylinderCoverProjection ⁻¹' (univ \ ⋃ j, (L.pathDrawing j).U)
  have hpre : IsPreconnected (B '' Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image B B.continuous.continuousOn
  have hsub : B '' Ioo (0 : unitInterval) 1 ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    have hj0 : j = 0 := Subsingleton.elim _ _
    rw [hj0, hBproj t] at hj
    exact hoff t ht.1 ht.2 hj
  have hcc := hpre.subset_connectedComponentIn ⟨mid, hmid, rfl⟩ hsub
  rw [hBmid] at hcc
  have heq := connectedComponentIn_eq hpStrip
  change cylinderCoverStrip L 1 = connectedComponentIn U (a p) at heq
  rw [← heq] at hcc
  let K := planeToCylinderCover '' D
  have hKclosed : IsClosed K := (hD.isCompact.image continuous_planeToCylinderCover).isClosed
  have hIntoK : Ioo (0 : unitInterval) 1 ⊆ B ⁻¹' K := by
    intro t ht
    have h := hcc ⟨t, ht, rfl⟩
    rw [cylinderCoverStrip_eq_single_strip_sheet L hG hθ hD hBd hstrip] at h
    exact h.1
  have hcl : closure (Ioo (0 : unitInterval) 1) ⊆ B ⁻¹' K :=
    closure_minimal hIntoK (hKclosed.preimage B.continuous)
  rw [closure_Ioo (by norm_num : (0 : unitInterval) ≠ 1)] at hcl
  have hLift (t : unitInterval) : ∃ q : D, a q = B t := by
    obtain ⟨q, hq, hqB⟩ := hcl (show t ∈ Icc (0 : unitInterval) 1 from ⟨bot_le, le_top⟩)
    exact ⟨⟨q, hq⟩, hqB⟩
  choose q hq using hLift
  have ha := isClosedEmbedding_single_strip_coverMap hD hstrip
  have hqc : Continuous q := ha.isEmbedding.continuous_iff.mpr (by
    have he : a ∘ q = B := funext hq
    rw [he]
    exact B.continuous)
  refine ⟨⟨q, hqc⟩, ?_⟩
  intro t
  change cylinderCoverProjection (a (q t)) = f t
  rw [hq t]
  exact hBproj t

/-- A curve with interior in an open surface set has its endpoint
contacts in the closure of the part off the surface boundary.
This identifies the lifted helix endpoints with the actual cut face
used in VI (5.5), page 131. -/
theorem curve_mem_closure_off_boundary_of_interior_mem
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S)
    {Y : Set S} (hY : IsOpen Y) (q : Curve S)
    (hq : ∀ t : unitInterval, 0 < t → t < 1 → q t ∈ Y) :
    ∀ t : unitInterval, q t ∈ closure (Y \ bd S) := by
  intro t
  rw [closure_sdiff_boundary_of_isOpen hS hY]
  have hsub : Ioo (0 : unitInterval) 1 ⊆ q ⁻¹' Y := fun u hu => hq u hu.1 hu.2
  have htcl : t ∈ closure (Ioo (0 : unitInterval) 1) := by
    rw [closure_Ioo (by norm_num : (0 : unitInterval) ≠ 1)]
    exact ⟨bot_le, le_top⟩
  exact q.continuous.closure_preimage_subset Y (closure_mono hsub htcl)

end GraphMinor.GM06
