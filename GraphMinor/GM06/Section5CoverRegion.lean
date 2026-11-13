module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5BoundaryGap

/-!
# Projection and initial incidence for a lifted region

The component above the following cuff gap projects into its region
on the cylinder and lies in the corresponding lifted linkage strip.
The half-gap on the cuff approaches the chosen initial lift without
meeting the drawing. Thus the initial lift is incident with the
specified lifted region, including when there is only one path.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Projection takes the selected lifted region into the selected
region on the cylinder. -/
theorem image_cylinderCoverRegion_subset_region (k : ℕ) (G : Drawing ClosedCylinder)
    (i : Fin k) :
    cylinderCoverProjection '' cylinderCoverRegion k G i ⊆ cylinderRegion k G i := by
  let S := univ \ G.U
  let b : CylinderCover := (⟨1, by norm_num⟩,
    (2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k)
  change cylinderCoverProjection '' connectedComponentIn (cylinderCoverProjection ⁻¹' S) b ⊆
    connectedComponentIn S (cylinderCoverProjection b)
  by_cases hb : b ∈ cylinderCoverProjection ⁻¹' S
  · exact (continuous_cylinderCoverProjection.continuousOn.image_connectedComponentIn_subset hb).trans
      (connectedComponentIn_mono _ (image_preimage_subset _ _))
  · rw [connectedComponentIn_eq_empty hb, image_empty]
    exact empty_subset _

/-- Incidence in the angular cover implies incidence in the projected
region, by continuity of the covering projection. -/
theorem cylinderCoverProjection_mem_closure_region
    {k : ℕ} {G : Drawing ClosedCylinder} {i : Fin k} {p : CylinderCover}
    (hp : p ∈ closure (cylinderCoverRegion k G i)) :
    cylinderCoverProjection p ∈ closure (cylinderRegion k G i) :=
  closure_mono (image_cylinderCoverRegion_subset_region k G i)
    (mem_closure_image continuous_cylinderCoverProjection.continuousAt hp)

/-- The selected lifted region stays between the corresponding consecutive
linkage lifts. -/
theorem cylinderCoverRegion_subset_strip {k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (i : Fin k) :
    cylinderCoverRegion k G i ⊆ cylinderCoverStrip L ((i.val : ℤ) + 1) := by
  rw [cylinderCoverRegion, cylinderCoverStrip]
  have he : (((i.val : ℤ) + 1 : ℤ) : ℝ) = ((i.val + 1 : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [he]
  apply connectedComponentIn_mono
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro hlink
  obtain ⟨j, hj⟩ := mem_iUnion.mp hlink
  exact hp.2 ((L.isSubdrawing j).2 hj)

/-- The chosen initial lift is incident with the lifted following region.
The half-gap on the initial cuff lies in that region before reaching
this lift; properness excludes all drawing points in its interior. -/
theorem cylinderInitialLift_mem_closure_coverRegion
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    cylinderInitialLift k i ∈ closure (cylinderCoverRegion k G i) := by
  let p : C(unitInterval, CylinderCover) :=
    ⟨fun t => (⟨1, by norm_num⟩,
      (2 * ((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k), by fun_prop⟩
  have hp0 : p 0 = cylinderInitialLift k i := by
    apply Prod.ext
    · rfl
    · change (2 * ((i.val + 1 : ℕ) : ℝ) + (0 : ℝ)) * π / k = _
      rw [add_zero]
      rfl
  have hp1 : p 1 = (⟨1, by norm_num⟩,
      (2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k) := rfl
  have hoff {t : unitInterval} (ht : 0 < t) : cylinderCoverProjection (p t) ∉ G.U := by
    let u : unitInterval := ⟨(t : ℝ) / 2, by constructor <;> linarith only [t.2.1, t.2.2]⟩
    have hu : u ∈ Ioo (0 : unitInterval) 1 := by
      constructor
      · change (0 : ℝ) < (t : ℝ) / 2
        exact half_pos ht
      · change (t : ℝ) / 2 < 1
        linarith only [t.2.2]
    have hproj : cylinderCoverProjection (p t) = initialCuffGapCurve k i u := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change Circle.exp _ = Circle.exp _
        congr 1
        change (2 * ((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k =
          2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ) / 2) * π / k
        ring
    have hR := (initialCuffGapCurve_props hG i).2.2.2.2 ⟨u, hu, hproj.symm⟩
    exact (connectedComponentIn_subset _ _ hR).2
  have him : p '' Ioi (0 : unitInterval) ⊆ cylinderCoverRegion k G i := by
    have hconn : IsPreconnected (p '' Ioi (0 : unitInterval)) :=
      isPreconnected_Ioi.image p p.continuous.continuousOn
    have hsub : p '' Ioi (0 : unitInterval) ⊆
        cylinderCoverProjection ⁻¹' (univ \ G.U) := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨mem_univ _, hoff ht⟩
    rw [cylinderCoverRegion, ← hp1]
    exact hconn.subset_connectedComponentIn ⟨1, zero_lt_one, rfl⟩ hsub
  have hz : (0 : unitInterval) ∈ closure (Ioi (0 : unitInterval)) := by
    rw [closure_Ioi' (⟨1, zero_lt_one⟩ : (Ioi (0 : unitInterval)).Nonempty)]
    exact le_rfl
  rw [← hp0]
  exact closure_mono him (mem_closure_image p.continuous.continuousAt hz)

end GraphMinor.GM06
