module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5BoundaryGap

/-!
# Incidence at the right initial lift

The following initial cuff gap approaches both of its endpoints
without meeting the drawing. Its right half shows that the next
initial lift belongs to the closure of the selected cover region.
For a single linkage path this is the other copy of the same initial
vertex, which must stay distinct in the proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The right endpoint lift of the following initial cuff gap is
incident with the selected lifted region. -/
theorem right_initialLift_mem_closure_coverRegion
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    (⟨1, by norm_num⟩, 2 * ((i.val + 2 : ℕ) : ℝ) * π / k) ∈
      closure (cylinderCoverRegion k G i) := by
  let p : C(unitInterval, CylinderCover) :=
    ⟨fun t => (⟨1, by norm_num⟩,
      (2 * ((i.val + 2 : ℕ) : ℝ) - (t : ℝ)) * π / k), by fun_prop⟩
  have hp0 : p 0 = (⟨1, by norm_num⟩, 2 * ((i.val + 2 : ℕ) : ℝ) * π / k) := by
    apply Prod.ext
    · rfl
    · change (2 * ((i.val + 2 : ℕ) : ℝ) - (0 : ℝ)) * π / k = _
      rw [sub_zero]
  have hp1 : p 1 = (⟨1, by norm_num⟩,
      (2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k) := by
    apply Prod.ext
    · rfl
    · change (2 * ((i.val + 2 : ℕ) : ℝ) - 1) * π / k = _
      push_cast
      ring
  have hoff {t : unitInterval} (ht : 0 < t) : cylinderCoverProjection (p t) ∉ G.U := by
    let u : unitInterval := ⟨1 - (t : ℝ) / 2, by
      constructor <;> linarith only [t.2.1, t.2.2]⟩
    have hu : u ∈ Ioo (0 : unitInterval) 1 := by
      constructor
      · change (0 : ℝ) < 1 - (t : ℝ) / 2
        linarith only [t.2.2]
      · change 1 - (t : ℝ) / 2 < 1
        have htR : (0 : ℝ) < (t : ℝ) := ht
        linarith only [htR]
    have hproj : cylinderCoverProjection (p t) = initialCuffGapCurve k i u := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change Circle.exp _ = Circle.exp _
        congr 1
        change (2 * ((i.val + 2 : ℕ) : ℝ) - (t : ℝ)) * π / k =
          2 * (((i.val + 1 : ℕ) : ℝ) + (1 - (t : ℝ) / 2)) * π / k
        push_cast
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
