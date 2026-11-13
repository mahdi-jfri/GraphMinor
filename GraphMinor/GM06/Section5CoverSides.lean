module

public import GraphMinor.GM06.Defs

/-!
# Sides of an initial linkage vertex in the angular cover

Reduction 1 in VI Section 5, page 128, deletes an edge on the clockwise
side of an initial linkage vertex. A component of the path complement
forgets this side when there is just one path. Work in the angular cover
instead. Its preceding strip projects into the printed preceding strip,
and incidence with the chosen initial lift projects to incidence with
the original vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The covering projection is continuous. -/
theorem continuous_cylinderCoverProjection : Continuous cylinderCoverProjection :=
  ((continuous_subtype_val.comp continuous_fst).prodMk
    (Circle.exp.continuous.comp continuous_snd)).subtype_mk _

/-- The specified initial lift projects to the specified initial vertex. -/
theorem cylinderCoverProjection_initialLift {k : ℕ} (i : Fin k) :
    cylinderCoverProjection (cylinderInitialLift k i) = cylinderM1Point k i := rfl

/-- The seed of the preceding lifted strip projects to the preceding dual point,
including the wrap from index zero to index k − 1. -/
theorem cylinderCoverProjection_preceding_seed {k : ℕ} (hk : 0 < k) (i : Fin k) :
    cylinderCoverProjection (⟨1, by norm_num⟩,
      (2 * ((i.val : ℤ) : ℝ) + 1) * π / k) = cylinderN1Point k (finPredCycle i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp _ = Circle.exp _
    by_cases hi : i.val = 0
    · simp only [finPredCycle, hi, ↓reduceDIte]
      have hkm : k - 1 + 1 = k := Nat.sub_add_cancel hk
      norm_num only [Nat.cast_zero, Int.cast_zero]
      change Circle.exp (1 * π / k) =
        Circle.exp ((2 * ((k - 1 + 1 : ℕ) : ℝ) + 1) * π / k)
      rw [hkm]
      have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      have he : (2 * (k : ℝ) + 1) * π / k = π / k + 2 * π := by
        field_simp [hkne]
        ring
      rw [he, Circle.exp_add_two_pi]
      congr 1
      ring
    · simp only [finPredCycle, hi, ↓reduceDIte]
      have him : i.val - 1 + 1 = i.val := Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)
      change Circle.exp ((2 * (i.val : ℝ) + 1) * π / k) =
        Circle.exp ((2 * ((i.val - 1 + 1 : ℕ) : ℝ) + 1) * π / k)
      rw [him]

/-- Projection sends the preceding lifted component into the preceding
component on the cylinder. This holds even for a single linkage path. -/
theorem image_cylinderCoverStrip_subset_preceding {k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (i : Fin k) :
    cylinderCoverProjection '' cylinderCoverStrip L (i.val : ℤ) ⊆
      cylinderStrip L (finPredCycle i) := by
  rw [cylinderCoverStrip, cylinderStrip, ← cylinderCoverProjection_preceding_seed i.pos i]
  let S := (Set.univ \ ⋃ j : Fin k, (L.pathDrawing j).U)
  let b : CylinderCover := (⟨1, by norm_num⟩,
    (2 * ((i.val : ℤ) : ℝ) + 1) * π / k)
  by_cases hb : b ∈ cylinderCoverProjection ⁻¹' S
  · exact (continuous_cylinderCoverProjection.continuousOn.image_connectedComponentIn_subset hb).trans
      (connectedComponentIn_mono _ (image_preimage_subset _ _))
  · rw [show connectedComponentIn (cylinderCoverProjection ⁻¹' S) b = ∅ from
      connectedComponentIn_eq_empty hb]
    simp only [image_empty, empty_subset]

/-- A clockwise initial edge satisfies the printed containment and incidence
conditions. Thus retaining the side can only restrict Reduction 1. -/
theorem IsClockwiseInitialEdge.incident_and_subset
    {k : ℕ} {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    {i : Fin k} {e : Set ClosedCylinder} (he : IsClockwiseInitialEdge L i e) :
    cylinderM1Point k i ∈ closure e ∧ e ⊆ cylinderStrip L (finPredCycle i) := by
  obtain ⟨A, _, hA, hs, hsub⟩ := he
  constructor
  · rw [← hA, ← cylinderCoverProjection_initialLift i]
    exact mem_closure_image continuous_cylinderCoverProjection.continuousAt hs
  · rw [← hA]
    exact (image_mono hsub).trans (image_cylinderCoverStrip_subset_preceding L i)

end GraphMinor.GM06
