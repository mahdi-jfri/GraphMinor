module

public import GraphMinor.GM06.Section5CoverSides
public import GraphMinor.GM06.Section5LinkageStripCircle
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5LiftCover
import GraphMinor.GM06.Section5RegionPoint

/-!
# A strip disc lies in its angular-cover component

The interior of the disc between consecutive linkage lifts misses all
linkage lifts. Adding the points of its boundary that also miss the
linkage preserves connectedness, since the interior is dense in the
disc. The initial gap point selects the required cover component.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Forget the radial subtype in angular-cover coordinates. -/
@[expose] def cylinderCoverCoordinates (p : CylinderCover) : ℝ × ℝ := (p.1.1, p.2)

/-- Extend the radial-angular cover coordinates to the plane by clamping
radii to the closed cylinder interval. -/
@[expose] noncomputable def planeToCylinderCover (p : ℝ × ℝ) : CylinderCover :=
  (⟨max 1 (min 2 p.1), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩, p.2)

/-- The clamped coordinate map is continuous. -/
theorem continuous_planeToCylinderCover : Continuous planeToCylinderCover :=
  (((continuous_const.max (continuous_const.min continuous_fst)).subtype_mk _).prodMk
    continuous_snd)

/-- Clamping does nothing to a point already in the angular cover. -/
theorem planeToCylinderCover_coordinates (p : CylinderCover) :
    planeToCylinderCover (cylinderCoverCoordinates p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    change max 1 (min 2 p.1.1) = p.1.1
    rw [min_eq_right p.1.2.2, max_eq_right p.1.2.1]
  · rfl

/-- A point of a lifted strip disc that misses the linkage is in the
cover component containing its initial gap point. -/
theorem mem_cylinderCoverStrip_of_mem_disc
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) {D : Set (ℝ × ℝ)}
    (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p : CylinderCover} (hpD : cylinderCoverCoordinates p ∈ D)
    (hp : cylinderCoverProjection p ∉ ⋃ j, (L.pathDrawing j).U) :
    p ∈ cylinderCoverStrip L m := by
  let S := cylinderCoverProjection ⁻¹' (univ \ ⋃ j, (L.pathDrawing j).U)
  let B := planeToCylinderCover '' discInt D
  let C := (planeToCylinderCover '' D) ∩ S
  let b : CylinderCover := (⟨1, by norm_num⟩, (2 * (m : ℝ) + 1) * π / k)
  have hBC : B ⊆ C := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨⟨q, hq.1, rfl⟩, mem_univ _, ?_⟩
    apply stripDiscInterior_projection_not_mem_linkage L hG hθ m hD hBd hstrip hq
    · change max 1 (min 2 q.1) = q.1
      rw [min_eq_right (hstrip hq.1).2, max_eq_right (hstrip hq.1).1]
    · rfl
  have hCcl : C ⊆ closure B := by
    rintro _ ⟨⟨q, hq, rfl⟩, _⟩
    exact mem_closure_image continuous_planeToCylinderCover.continuousAt
      (hD.subset_closure_discInt hq)
  have hC : IsPreconnected C :=
    (hD.isPreconnected_discInt.image planeToCylinderCover
      continuous_planeToCylinderCover.continuousOn).subset_closure hBC hCcl
  have hbD : cylinderCoverCoordinates b ∈ D := by
    apply discBd_subset D
    rw [hBd]
    apply Or.inl
    apply Or.inr
    refine ⟨mem_singleton 1, ?_⟩
    rw [(liftedLinkageCurve_props_raw hG.1 L m).2.2.2.1,
      (liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.2.2.1]
    change 2 * (m : ℝ) * π / k ≤ (2 * (m : ℝ) + 1) * π / k ∧
      (2 * (m : ℝ) + 1) * π / k ≤ 2 * ((m + 1 : ℤ) : ℝ) * π / k
    constructor <;> apply (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hG.1)).mpr
    all_goals push_cast; nlinarith only [pi_pos]
  have hbS : b ∈ S := by
    refine ⟨mem_univ _, ?_⟩
    intro hb
    obtain ⟨j, hj⟩ := mem_iUnion.mp hb
    have hbase : cylinderCoverProjection b = cylinderN1Point k (modIdx k hG.1 m) := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have he := exp_two_mul_int_div_eq_cylinderM1Point hG.1 m
        change Circle.exp (2 * (m : ℝ) * π / k) =
          Circle.exp (2 * (((modIdx k hG.1 m).val + 1 : ℕ) : ℝ) * π / k) at he
        change Circle.exp ((2 * (m : ℝ) + 1) * π / k) =
          Circle.exp ((2 * (((modIdx k hG.1 m).val + 1 : ℕ) : ℝ) + 1) * π / k)
        rw [show (2 * (m : ℝ) + 1) * π / k = 2 * (m : ℝ) * π / k + π / k by ring,
          Circle.exp_add, he, ← Circle.exp_add]
        congr 1
        ring
    rw [hbase] at hj
    exact cylinderN1Point_not_mem_U hG _ ((L.isSubdrawing j).2 hj)
  have hbC : b ∈ C :=
    ⟨⟨cylinderCoverCoordinates b, hbD, planeToCylinderCover_coordinates b⟩, hbS⟩
  exact hC.subset_connectedComponentIn hbC inter_subset_right
    ⟨⟨cylinderCoverCoordinates p, hpD, planeToCylinderCover_coordinates p⟩, mem_univ _, hp⟩

end GraphMinor.GM06
