module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverRerouting

/-!
# The one-path rerouting preserves winding

The side-sensitive Reduction 4 reaches the same lifted contact as the
old prefix. Parameterize its old tail, including the constant tail at
a terminal contact, and compare the old and new concatenations. For
one path the terminal cuff has only one prescribed point, so both full
paths have the same ends. The lifted-contact winding lemma applies.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The lifted incidence data for Reduction 4 preserve the common winding
for one path. Winding equality follows from the actual prefix and tail
curves and is not an assumption in the incidence condition. -/
theorem theta_eq_of_sided_reduction4_one
    {G G' : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) (L' : CylinderLinkage 1 G')
    {θ θ' : ℝ} (hL : L.HasTheta θ) (hL' : L'.HasTheta θ')
    (hside : Section5Reduction4SideCondition 1 G L G' L') : θ' = θ := by
  obtain ⟨i, u, T, Q, q, _, _, _, hT, _, _, _, hq, _, hend, hU, _⟩ := hside
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  obtain ⟨j, hj⟩ := L.curve_one_mem 0
  obtain ⟨j', hj'⟩ := L'.curve_one_mem 0
  have ht : L'.curve 0 1 = L.curve 0 1 :=
    hj'.symm.trans ((congrArg (cylinderM2Point 1) (Subsingleton.elim j' j)).trans hj)
  obtain ⟨r, hrT, hr0, hr1, hrP⟩ :
      ∃ r : Curve ClosedCylinder, range r ⊆ T.U ∧ r 0 = L.curve 0 u ∧
        r 1 = L.curve 0 1 ∧ range r ⊆ (L.pathDrawing 0).U := by
    rcases hT with ⟨hvt, hTU, _⟩ | hT
    · let r : Curve ClosedCylinder := ContinuousMap.const _ (L.curve 0 u)
      refine ⟨r, ?_, rfl, hvt, ?_⟩
      · rintro _ ⟨x, rfl⟩
        rw [hTU]
        exact mem_singleton _
      · rintro _ ⟨x, rfl⟩
        exact (L.curve_parametrizes 0).2.1 ▸ mem_range_self u
    · obtain ⟨r, hr⟩ := hT.2.2.2
      refine ⟨r, ?_, hr.2.2.1, hr.2.2.2, ?_⟩
      · rw [hr.2.1]
      · rw [hr.2.1]
        exact hT.2.1
  let qp : Path (cylinderM1Point 1 0) (L.curve 0 u) := ⟨q, hq.2.2.1, hq.2.2.2⟩
  let rp : Path (L.curve 0 u) (L.curve 0 1) := ⟨r, hr0, hr1⟩
  have hqR : range qp ⊆ (L'.pathDrawing 0).U := by
    change range q ⊆ _
    rw [hq.2.1, hU]
    exact subset_union_left
  have hrR : range rp ⊆ (L'.pathDrawing 0).U := by
    rw [hU]
    exact hrT.trans subset_union_right
  have hR : IsPathDrawing (L'.pathDrawing 0) (cylinderM1Point 1 0) (L.curve 0 1) := by
    simpa only [ht] using L'.isPath 0
  have hg : ParametrizesSet (L'.curve 0) (L'.pathDrawing 0).U
      (cylinderM1Point 1 0) (L.curve 0 1) := by
    have hg := L'.curve_parametrizes 0
    exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.trans ht⟩
  have hw := windingNumber_eq_of_rerouting_lifted_contact (L.isPath 0) hR
    (L.curve 0) (L'.curve 0) (L.curve_parametrizes 0) hg qp rp hqR hrR hrP
    u rfl (cylinderInitialLift 1 0).2 rfl (congrArg Prod.snd hend)
  rw [← hL' 0, ← hL 0]
  exact hw

end GraphMinor.GM06
