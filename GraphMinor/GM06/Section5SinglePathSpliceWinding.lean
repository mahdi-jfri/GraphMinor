module

public import GraphMinor.GM06.Section5CoverLinkageLift
import GraphMinor.GM06.Section5CoverRerouting

/-!
# Splicing at the right seam increases winding by one

The right old-path lift is the left lift translated by one full
turn. A contact path reaching the right lift therefore has one
more winding than the old prefix. Parametrize the shared old tail,
including the singleton terminal tail, and apply the proved
shifted-contact winding comparison to the full path. This is the
one-path winding calculation in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

private theorem exists_curve_in_tail
    {P T : Drawing ClosedCylinder} {v t : ClosedCylinder}
    (hT : IsSection5Tail P T v t) :
    ∃ r : Curve ClosedCylinder, range r ⊆ T.U ∧ r 0 = v ∧ r 1 = t := by
  rcases hT with ⟨hvt, hTU, _⟩ | hT
  · let r : Curve ClosedCylinder := ContinuousMap.const _ v
    refine ⟨r, ?_, rfl, hvt⟩
    rintro x ⟨u, rfl⟩
    rw [hTU]
    exact mem_singleton v
  · obtain ⟨r, hr⟩ := hT.2.2.2
    exact ⟨r, hr.2.1 ▸ Subset.rfl, hr.2.2.1, hr.2.2.2⟩

/-- An original contact path whose aligned lift reaches the right seam,
followed by the old tail, gives a full path with winding increased by one. -/
theorem windingNumber_single_path_right_contact_splice
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (u : unitInterval)
    {Q T R : Drawing ClosedCylinder}
    (q : Curve ClosedCylinder) (hq : ParametrizesSet q Q.U (cylinderM1Point 1 0) (L.curve 0 u))
    (hqEnd : cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 =
      planeToCylinderCover (liftedLinkageCurve hG.1 L 2 u))
    (hT : IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1))
    (hTP : T.IsSubdrawing (L.pathDrawing 0))
    (hR : IsPathDrawing R (cylinderM1Point 1 0) (L.curve 0 1))
    (hRU : R.U = Q.U ∪ T.U)
    (g : Curve ClosedCylinder) (hg : ParametrizesSet g R.U (cylinderM1Point 1 0) (L.curve 0 1)) :
    windingNumber g = windingNumber (L.curve 0) + 1 := by
  obtain ⟨r, hrT, hr0, hr1⟩ := exists_curve_in_tail hT
  let qp : Path (cylinderM1Point 1 0) (L.curve 0 u) := ⟨q, hq.2.2.1, hq.2.2.2⟩
  let rp : Path (L.curve 0 u) (L.curve 0 1) := ⟨r, hr0, hr1⟩
  have hqR : range qp ⊆ R.U := by change range q ⊆ _; rw [hq.2.1, hRU]; exact subset_union_left
  have hrR : range rp ⊆ R.U := by rw [hRU]; exact hrT.trans subset_union_right
  have hrP : range rp ⊆ (L.pathDrawing 0).U := hrT.trans hTP.U_subset
  have hOld : (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u).2 =
      (liftedLinkageCurve hG.1 L 1 u).2 := by
    have h := cylinderCurveLiftAt_eq_indexed_linkage_lift hG.1 L 1 u
    have hi : modIdx 1 hG.1 1 = 0 := Subsingleton.elim _ _
    rw [hi] at h
    simpa [cylinderInitialLift, planeToCylinderCover] using congrArg Prod.snd h
  have hShift : (liftedLinkageCurve hG.1 L 2 u).2 =
      (liftedLinkageCurve hG.1 L 1 u).2 + 2 * π := by
    simpa only [Nat.cast_one, Int.cast_one, one_mul, mul_one, Int.reduceAdd] using
      congrArg Prod.snd (liftedLinkageCurve_add_mul hG.1 L 1 1 u)
  have hend : (cylinderCurveLiftAt qp.toContinuousMap (cylinderInitialLift 1 0).2 1).2 =
      (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u).2 + 2 * π * 1 := by
    have hqA := congrArg Prod.snd hqEnd
    change (cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1).2 = _
    change (cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1).2 =
      (liftedLinkageCurve hG.1 L 2 u).2 at hqA
    rw [hqA, hOld, hShift, mul_one]
  exact windingNumber_eq_add_of_rerouting_lifted_contact (L.isPath 0) hR
    (L.curve 0) g (L.curve_parametrizes 0) hg qp rp hqR hrR hrP
    u rfl (cylinderInitialLift 1 0).2 rfl 1 hend

end GraphMinor.GM06
