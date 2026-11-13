module

public import GraphMinor.GM06.Section5CoverLinkageLift
import GraphMinor.GM06.Section5PathLiftMeet

/-!
# Lifted prefixes stay on the left linkage seam

A curve inside a linkage path and starting at its initial vertex
meets the old parametrization at each of its points. Equality of
aligned lifts at path meetings places its lift on the indexed left
seam. The same argument gives equality of lifted point sets when
two curves cover the whole path. These facts are used in the
one-path Reduction 4 progress proof of VI Section 5, page 129.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A curve contained in the sole linkage path, starting at its initial
vertex, has its canonical aligned lift on the left indexed seam. -/
theorem exists_left_seam_parameter_of_path_prefix
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (q : Curve ClosedCylinder)
    (hqP : range q ⊆ (L.pathDrawing 0).U) (hq0 : q 0 = cylinderM1Point 1 0)
    (t : unitInterval) :
    ∃ u : unitInterval, q t = L.curve 0 u ∧
      cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 t =
        planeToCylinderCover (liftedLinkageCurve hG.1 L 1 u) := by
  obtain ⟨u, hu⟩ := (L.curve_parametrizes 0).2.1.symm ▸ hqP (mem_range_self t)
  have hMeet := aligned_curve_lifts_eq_at_path_meeting (L.isPath 0) (L.curve 0)
    (L.curve_parametrizes 0) q hqP hq0 (cylinderInitialLift 1 0).2 rfl hu.symm
  have hOld : cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u =
      planeToCylinderCover (liftedLinkageCurve hG.1 L 1 u) := by
    have h := cylinderCurveLiftAt_eq_indexed_linkage_lift hG.1 L 1 u
    have hi : modIdx 1 hG.1 1 = 0 := Subsingleton.elim _ _
    rw [hi] at h
    simpa [cylinderInitialLift] using h
  exact ⟨u, hu.symm, hMeet.trans hOld⟩

/-- Curves covering the same path and sharing its initial vertex
have exactly the same aligned lifted point set. -/
theorem range_aligned_lift_eq_of_range_eq_path
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (f : Curve ClosedCylinder)
    (hf : ParametrizesSet f P.U s t) (q : Curve ClosedCylinder)
    (hRange : range q = P.U) (hq0 : q 0 = s) (a : ℝ) (ha : Circle.exp a = s.1.2) :
    range (cylinderCurveLiftAt q a) = range (cylinderCurveLiftAt f a) := by
  have hqP : range q ⊆ P.U := hRange ▸ Subset.rfl
  apply subset_antisymm
  · rintro p ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := hf.2.1.symm ▸ hqP (mem_range_self u)
    exact ⟨v, (aligned_curve_lifts_eq_at_path_meeting hP f hf q hqP hq0 a ha hv.symm).symm⟩
  · rintro p ⟨v, rfl⟩
    have hvP : f v ∈ P.U := hf.2.1 ▸ mem_range_self v
    obtain ⟨u, hu⟩ := hRange.symm ▸ hvP
    exact ⟨u, aligned_curve_lifts_eq_at_path_meeting hP f hf q hqP hq0 a ha hu⟩

end GraphMinor.GM06
