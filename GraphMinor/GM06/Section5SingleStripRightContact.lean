module

public import GraphMinor.GM06.Section5SingleStripContact
public import GraphMinor.GM06.Section5CutPathParameter
import GraphMinor.GM06.Section5SinglePathReduction4Apply
import GraphMinor.GM06.Section5CoverLinkageLift
import GraphMinor.GM06.Section5CutSeam
import GraphMinor.GM06.Section5StripImage

/-!
# The one-path contact is on the right seam

The terminal cut vertex lies above the old path, so it belongs to
one of the two seam copies. Its projected vertex is noninitial,
hence its old path parameter is positive. On the left seam the
actual aligned lift of the projected contact path reaches the old
lift at that parameter. The proved old-prefix obstruction then
gives corrected Reduction 4. The no-reduction hypothesis excludes
this case, leaving the right seam, as required in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The constructed contact path reaches the right old-path seam;
a left-seam return would give an actual corrected Reduction 4. -/
theorem exists_right_seam_parameter_of_single_strip_contact
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {s t : D} {Q : Drawing D} (hQ : IsPathDrawing Q s t) (hscoord : s.1 = (1, 2 * π))
    (htV : radialCylinderProjection t.1 ∈ (L.pathDrawing 0).V)
    (htNot : radialCylinderProjection t.1 ≠ cylinderM1Point 1 0)
    (hpoint : Q.U ∩ bd D ⊆ {s, t})
    (hQR : (fun p : D => planeToCylinderCover p.1) '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0))
    {P : Drawing ClosedCylinder} (hP : IsSubpathOf G P (cylinderM1Point 1 0) (radialCylinderProjection t.1))
    (hPU : P.U = (fun p : D => radialCylinderProjection p.1) '' Q.U)
    (hPL : P.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, radialCylinderProjection t.1}) :
    ∃ u : unitInterval, 0 < u ∧ L.curve 0 u ∈ (L.pathDrawing 0).V ∧
      L.curve 0 u = radialCylinderProjection t.1 ∧ t.1 = liftedLinkageCurve hG.1 L 2 u := by
  have hsproj : radialCylinderProjection s.1 = cylinderM1Point 1 0 := by
    rw [hscoord]
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 (1 : ℝ)) = 1
      norm_num
    · change Circle.exp (2 * π) = Circle.exp (2 * (((0 + 1 : ℕ) : ℝ)) * π / (1 : ℕ))
      norm_num
  have hends : radialCylinderProjection s.1 ≠ radialCylinderProjection t.1 := by
    rw [hsproj]
    exact htNot.symm
  obtain ⟨q, hq, hqR, hqEnd⟩ := exists_parameterized_projection_with_cover_lift L hG hθ hD hBd hstrip
    hQ hscoord hpoint hends hPU hQR
  have hproj (n : ℤ) (u : unitInterval) :
      radialCylinderProjection (liftedLinkageCurve hG.1 L n u) = L.curve 0 u := by
    rw [radialCylinderProjection_liftedLinkageCurve]
    have hi : modIdx 1 hG.1 n = 0 := Subsingleton.elim _ _
    rw [hi]
  have hpos (u : unitInterval) (he : L.curve 0 u = radialCylinderProjection t.1) : 0 < u := by
    apply unitInterval.pos_iff_ne_zero.mpr
    intro hu
    rw [hu, (L.curve_parametrizes 0).2.2.1] at he
    exact htNot he.symm
  have htSeam : t.1 ∈ range (liftedLinkageCurve hG.1 L 1) ∪ range (liftedLinkageCurve hG.1 L (1 + 1)) := by
    rw [← preimage_path_inter_single_strip_eq_seams L hG hθ 1 hD hBd hstrip]
    exact ⟨t.2, (L.pathDrawing 0).V_subset_U htV⟩
  rcases htSeam with ⟨u, huΓ⟩ | ⟨u, huΓ⟩
  · have huEq : L.curve 0 u = radialCylinderProjection t.1 :=
      (hproj 1 u).symm.trans (congrArg radialCylinderProjection huΓ)
    have huV : L.curve 0 u ∈ (L.pathDrawing 0).V := huEq.symm ▸ htV
    have hP' : IsSubpathOf G P (cylinderM1Point 1 0) (L.curve 0 u) := by rw [huEq]; exact hP
    have hPL' : P.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, L.curve 0 u} := by rw [huEq]; exact hPL
    have hq' : ParametrizesSet q P.U (cylinderM1Point 1 0) (L.curve 0 u) := by rw [huEq]; exact hq
    have hOld : cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u =
        planeToCylinderCover (liftedLinkageCurve hG.1 L 1 u) := by
      have h := cylinderCurveLiftAt_eq_indexed_linkage_lift hG.1 L 1 u
      have hi : modIdx 1 hG.1 1 = 0 := Subsingleton.elim _ _
      rw [hi] at h
      simpa [cylinderInitialLift] using h
    have hEnd : cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 =
        cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u := by
      calc
        _ = planeToCylinderCover t.1 := hqEnd
        _ = planeToCylinderCover (liftedLinkageCurve hG.1 L 1 u) := congrArg planeToCylinderCover huΓ.symm
        _ = _ := hOld.symm
    exact False.elim (hno (reduction4_applies_of_single_path_left_return L hG hθ hno hval
      hD hBd hstrip u (hpos u huEq) huV hP' hPL' q hq' hqR hEnd))
  · have huEq : L.curve 0 u = radialCylinderProjection t.1 :=
      (hproj (1 + 1) u).symm.trans (congrArg radialCylinderProjection huΓ)
    exact ⟨u, hpos u huEq, huEq.symm ▸ htV, huEq, huΓ.symm⟩

end GraphMinor.GM06
