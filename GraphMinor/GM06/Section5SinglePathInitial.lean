module

public import GraphMinor.GM06.Section5SingleStripRightContact
import GraphMinor.GM06.Section5SinglePathSuccessor
import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5CutStripBoundary

/-!
# The one-path case of VI (5.1)

Cut the cylinder along the sole linkage path. The proved region
argument constructs a path from the left initial copy to a
noninitial vertex on the right seam. Its projection is an original
graph path with no other old-path contacts. Parametrize it with its
actual aligned cover lift, splice on the old tail, and use the
proved full-turn winding increment. This completes the larger-valency
one-path case of VI (5.1), page 129, for the corrected reductions.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Graph Minors VI, (5.1), page 129, in the one-path case with initial
valency different from one, using the corrected side conditions. -/
theorem isThetaFeasible_successor_of_single_path_unreduced
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1) :
    IsThetaFeasible 1 G (θ + 1) := by
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ 1
  obtain ⟨F, hFU, hFV, hEdges⟩ := exists_augmented_drawing_on_single_strip L hG hθ hD hBd hstrip
  obtain ⟨s, t, Q, P, hscoord, htV, htNot, hQ, hQR, hpoint, hP, hPU, hPL⟩ :=
    exists_single_strip_original_contact_path L hG hθ hno hval hD hBd hstrip F hFU hFV hEdges
  obtain ⟨u, hu, huV, huEq, htΓ⟩ := exists_right_seam_parameter_of_single_strip_contact L hG hθ hno hval
    hD hBd hstrip hQ.2.2 hscoord htV htNot hpoint hQR hP hPU hPL
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
  obtain ⟨q, hq, _, hqEnd⟩ := exists_parameterized_projection_with_cover_lift L hG hθ hD hBd hstrip
    hQ.2.2 hscoord hpoint hends hPU hQR
  have hP' : IsSubpathOf G P (cylinderM1Point 1 0) (L.curve 0 u) := by rw [huEq]; exact hP
  have hPL' : P.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, L.curve 0 u} := by rw [huEq]; exact hPL
  have hq' : ParametrizesSet q P.U (cylinderM1Point 1 0) (L.curve 0 u) := by rw [huEq]; exact hq
  rw [htΓ] at hqEnd
  exact isThetaFeasible_successor_of_single_path_right_contact L hG hθ u hu huV hP' hPL' q hq' hqEnd

end GraphMinor.GM06
