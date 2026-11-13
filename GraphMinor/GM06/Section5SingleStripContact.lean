module

public import GraphMinor.GM06.Section5CutProjectedPath
import GraphMinor.GM06.Section5CutFirstContact
import GraphMinor.GM06.Section5CutTerminalExclusion

/-!
# The original contact path obtained from the one-path cut disc

Construct the first seam-vertex prefix along the chosen region
boundary. At larger valency its interior misses the whole cut
boundary, and corrected Reduction 1 excludes a terminal initial
copy. Projection then gives an original graph path with no other
linkage contacts. This assembles the path construction preceding
the rerouting and winding steps of VI (5.1), page 129, for one path.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The one-path cut-disc boundary argument supplies an original
contact path, its cut lift, and their exact point-set correspondence. -/
theorem exists_single_strip_original_contact_path
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    ∃ (s t : D) (Q : Drawing D) (P : Drawing ClosedCylinder),
      s.1 = (1, 2 * π) ∧ radialCylinderProjection t.1 ∈ (L.pathDrawing 0).V ∧
      radialCylinderProjection t.1 ≠ cylinderM1Point 1 0 ∧ IsSubpathOf F Q s t ∧
      (fun p : D => planeToCylinderCover p.1) '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0) ∧
      Q.U ∩ bd D ⊆ {s, t} ∧
      IsSubpathOf G P (cylinderM1Point 1 0) (radialCylinderProjection t.1) ∧
      P.U = (fun p : D => radialCylinderProjection p.1) '' Q.U ∧
      P.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, radialCylinderProjection t.1} := by
  have hEdges' : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
    intro ec hec
    rcases hEdges ec hec with hbd | ⟨e, he, heq⟩
    · exact Or.inl hbd
    · exact Or.inr ⟨e, he.1, heq⟩
  obtain ⟨g, t, Q, b, hgcoord, htP, _, hQ, hQR, hQV, hb, hbBd, hgap, hbQ⟩ :=
    exists_single_strip_first_contact_path L hG hθ hno hD hBd hstrip F hFU hFV hEdges'
  obtain ⟨_, hpoint⟩ := cut_first_contact_path_point_contact L hG hθ hno hval hD hBd hstrip
    F hFU hFV hEdges g hgcoord hQ hQR hQV hb hbBd hgap hbQ
  have htNot := cut_first_contact_terminal_not_initial L hG hθ hno hD hBd hstrip hEdges g hgcoord hQ hpoint
  have hscoord : (g 0).1 = (1, 2 * π) := by simpa using hgcoord 0
  have hsproj : radialCylinderProjection (g 0).1 = cylinderM1Point 1 0 := by
    rw [hscoord]
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 (1 : ℝ)) = 1
      norm_num
    · change Circle.exp (2 * π) = Circle.exp (2 * (((0 + 1 : ℕ) : ℝ)) * π / (1 : ℕ))
      norm_num
  have hends : radialCylinderProjection (g 0).1 ≠ radialCylinderProjection t.1 := by
    rw [hsproj]
    exact htNot.symm
  obtain ⟨P, hP, hPU, hPL⟩ := exists_original_path_of_cut_path_point_contact L hG hθ hD hBd hstrip
    hFV hEdges hQ hpoint hends
  rw [hsproj] at hP hPL
  exact ⟨g 0, t, Q, P, hscoord, htP, htNot, hQ, hQR, hpoint, hP, hPU, hPL⟩

end GraphMinor.GM06
