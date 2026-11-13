module

public import GraphMinor.GM06.Section5CutPointContact
import GraphMinor.GM06.Section5CutInitialFiber
import GraphMinor.GM06.Section5CutRightEdgeExclusion
import GraphMinor.GM06.Section5NextContact
import GraphMinor.GM06.Section5EndpointObstruction

/-!
# The cut path cannot terminate above the initial vertex

The initial fiber consists of the two gap ends. A nondegenerate
path cannot return to its own start. If it reached the other copy,
its terminal edge would be a full lifted original non-seam edge,
since the path meets the boundary only at its ends. Such an edge
at the right initial copy permits corrected Reduction 1. This
excludes the initial terminal contact in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- A first-contact cut path whose interior avoids the boundary cannot
end above the original initial vertex in the unreduced case. -/
theorem cut_first_contact_terminal_not_initial
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D}
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    {v : D} {Q : Drawing D} (hQ : IsSubpathOf F Q (g 0) v)
    (hpoint : Q.U ∩ bd D ⊆ {g 0, v}) :
    radialCylinderProjection v.1 ≠ cylinderM1Point 1 0 := by
  intro hv
  have hv1 : v = g 1 := by
    rcases eq_gap_end_of_projecting_to_initial L hG hθ hD hBd hstrip g hgcoord hv with h | h
    · exact False.elim (isPathDrawing_start_ne_end hQ.2.2 h.symm)
    · exact h
  obtain ⟨ec, heQ, hvec⟩ := exists_terminal_edge hQ.2.2
  have hec := hQ.1.2 heQ
  have heDis := edge_disjoint_of_path_point_contact hQ.2.2 hpoint heQ
  obtain ⟨e, he, heq⟩ : ∃ e ∈ G.E \ (L.pathDrawing 0).E,
      ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
    rcases hEdges ec hec with heBd | h
    · obtain ⟨p, hp⟩ := heQ.1
      exact False.elim (disjoint_left.mp heDis hp (heBd hp))
    · exact h
  have ha1 : planeToCylinderCover (g 1).1 = (⟨1, by norm_num⟩, 4 * π) := by
    rw [hgcoord]
    apply Prod.ext
    · apply Subtype.ext
      change max 1 (min 2 (1 : ℝ)) = 1
      norm_num
    · change 2 * (1 + (1 : ℝ)) * π = 4 * π
      ring
  have hinc : (⟨1, by norm_num⟩, 4 * π) ∈
      closure ((fun p : D => planeToCylinderCover p.1) '' ec) := by
    rw [← ha1]
    exact mem_closure_image
      (continuous_planeToCylinderCover.comp continuous_subtype_val).continuousAt (hv1 ▸ hvec)
  exact not_right_initialLift_mem_closure_cut_edge L hG hθ hno hD hBd hstrip hec he.1 he.2 heq hinc

end GraphMinor.GM06
