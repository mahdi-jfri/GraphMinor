module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutRightEdgeExclusion

/-!
# Discarded cut edges miss the clockwise initial copy

For the one-path Reduction 2 argument of VI (5.5), page 130,
clockwise discarded edges have already been exhausted. If a
remaining lifted edge approached the clockwise initial copy, its
cover image would give the clockwise certificate just excluded.
Thus that copy is isolated from all remaining discarded edges.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- A lifted discarded edge with no clockwise certificate cannot
be incident with the clockwise initial copy of the cut disc. -/
theorem right_gap_end_not_mem_closure_cut_edge_of_not_clockwise
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {F : Drawing D} {ec : Set D} (hec : ec ∈ F.E)
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (heq : ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (hno : ¬ IsClockwiseInitialEdge L 0 e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π)) :
    g 1 ∉ closure ec := by
  intro hinc
  let a : D → CylinderCover := fun p => planeToCylinderCover p.1
  have hpoint : a (g 1) = (⟨1, by norm_num⟩, 4 * π) := by
    apply Prod.ext
    · apply Subtype.ext
      change max 1 (min 2 (g 1).1.1) = 1
      rw [hgcoord 1]
      norm_num
    · change (g 1).1.2 = 4 * π
      rw [hgcoord 1]
      norm_num
  have hcover : (⟨1, by norm_num⟩, 4 * π) ∈ closure (a '' ec) := by
    rw [← hpoint]
    exact mem_closure_image
      (continuous_planeToCylinderCover.comp continuous_subtype_val).continuousAt hinc
  exact hno (isClockwiseInitialEdge_of_right_cut_edge_incidence
    L hG hθ hD hBd hstrip hec he heP heq hcover)

end GraphMinor.GM06
