module

public import GraphMinor.GM06.Section5CutEdgePreimage
public import GraphMinor.GM11.Defs
import GraphMinor.GM11.Section5

/-!
# Edge deletion in the augmented cut-disc drawing

In the one-path Reduction 1 proof of VI (5.5), delete the full lift
of the original edge from the augmented cut drawing. This is an
actual edge and misses the disc boundary. Its deletion therefore
commutes with pulling back the original drawing and adjoining the
boundary. The vertex set is unchanged, as in the cylinder reduction.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11

/-- Deleting the full lifted edge produces the required augmented
cut drawing of the reduced cylinder graph in VI (5.5). -/
theorem full_preimage_edge_deletion_on_single_strip
    {G G' : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (hU : G'.U = G.U \ e) (hV : G'.V = G.V) :
    let ec := (fun p : D => radialCylinderProjection p.1) ⁻¹' e
    ec ∈ F.E ∧ Disjoint ec (bd D) ∧
      (F.deleteEdge ec).U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G'.U ∪ bd D ∧
      (F.deleteEdge ec).V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G'.V := by
  dsimp only
  let ec := (fun p : D => radialCylinderProjection p.1) ⁻¹' e
  have hec := full_preimage_non_seam_edge_mem L hG hθ hD hBd hstrip F hFU hFV hEdges he heP
  have heBd := preimage_non_seam_edge_disjoint_boundary L hG hθ hD hBd hstrip he heP
  refine ⟨hec, heBd, ?_, ?_⟩
  · rw [deleteEdge_U F hec, hFU, hU]
    ext p
    constructor
    · rintro ⟨hx | hx, hno⟩
      · exact Or.inl ⟨hx, hno⟩
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨Or.inl hx.1, hx.2⟩
      · exact ⟨Or.inr hx, fun h => disjoint_left.mp heBd h hx⟩
  · rw [deleteEdge_V, hFV, hV]

end GraphMinor.GM06
