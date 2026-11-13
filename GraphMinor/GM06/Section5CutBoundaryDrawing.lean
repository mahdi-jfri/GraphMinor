module

public import GraphMinor.GM06.Section5CutEdgePreimage
import GraphMinor.GM06.Section5BoundarySubdrawing
import GraphMinor.GM06.DiscRegions

/-!
# The boundary subdrawing of the one-path cut disc

Every edge of the augmented cut drawing either lies on the boundary
or is the full preimage of an original non-linkage edge. The latter
misses the boundary. The closed-union construction therefore gives
a subdrawing whose point set is exactly the disc boundary and whose
vertices are exactly the boundary vertices. This is the target
subdrawing in the point-contact step of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The full boundary of the augmented cut drawing is the point set
of a subdrawing, with exactly its boundary vertices. -/
theorem exists_boundary_subdrawing_on_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    ∃ B : Drawing D, B.IsSubdrawing F ∧ B.V = F.V ∩ bd D ∧ B.U = bd D := by
  have hbdClosed := isClosed_bd_of_isClosedDiscSpace (show IsClosedDiscSpace D from hD)
  have hbdF : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  apply exists_subdrawing_on_closed_union_of_edges F hbdClosed hbdF
  intro ec hec hmeet
  rcases hEdges ec hec with hbd | ⟨e, he, heq⟩
  · exact hbd
  · obtain ⟨p, hp, hpbd⟩ := hmeet
    rw [heq] at hp
    exact False.elim (disjoint_left.mp
      (preimage_non_seam_edge_disjoint_boundary L hG hθ hD hBd hstrip he.1 he.2) hp hpbd)

end GraphMinor.GM06
