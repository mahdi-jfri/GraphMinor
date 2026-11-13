module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM11.CircuitRegions
import GraphMinor.GM11.Walks
import GraphMinor.GM07.NetExists

/-!
# Every original non-seam edge occurs in the cut drawing

A point on an original edge off the linkage lies off both cylinder
cuffs and the linkage. All its cut-disc preimages are therefore
interior points. The augmented drawing contains those points but
has no vertex there. Its edge classification identifies the edge
through such a point with the full preimage of the original edge.
This gives the reverse edge correspondence needed to lift graph
paths in the one-path argument of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The full lift of an original non-seam edge misses the cut-disc boundary. -/
theorem preimage_non_seam_edge_disjoint_boundary
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E) :
    Disjoint ((fun p : D => radialCylinderProjection p.1) ⁻¹' e) (bd D) := by
  apply disjoint_left.mpr
  intro p hp hpbd
  have hboundary := preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip
  rw [← hboundary] at hpbd
  rcases hpbd with hpcuff | hpP
  · exact (he.2.1 hp).2 (hG.2.1 ⟨hpcuff, (he.2.1 hp).1⟩)
  · exact disjoint_left.mp (GM11.edge_disjoint_U (L.isSubdrawing 0).1 he heP) hp hpP

/-- Every original edge off the linkage has its full preimage as an
edge in any augmented cut drawing with the stated vertex and edge sets. -/
theorem full_preimage_non_seam_edge_mem
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E) :
    (fun p : D => radialCylinderProjection p.1) ⁻¹' e ∈ F.E := by
  obtain ⟨z, hz⟩ := he.1
  obtain ⟨p, hp⟩ := surjective_single_strip_projection L hG hθ hD hBd hstrip z
  have hpe : radialCylinderProjection p.1 ∈ e := by
    change (fun p : D => radialCylinderProjection p.1) p ∈ e
    rw [hp]
    exact hz
  have hpF : p ∈ F.U := by rw [hFU]; exact Or.inl ((he.2.1 hpe).1)
  have hpV : p ∉ F.V := by rw [hFV]; exact (he.2.1 hpe).2
  obtain ⟨ec, hec, hpec⟩ := F.exists_edge_of_mem hpF hpV
  rcases hEdges ec hec with hecBd | ⟨e', he', heq⟩
  · exact False.elim (disjoint_left.mp
      (preimage_non_seam_edge_disjoint_boundary L hG hθ hD hBd hstrip he heP)
      hpe (hecBd hpec))
  · rw [heq] at hpec
    have he'e : e' = e := GM07.arcComponentsIn_eq_of_mem he' he hpec hpe
    rw [he'e] at heq
    exact heq ▸ hec

end GraphMinor.GM06
