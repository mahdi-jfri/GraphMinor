module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# Boundary vertices of the one-path cut drawing

For one path, every prescribed cuff vertex is an end of that path.
A drawing vertex on its point set is one of its graph vertices.
The cut-boundary formula then says that the boundary vertices of
the cut drawing are exactly the vertices projecting to the linkage.
Thus the first seam-vertex prefix is also a first boundary-vertex
prefix in the proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- With one linkage path, every original boundary vertex is a vertex
of that path. -/
theorem mem_single_path_vertices_of_boundary_vertex
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) {x : ClosedCylinder}
    (hx : x ∈ G.V) (hxbd : x ∈ bd ClosedCylinder) : x ∈ (L.pathDrawing 0).V := by
  have hpres : x ∈ cylinderM1 1 ∪ cylinderM2 1 := hG.2.2 ▸ ⟨hx, hxbd⟩
  rcases hpres with ⟨j, hj⟩ | hxM2
  · have hj0 : j = 0 := Subsingleton.elim _ _
    rw [hj0] at hj
    exact hj ▸ (isPathDrawing_end_vertices (L.isPath 0)).1
  · obtain ⟨j, hj⟩ := L.curve_one_surjective hxM2
    have hj0 : j = 0 := Subsingleton.elim _ _
    rw [hj0] at hj
    exact hj ▸ (isPathDrawing_end_vertices (L.isPath 0)).2

/-- Boundary vertices of the cut drawing are exactly the full inverse
image of the sole linkage's graph vertices. -/
theorem cut_boundary_vertices_eq_preimage_path_vertices
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D) (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V) :
    F.V ∩ bd D = (fun p : D => radialCylinderProjection p.1) ⁻¹' (L.pathDrawing 0).V := by
  ext p
  constructor
  · rintro ⟨hpV, hpbd⟩
    have hpG : radialCylinderProjection p.1 ∈ G.V := by rw [hFV] at hpV; exact hpV
    rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip] at hpbd
    rcases hpbd with hpcuff | hpP
    · exact mem_single_path_vertices_of_boundary_vertex L hG hpG hpcuff
    · rw [(L.pathDrawing 0).U_eq] at hpP
      rcases hpP with hpPV | hpEdge
      · exact hpPV
      · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp hpEdge
        have hm : radialCylinderProjection p.1 ∈ closure e ∩ (L.pathDrawing 0).V := by
          rw [(L.isSubdrawing 0).1.closure_inter_V he]
          exact ⟨hpe, hpG⟩
        exact hm.2
  · intro hp
    refine ⟨?_, ?_⟩
    · rw [hFV]
      exact (L.isSubdrawing 0).1.1 hp
    · rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
      exact Or.inr ((L.pathDrawing 0).V_subset_U hp)

end GraphMinor.GM06
