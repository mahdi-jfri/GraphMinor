module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section5BoundaryConnected
import GraphMinor.GM06.Section5DrawingConnected
import GraphMinor.GM11.ArcDrawings
import GraphMinor.GM11.RadialBasics
import GraphMinor.Surface.Cylinder

/-!
# A drawing with the cuff arcs adjoined

For the region-boundary argument in VI (5.1), page 129, put edges on
the cuffs between the prescribed vertices. Properness says the cuffs
meet G only at these vertices. The two cuff drawings and G can thus
be glued along their common vertices. No vertex is added to G, and
the resulting point set is U(G) together with the boundary.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

/-- Adjoining the cuff arcs to a Section 5 drawing containing a linkage
adds the boundary to its point set and keeps its vertex set. -/
theorem exists_drawing_adjoining_boundary
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) :
    ∃ F : Drawing ClosedCylinder, G.IsSubdrawing F ∧
      F.U = G.U ∪ bd ClosedCylinder ∧ F.V = G.V := by
  let i : Fin k := ⟨0, hG.1⟩
  have hverts := L.boundary_vertices_subset (fun j => (L.isSubdrawing j).1)
  have hsV : cylinderM1Point k i ∈ G.V := hverts (Or.inl ⟨i, rfl⟩)
  have htV : L.curve i 1 ∈ G.V := hverts (Or.inr (L.curve_one_mem i))
  have htC : L.curve i 1 ∈ cylinderCuff2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [← hj]
    rfl
  obtain ⟨D₁, hU₁, hV₁⟩ := exists_drawing_on_oArc isOArc_cylinderCuff1
    (G.finite_V.inter_of_left cylinderCuff1) ⟨cylinderM1Point k i, hsV, rfl⟩ inter_subset_right
  obtain ⟨D₂, hU₂, hV₂⟩ := exists_drawing_on_oArc isOArc_cylinderCuff2
    (G.finite_V.inter_of_left cylinderCuff2) ⟨L.curve i 1, htV, htC⟩ inter_subset_right
  have hmeet : D₁.U ∩ D₂.U ⊆ D₁.V ∩ D₂.V := by
    rw [hU₁, hU₂]
    intro x hx
    exact False.elim (disjoint_left.mp disjoint_cylinderCuffs hx.1 hx.2)
  let B := D₁.glue D₂ hmeet
  have hBU : B.U = bd ClosedCylinder := by
    change D₁.U ∪ D₂.U = _
    rw [hU₁, hU₂, bd_closedCylinder]
  have hBV : B.V = G.V ∩ bd ClosedCylinder := by
    change D₁.V ∪ D₂.V = _
    rw [hV₁, hV₂, bd_closedCylinder, inter_union_distrib_left]
  have hGB : G.U ∩ B.U ⊆ G.V ∩ B.V := by
    rw [hBU, hBV]
    intro x hx
    exact ⟨hG.2.1 ⟨hx.2, hx.1⟩, hG.2.1 ⟨hx.2, hx.1⟩, hx.2⟩
  let F := G.glue B hGB
  refine ⟨F, ?_, ?_, ?_⟩
  · constructor
    · exact subset_union_left
    · rw [Drawing.glue_E]
      exact subset_union_left
  · change G.U ∪ B.U = _
    rw [hBU]
  · change G.V ∪ B.V = G.V
    rw [hBV]
    exact union_eq_left.mpr inter_subset_left

/-- In the unreduced situation of VI (5.1), the drawing with cuff arcs
adjoined is connected, with exactly the original vertices. -/
theorem exists_connected_drawing_adjoining_boundary
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L) :
    ∃ F : Drawing ClosedCylinder, G.IsSubdrawing F ∧
      F.U = G.U ∪ bd ClosedCylinder ∧ F.V = G.V ∧ IsGraphConnected F.toGraph := by
  obtain ⟨F, hGF, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
  have hconn : IsConnected F.U := by
    rw [hFU]
    exact isConnected_union_boundary_of_no_section5_reduction L hG hno
  let i : Fin k := ⟨0, hG.1⟩
  have hsV : cylinderM1Point k i ∈ F.V := by
    rw [hFV]
    exact L.boundary_vertices_subset (fun j => (L.isSubdrawing j).1) (Or.inl ⟨i, rfl⟩)
  exact ⟨F, hGF, hFU, hFV, isGraphConnected_of_isPreconnected_U hconn.isPreconnected ⟨_, hsV⟩⟩

end GraphMinor.GM06
