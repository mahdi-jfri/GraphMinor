module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DrawingImage
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM06.Section5Red

/-!
# The drawing obtained by collapsing the initial edge

For Reduction 3 of VI, page 129, take the image of the drawing with
the initial vertex deleted. The deleted edge has constant image,
already represented by its surviving endpoint. Thus the point and
vertex sets are the images of the original sets, while the edge set
is the image of all edges except the collapsed edge.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The continuous edge collapse gives the exact point, vertex, and
edge sets required in Reduction 3. -/
theorem exists_contracted_initial_edge_drawing
    {k : ℕ} {G : Drawing ClosedCylinder} {i : Fin k}
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure a)
    (hi : InjOn π (closure a)ᶜ) :
    ∃ H : Drawing ClosedCylinder,
      H.U = π '' G.U ∧ H.V = π '' G.V ∧
      H.E = (image π) '' (G.E \ {a}) := by
  let J := induceDrawing G (G.V \ {cylinderM1Point k i})
  obtain ⟨hJE, hinter, hGU⟩ := deleted_initial_vertex_drawing hval hl hvs
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_drawing_image_of_injOn_pointSet J π
    (injOn_deleted_initial_vertex_drawing hval hl hvs hfiber hi)
  have hvcl : v ∈ closure a :=
    (show v ∈ closure a ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
  have hvJ : v ∈ J.V := by
    rw [induceDrawing_V G sdiff_subset]
    exact ⟨hl.2.2.1, hvs⟩
  have hπv : π v = cylinderM1Point k i := by
    have hvpre : v ∈ π ⁻¹' {cylinderM1Point k i} := by rw [hfiber]; exact hvcl
    exact hvpre
  have hπcl : ∀ x ∈ closure a, π x = π v := by
    intro x hx
    have hxpre : x ∈ π ⁻¹' {cylinderM1Point k i} := by rw [hfiber]; exact hx
    exact hxpre.trans hπv.symm
  refine ⟨H, hHU.trans ?_, hHV.trans ?_, ?_⟩
  · apply subset_antisymm (image_mono (induceDrawing_isSubdrawing G sdiff_subset).U_subset)
    rintro y ⟨x, hx, rfl⟩
    rw [hGU] at hx
    rcases hx with hxJ | hxa
    · exact mem_image_of_mem π hxJ
    · exact ⟨v, J.V_subset_U hvJ, (hπcl x hxa).symm⟩
  · apply subset_antisymm (image_mono (induceDrawing_isSubdrawing G sdiff_subset).1)
    rintro y ⟨x, hx, rfl⟩
    by_cases hxs : x = cylinderM1Point k i
    · have hxcl : x ∈ closure a := by
        rw [hxs]
        exact (show cylinderM1Point k i ∈ closure a ∩ G.V from
          hl.2.2.2.symm ▸ mem_insert _ {v}).1
      exact ⟨v, hvJ, (hπcl x hxcl).symm⟩
    · refine ⟨x, ?_, rfl⟩
      rw [induceDrawing_V G sdiff_subset]
      exact ⟨hx, hxs⟩
  · exact hHE.trans (congrArg (image (image π)) hJE)

end GraphMinor.GM06
