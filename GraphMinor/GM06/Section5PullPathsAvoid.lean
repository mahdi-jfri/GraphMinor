module

public import GraphMinor.GM06.Section5PullPaths
import GraphMinor.GM11.Walks
import GraphMinor.GM07.NetExists

/-!
# Pulling back a path while preserving edge exclusion

For VI (5.1), page 129, the frontier path in the capped sphere must
avoid the added cuff edge after it is pulled back. Every edge of the
pulled-back subpath maps to an edge of the original sphere path.
At an interior point of that edge, the sphere path has an edge, and
uniqueness of drawing edges identifies it with the image edge.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- If the image of a subdrawing lies in a sphere subdrawing, each
of its edges maps to an edge of that sphere subdrawing. -/
theorem image_edges_subset_of_sphere_subdrawing
    {G Q : Drawing ClosedCylinder} {P : Drawing (OnePoint EuclideanPlane)}
    (hQ : Q.IsSubdrawing G) (hP : P.IsSubdrawing (cylinderSphereDrawing G))
    (hU : cylinderToSphere '' Q.U ⊆ P.U) :
    (image cylinderToSphere) '' Q.E ⊆ P.E := by
  rintro f ⟨e, he, rfl⟩
  have heG := hQ.2 he
  obtain ⟨x, hx⟩ := he.1
  have hxP : cylinderToSphere x ∈ P.U := hU ⟨x, (he.2.1 hx).1, rfl⟩
  have hxPV : cylinderToSphere x ∉ P.V := by
    intro hxV
    have hxD := hP.1 hxV
    rw [cylinderSphereDrawing_V] at hxD
    obtain ⟨y, hy, hyx⟩ := hxD
    exact (heG.2.1 hx).2 ((injective_cylinderToSphere hyx) ▸ hy)
  obtain ⟨f, hf, hxf⟩ := P.exists_edge_of_mem hxP hxPV
  have hie : cylinderToSphere '' e ∈ (cylinderSphereDrawing G).E := by
    rw [cylinderSphereDrawing_E]
    exact ⟨e, heG, rfl⟩
  have hef := GM07.arcComponentsIn_eq_of_mem hie (hP.2 hf) (mem_image_of_mem _ hx) hxf
  exact hef.symm ▸ hf

/-- A sphere subpath avoiding the image of an edge pulls back to a
cylinder subpath avoiding that edge. -/
theorem exists_subpath_of_sphere_subpath_avoiding_edge
    {G : Drawing ClosedCylinder} {P : Drawing (OnePoint EuclideanPlane)}
    {a b : ClosedCylinder} (hab : a ≠ b)
    (hP : IsSubpathOf (cylinderSphereDrawing G) P (cylinderToSphere a) (cylinderToSphere b))
    {e : Set ClosedCylinder} (he : cylinderToSphere '' e ∉ P.E) :
    ∃ Q : Drawing ClosedCylinder, IsSubpathOf G Q a b ∧
      cylinderToSphere '' Q.U ⊆ P.U ∧ e ∉ Q.E := by
  obtain ⟨Q, hQ, hU⟩ := exists_subpath_of_sphere_subpath hab hP
  have hE := image_edges_subset_of_sphere_subdrawing hQ.1 hP.1 hU
  exact ⟨Q, hQ, hU, fun heQ => he (hE ⟨e, heQ, rfl⟩)⟩

end GraphMinor.GM06
