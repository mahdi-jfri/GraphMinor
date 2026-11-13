module

public import GraphMinor.GM06.Section5CapDrawing
import GraphMinor.GM06.Section5WalkSubpaths
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM07.Matched
import GraphMinor.GM11.Walks

/-!
# Pulling sphere paths back to the cylinder

The region path in the proof of VI (5.1), page 129, is first read in
the sphere drawing with cuff arcs adjoined. The annulus embedding has
an inverse on the drawing. Carrying its walk through that inverse and
removing repeated vertices gives a cylinder path whose image stays
inside the original sphere path. No new point of the drawing is used.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A path in the sphere image between two distinct image vertices
pulls back to a cylinder path using only points of that path. -/
theorem exists_subpath_of_sphere_subpath
    {G : Drawing ClosedCylinder} {P : Drawing (OnePoint EuclideanPlane)}
    {a b : ClosedCylinder} (hab : a ≠ b)
    (hP : IsSubpathOf (cylinderSphereDrawing G) P (cylinderToSphere a) (cylinderToSphere b)) :
    ∃ Q : Drawing ClosedCylinder, IsSubpathOf G Q a b ∧ cylinderToSphere '' Q.U ⊆ P.U := by
  classical
  let : Nonempty ClosedCylinder := ⟨cylinderPoint 1 (by simp) 0⟩
  obtain ⟨ψ, hψleft, hψright, hcarry⟩ := (cylinderSphereDrawing_isMatched G).exists_inverse
  have haD : cylinderToSphere a ∈ (cylinderSphereDrawing G).V :=
    hP.1.1 (isPathDrawing_end_vertices hP.2.2).1
  have hbD : cylinderToSphere b ∈ (cylinderSphereDrawing G).V :=
    hP.1.1 (isPathDrawing_end_vertices hP.2.2).2
  have haG : a ∈ G.V := by
    rw [cylinderSphereDrawing_V] at haD
    obtain ⟨x, hx, hxa⟩ := haD
    exact (injective_cylinderToSphere hxa) ▸ hx
  have hbG : b ∈ G.V := by
    rw [cylinderSphereDrawing_V] at hbD
    obtain ⟨x, hx, hxb⟩ := hbD
    exact (injective_cylinderToSphere hxb) ▸ hx
  obtain ⟨W, _, hV, hE⟩ := hP.2.2.1
  have hle : P.toGraph ≤ (cylinderSphereDrawing G).toGraph :=
    { vertexSet_mono := hP.1.1
      isLink_mono := fun _ _ _ hl => (hP.1.isLink_iff hl.1).mp hl }
  let W₀ := W.mono hle
  obtain ⟨R, hRV, hRE, _, _⟩ := hcarry.walk W₀ haD a b
    (hψleft a (G.V_subset_U haG)) (hψleft b (G.V_subset_U hbG))
  obtain ⟨Q, hQ, hQV, hQE⟩ := exists_subpath_of_walk_support G R R.start_mem_support R.end_mem_support hab
  have hvertices : ∀ x ∈ Q.V, cylinderToSphere x ∈ P.U := by
    intro x hx
    have hxR := hQV hx
    rw [hRV, show W₀.support = W.support from GraphWalk.support_mono hle W] at hxR
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxR
    have hyV : y ∈ P.V := by rw [hV]; exact hy
    rw [hψright y (hP.2.1 (P.V_subset_U hyV))]
    exact P.V_subset_U hyV
  refine ⟨Q, hQ, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  rw [Q.U_eq] at hx
  rcases hx with hxV | hxE
  · exact hvertices x hxV
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
    have heR := hQE he
    rw [hRE, show W₀.edges = W.edges from GraphWalk.edges_mono hle W] at heR
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp heR
    have hfP : f ∈ P.E := by rw [hE]; exact hf
    have him : cylinderToSphere '' (ψ '' f) = f := by
      rw [image_image]
      calc
        (cylinderToSphere ∘ ψ) '' f = id '' f := image_congr fun y hy =>
          hψright y (hP.2.1 (P.closure_subset_U hfP (subset_closure hy)))
        _ = f := image_id' f
    have hxIm : cylinderToSphere x ∈ cylinderToSphere '' closure (ψ '' f) := ⟨x, hxe, rfl⟩
    rw [← isClosedEmbedding_cylinderToSphere.closure_image_eq, him] at hxIm
    exact P.closure_subset_U hfP hxIm

end GraphMinor.GM06
