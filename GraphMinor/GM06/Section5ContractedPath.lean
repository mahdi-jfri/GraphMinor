module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM06.Section5InitialEdgeSuffix
import GraphMinor.GM06.Section5DrawingImage
import GraphMinor.GM06.Section5PathImage
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools

/-!
# The path shortened by the initial-edge contraction

For Reduction 3 of VI, page 129, map the suffix injectively into the
contracted drawing. The closed initial edge has constant image equal
to the new start, which already belongs to the mapped suffix. Hence
the new path has exactly the image of the old path as its point set.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The initial linkage path has a nondegenerate image path after
its sole initial edge is collapsed. -/
theorem exists_contracted_initial_path
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure a)
    (hi : InjOn π (closure a)ᶜ)
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {a})) :
    ∃ Q : Drawing ClosedCylinder, Q.IsSubdrawing G' ∧
      IsPathDrawing Q (cylinderM1Point k i) (L.curve i 1) ∧
      Q.U = π '' (L.pathDrawing i).U := by
  obtain ⟨B, hB, hBJ, hPU⟩ := exists_suffix_of_initial_valency_one_edge L i hval hl hvs hvC
  have hJinj := injOn_deleted_initial_vertex_drawing hval hl hvs hfiber hi
  have hBinj : InjOn π B.U := hJinj.mono hBJ.U_subset
  obtain ⟨Q, hQU, hQV, hQE⟩ := exists_drawing_image_of_injOn_pointSet B π hBinj
  have hJE := (deleted_initial_vertex_drawing hval hl hvs).1
  have hJG := induceDrawing_isSubdrawing G (sdiff_subset : G.V \ {cylinderM1Point k i} ⊆ G.V)
  have hQG : Q.IsSubdrawing G' := by
    constructor
    · rw [hQV, hV]
      exact image_mono (hBJ.trans hJG).1
    · rw [hQE, hE]
      exact image_mono (fun e he => hJE ▸ hBJ.2 he)
  have hvcl : v ∈ closure a :=
    (show v ∈ closure a ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
  have hπv : π v = cylinderM1Point k i := by
    have hvpre : v ∈ π ⁻¹' {cylinderM1Point k i} := by rw [hfiber]; exact hvcl
    exact hvpre
  have htbd : L.curve i 1 ∈ bd ClosedCylinder := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [← hj]
    exact cylinderM2Point_mem_bd k j
  have hQpath := isPathDrawing_image_of_injOn_pointSet hB π hBinj hQU hQV hQE
  rw [hπv, hbd _ htbd] at hQpath
  refine ⟨Q, hQG, hQpath, hQU.trans ?_⟩
  apply subset_antisymm (image_mono (by rw [hPU]; exact subset_union_right))
  rintro y ⟨x, hx, rfl⟩
  rw [hPU] at hx
  rcases hx with hxa | hxB
  · have hxpre : x ∈ π ⁻¹' {cylinderM1Point k i} := by rw [hfiber]; exact hxa
    have hvB : v ∈ B.U := B.V_subset_U (isPathDrawing_end_vertices hB).1
    exact ⟨v, hvB, hπv.trans hxpre.symm⟩
  · exact mem_image_of_mem π hxB

end GraphMinor.GM06
