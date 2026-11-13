module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5InitialEdgeSuffix
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# The other paths under initial-edge contraction

For Reduction 3 of VI, page 129, all other linkage paths are fixed
pointwise by the collapse. They remain subdrawings of the contracted
graph. They are disjoint from the shortened path because injectivity
holds away from the collapsed edge, whose closure lies on the old
initial path.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Paths fixed pointwise by the initial-edge collapse remain paths
of the new drawing and miss the image of the contracted path. -/
theorem other_paths_of_initial_edge_collapse
    {k : ℕ} {G G' Q : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure a)
    (hi : InjOn π (closure a)ᶜ)
    (hfix : ∀ j, j ≠ i → ∀ x ∈ (L.pathDrawing j).U, π x = x)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {a}))
    (hQU : Q.U = π '' (L.pathDrawing i).U) :
    ∀ j, j ≠ i → (L.pathDrawing j).IsSubdrawing G' ∧
      Disjoint Q.U (L.pathDrawing j).U := by
  obtain ⟨B, _, _, hPU⟩ := exists_suffix_of_initial_valency_one_edge L i hval hl hvs hvC
  have hcl : closure a ⊆ (L.pathDrawing i).U := by rw [hPU]; exact subset_union_left
  have hsPi : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
    (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
  intro j hji
  have hd := L.pairwise_disjoint hji.symm
  have hmiss : Disjoint (closure a) (L.pathDrawing j).U := hd.mono_left hcl
  constructor
  · constructor
    · intro x hx
      rw [hV]
      exact ⟨x, (L.isSubdrawing j).1.1 hx,
        hfix j hji x ((L.pathDrawing j).V_subset_U hx)⟩
    · intro e he
      have hea : e ≠ a := by
        intro hea
        have hsPj := (L.pathDrawing j).closure_subset_U he (hea.symm ▸
          (show cylinderM1Point k i ∈ closure a ∩ G.V from
            hl.2.2.2.symm ▸ mem_insert _ {v}).1)
        exact disjoint_left.mp hd hsPi hsPj
      have himg : π '' e = e := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hfix j hji y ((L.pathDrawing j).closure_subset_U he (subset_closure hy))]
          exact hy
        · intro hx
          exact ⟨x, hx, hfix j hji x ((L.pathDrawing j).closure_subset_U he (subset_closure hx))⟩
      rw [hE]
      exact ⟨e, ⟨(L.isSubdrawing j).1.2 he, hea⟩, himg⟩
  · rw [hQU]
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    have hznot : π x ∉ closure a := fun hzcl => disjoint_left.mp hmiss hzcl hz
    have hxnot : x ∉ closure a := by
      intro hxcl
      have hxpre : x ∈ π ⁻¹' {cylinderM1Point k i} := by rw [hfiber]; exact hxcl
      have hxs : π x = cylinderM1Point k i := hxpre
      exact disjoint_left.mp hd hsPi (hxs ▸ hz)
    have heq : x = π x := hi hxnot hznot (hfix j hji (π x) hz).symm
    exact disjoint_left.mp hd (heq ▸ hx) hz

end GraphMinor.GM06
