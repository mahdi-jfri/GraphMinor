module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Regions
import GraphMinor.GM11.CircuitRegions

/-!
# Removing the seam edges before cutting a drawing

To carry the one-path argument of VI Section 5 to the cut cylinder,
first separate the linkage path from the other edges. Keep every
vertex and delete just the path edges. The resulting drawing meets
the seam only at vertices, so its pullback across the cut is a drawing.
Adjoining the two seam copies afterwards restores the full cut graph.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

universe u

/-- Deleting the edges of a subdrawing while retaining every vertex
makes its point set normal to the remaining drawing. Their point sets
still cover the original drawing. These are the inputs for cutting
along a linkage path in the one-path case of VI Section 5. -/
theorem exists_drawing_without_subdrawing_edges
    {S : Type u} [TopologicalSpace S] [T2Space S] (G P : Drawing S)
    (hP : P.IsSubdrawing G) :
    ∃ H : Drawing S, H.IsSubdrawing G ∧ H.V = G.V ∧ H.E = G.E \ P.E ∧
      G.U = H.U ∪ P.U ∧ H.IsNormal P.U := by
  let H := G.span G.V (G.E \ P.E)
  have hHG : H.IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hV : H.V = G.V := by
    apply subset_antisymm hHG.1
    intro x hx
    change x ∈ G.spanV G.V (G.E \ P.E)
    exact Or.inl ⟨hx, hx⟩
  have hE : H.E = G.E \ P.E := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr sdiff_subset
  have hU : G.U = H.U ∪ P.U := by
    apply subset_antisymm
    · intro x hx
      by_cases hxV : x ∈ G.V
      · exact Or.inl (H.V_subset_U (hV.symm ▸ hxV))
      · obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hx hxV
        by_cases heP : e ∈ P.E
        · exact Or.inr ((heP.2.1 hxe).1)
        · have heH : e ∈ H.E := hE.symm ▸ ⟨he, heP⟩
          exact Or.inl ((heH.2.1 hxe).1)
    · exact union_subset hHG.U_subset hP.U_subset
  refine ⟨H, hHG, hV, hE, hU, ?_⟩
  intro x hx
  by_cases hxV : x ∈ H.V
  · exact hxV
  · obtain ⟨e, heH, hxe⟩ := H.exists_edge_of_mem hx.2 hxV
    have he : e ∈ G.E \ P.E := hE ▸ heH
    exact False.elim (disjoint_left.mp (GM11.edge_disjoint_U hP he.1 he.2) hxe hx.1)

end GraphMinor.GM06
