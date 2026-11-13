module

public import GraphMinor.GM01.ConnectedInducedSets
public import GraphMinor.GM01.PathLastEdgeCover
import GraphMinor.GM01.SubdivisionConnected

/-!
# Removing a piece attached by one path

For Graph Minors I, (4.12), page 59, removing the second end of the
subdivision leaves a connected graph. The remaining cells are connected.
Their boundary path meets the second end only at its last vertex.
Remove that vertex from the path and join the remaining path to the
remaining cells. The vertex-cover identity shows that this is exactly
the required complement.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- A connected piece and its connecting path remain connected when
the terminal piece is removed. This is the graph step in the
second-end contraction of GM01 (4.12), page 59. -/
theorem connected_complement_of_terminal_piece {α β : Type*}
    {D K P : Graph α β} {E : Set α} (hKD : K ≤ D)
    (hKconn : GraphConnected K) (hKE : Disjoint V(K) E)
    {a b : α} (ha : a ∈ V(K)) (hb : b ∈ E)
    (hP : IsGraphPathWithEnds D P a b) (hMeet : V(P) ∩ E = {b})
    (hcover : V(D) ⊆ V(K) ∪ V(P) ∪ E) :
    GraphConnected (D.induce (V(D) \ E)) := by
  have hab : a ≠ b := fun h ↦ Set.disjoint_left.mp hKE ha (h.symm ▸ hb)
  obtain ⟨e, q, Q, _, hQP, hQ, hbQ, hPQ⟩ := exists_last_edge_with_vertex_cover hP hab
  have hQE : Disjoint V(Q) E := by
    apply Set.disjoint_left.mpr
    intro x hx hxE
    have hxb : x = b := mem_singleton_iff.mp (hMeet ▸ ⟨hQP.vertexSet_mono hx, hxE⟩)
    exact hbQ (hxb ▸ hx)
  let U := subgraphUnion D K Q
  have hUD : U ≤ D := subgraphUnion_le hKD hQ.le
  have hUconn : GraphConnected U := graphConnected_subgraphUnion hKD hQ.le hKconn
    (graphConnected_of_isGraphPath hQ) ⟨a, ha, hQ.left_mem⟩
  have hUV : V(U) = V(D) \ E := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hUD.vertexSet_mono hx, fun hxE ↦
        Set.disjoint_left.mp (hKE.union_left hQE) hx hxE⟩
    · intro x hx
      rcases hcover hx.1 with (hxK | hxP) | hxE
      · exact Or.inl hxK
      · rw [hPQ] at hxP
        rcases hxP with rfl | hxQ
        · exact False.elim (hx.2 hb)
        · exact Or.inr hxQ
      · exact False.elim (hx.2 hxE)
  rw [← hUV]
  exact graphConnected_induce_of_subgraph hUD hUconn

end GraphMinor.GM01
