module

public import GraphMinor.GM02.Separation
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Recovering a separation from its vertex sides

The separator program writes two vertex-side arrays. To recover actual
edge-disjoint subgraphs, put every edge whose ends lie on the first side
in that side. Put the remaining edges with ends on the second side there.
Any original separation with these vertex sides proves that this rule
covers all edges. Thus the recursive program needs only the two arrays.
-/

public section
namespace GraphMinor.GM02
open Graph Set
universe u v

/-- Assign separator edges to the first side, retaining the vertex sides
of a separation returned by II (3.1). -/
theorem IsSeparation.canonicalize {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hsep : IsSeparation G H H') :
    IsSeparation G (G.induce V(H))
      ((G.induce V(H')).deleteEdges E(G.induce V(H))) := by
  have hL : G.induce V(H) ≤ G := G.induce_le hsep.1.vertexSet_mono
  have hR : (G.induce V(H')).deleteEdges E(G.induce V(H)) ≤ G :=
    Graph.deleteEdges_le.trans (G.induce_le hsep.2.1.vertexSet_mono)
  refine ⟨hL, hR, hsep.2.2.1, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · exact Set.union_subset hL.edgeSet_mono hR.edgeSet_mono
    · intro e he
      by_cases hl : e ∈ E(G.induce V(H))
      · exact Or.inl hl
      · apply Or.inr
        change e ∈ E(G.induce V(H')) \ E(G.induce V(H))
        refine ⟨?_, hl⟩
        have hor : e ∈ E(H) ∪ E(H') := hsep.2.2.2.1.symm ▸ he
        rcases hor with heH | heH'
        · obtain ⟨a, b, hab⟩ := H.exists_isLink_of_mem_edgeSet heH
          have hg : G.IsLink e a b := hsep.1.isLink_mono hab
          exact (hl (Graph.IsLink.edge_mem (by
            rw [Graph.induce_isLink]
            exact ⟨hg, hab.left_mem, hab.right_mem⟩))).elim
        · obtain ⟨a, b, hab⟩ := H'.exists_isLink_of_mem_edgeSet heH'
          apply Graph.IsLink.edge_mem (x := a) (y := b)
          rw [Graph.induce_isLink]
          exact ⟨hsep.2.1.isLink_mono hab, hab.left_mem, hab.right_mem⟩
  · exact Set.disjoint_sdiff_right

/-- Canonicalization leaves the first vertex-side array unchanged. -/
theorem canonicalSeparation_left_vertices {α : Type u} {β : Type v} (G H : Graph α β) :
    V(G.induce V(H)) = V(H) := rfl

/-- Deleting separator edges leaves the second vertex-side array unchanged. -/
theorem canonicalSeparation_right_vertices {α : Type u} {β : Type v} (G H H' : Graph α β) :
    V((G.induce V(H')).deleteEdges E(G.induce V(H))) = V(H') := rfl

end GraphMinor.GM02
