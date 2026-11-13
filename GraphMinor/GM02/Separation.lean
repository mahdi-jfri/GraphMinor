module

public import GraphMinor.GM02.BagSeparation

/-!
# Separations of a graph

Graph Minors II, page 313, defines a separation by two subgraphs covering
all vertices and partitioning the edges. The proof of (2.6) constructs one
from two separated sides and their separator. Assign to the first side all
edges whose ends are in that side together with the separator. Assign the
remaining edges to the second side.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Relation Classical
universe u v

/-- Graph Minors II, Section 2, page 313: a separation is a pair of
subgraphs covering the vertices and partitioning the edges. -/
def IsSeparation {α : Type u} {β : Type v} (G H H' : Graph α β) : Prop :=
  H ≤ G ∧ H' ≤ G ∧ V(H) ∪ V(H') = V(G) ∧
    E(H) ∪ E(H') = E(G) ∧ Disjoint E(H) E(H')

/-- Construct the separation in the first paragraph of the proof of
II (2.6), page 313, from the separated vertex partition. -/
theorem exists_separation_of_partition {α : Type u} {β : Type v}
    {G : Graph α β} {X Y Y' : Set α} (hX : X ⊆ V(G))
    (hpart : Y ∪ Y' = V(G) \ X)
    (hsep : Separates G X Y Y') :
    ∃ H H', IsSeparation G H H' ∧ V(H) = X ∪ Y ∧ V(H') = X ∪ Y' := by
  have hY : Y ⊆ V(G) \ X := by intro a ha; rw [← hpart]; exact Or.inl ha
  have hY' : Y' ⊆ V(G) \ X := by intro a ha; rw [← hpart]; exact Or.inr ha
  let H := G.induce (X ∪ Y)
  let H' := (G.induce (X ∪ Y')).deleteEdges E(H)
  have hH : H ≤ G := Graph.induce_le (fun _ h => h.elim (fun h => hX h) (fun h => (hY h).1))
  have hH' : H' ≤ G := Graph.deleteEdges_le.trans
    (Graph.induce_le (fun _ h => h.elim (fun h => hX h) (fun h => (hY' h).1)))
  refine ⟨H, H', ⟨hH, hH', ?_, ?_, ?_⟩, rfl, rfl⟩
  · change (X ∪ Y) ∪ (X ∪ Y') = V(G)
    rw [Set.union_union_union_comm, Set.union_self, hpart, Set.union_sdiff_cancel hX]
  · apply Set.Subset.antisymm
    · exact Set.union_subset hH.edgeSet_mono hH'.edgeSet_mono
    · intro e he
      by_cases heH : e ∈ E(H)
      · exact Or.inl heH
      · apply Or.inr
        change e ∈ E(G.induce (X ∪ Y')) \ E(H)
        refine ⟨?_, heH⟩
        obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet he
        have hend : ∀ a b, G.IsLink e a b → a ∈ X ∪ Y' := by
          intro a b hab
          by_cases haX : a ∈ X
          · exact Or.inl haX
          · have ha : a ∈ Y ∪ Y' := by rw [hpart]; exact ⟨hab.left_mem, haX⟩
            rcases ha with haY | haY'
            · have hbL : b ∈ X ∪ Y := by
                by_cases hbX : b ∈ X
                · exact Or.inl hbX
                · have hb : b ∈ Y ∪ Y' := by rw [hpart]; exact ⟨hab.right_mem, hbX⟩
                  rcases hb with hbY | hbY'
                  · exact Or.inr hbY
                  · exact (hsep a haY b hbY' ⟨hab.left_mem, haX⟩
                      ⟨hab.right_mem, hbX⟩ (ReflTransGen.single
                        (show (G.induce (V(G) \ X)).Adj a b from
                          ⟨e, hab, ⟨hab.left_mem, haX⟩, hab.right_mem, hbX⟩))).elim
              exact (heH (show e ∈ E(H) from
                Graph.IsLink.edge_mem (G := H) ⟨hab, Or.inr haY, hbL⟩)).elim
            · exact Or.inr haY'
        exact Graph.IsLink.edge_mem ⟨hab, hend a b hab, hend b a hab.symm⟩
  · exact Set.disjoint_sdiff_right

end GraphMinor.GM02
