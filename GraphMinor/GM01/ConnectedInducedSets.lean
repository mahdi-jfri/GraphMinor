module

public import GraphMinor.Minor.Model

/-!
# Connected induced unions for the root piece

The root piece in Graph Minors I, (4.1), page 55, joins a connected
initial piece to two path prefixes. A connected subgraph stays connected
when all edges between its vertices are added. Two connected induced
sets with a common vertex have connected union, by joining paths through
that vertex. These facts justify the root-piece construction.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation

/-- Adding all ambient edges between the vertices of a connected subgraph
preserves connectivity. -/
theorem graphConnected_induce_of_subgraph {α β : Type*} {G K : Graph α β}
    (hKG : K ≤ G) (hK : GraphConnected K) : GraphConnected (G.induce V(K)) := by
  refine ⟨hK.1, ?_⟩
  intro a ha b hb
  apply ReflTransGen.mono ?_ a b (hK.2 a ha b hb)
  intro x y hxy
  obtain ⟨e, he⟩ := hxy
  exact ⟨e, he.mono hKG, he.left_mem, he.right_mem⟩

/-- Connected induced vertex sets meeting at a vertex have connected
induced union. -/
theorem graphConnected_induce_union {α β : Type*} {G : Graph α β} {A B : Set α}
    (hA : GraphConnected (G.induce A)) (hB : GraphConnected (G.induce B))
    (hmeet : (A ∩ B).Nonempty) : GraphConnected (G.induce (A ∪ B)) := by
  obtain ⟨z, hzA, hzB⟩ := hmeet
  have htoz : ∀ x ∈ A ∪ B, ReflTransGen (G.induce (A ∪ B)).Adj x z := by
    intro x hx
    rcases hx with hx | hx
    · apply ReflTransGen.mono ?_ x z (hA.2 x hx z hzA)
      intro a b hab
      obtain ⟨e, he⟩ := hab
      exact ⟨e, he.1, Or.inl he.2.1, Or.inl he.2.2⟩
    · apply ReflTransGen.mono ?_ x z (hB.2 x hx z hzB)
      intro a b hab
      obtain ⟨e, he⟩ := hab
      exact ⟨e, he.1, Or.inr he.2.1, Or.inr he.2.2⟩
  exact ⟨⟨z, Or.inl hzA⟩, fun x hx y hy ↦
    (htoz x hx).trans (Std.Symm.symm _ _ (htoz y hy))⟩

end GraphMinor.GM01
