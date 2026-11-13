module

public import GraphMinor.GM01.SeparatorLayers

/-!
# Edges across a root separator

In the edge-coverage proof of Graph Minors I, (1.7), page 42, one end
of an edge is cut off from the root and the other is not. The separated
end must lie in the cut: otherwise the edge extends an avoiding path
to the root and gives a contradiction.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation

/-- The edge argument proving (W1) in GM01 (1.7), page 42. -/
theorem mem_separator_of_adj {α β : Type*} {G : Graph α β} {X : Set α}
    {u v root : α} (huv : G.Adj u v)
    (hv : GraphSeparates G X {v} {root})
    (hu : ¬ GraphSeparates G X {u} {root}) : v ∈ X := by
  classical
  by_contra hvNot
  have hreach : u ∈ V(G.deleteVerts X) ∧ root ∈ V(G.deleteVerts X) ∧
      ReflTransGen (G.deleteVerts X).Adj u root := by
    simpa only [GraphSeparates, Set.mem_singleton_iff, forall_eq, not_imp, not_not] using hu
  obtain ⟨e, he⟩ := huv
  have huNot := (((G.vertexSet_deleteVerts X) ▸ hreach.1)).2
  have hdel := (G.deleteVerts_isLink X).mpr ⟨he, huNot, hvNot⟩
  exact hv v rfl root rfl hdel.right_mem hreach.2.1
    (hreach.2.2.head ⟨e, hdel.symm⟩)

end GraphMinor.GM01
