module

public import GraphMinor.GM05.FullWebDefs
public import GraphMinor.GM05.Section5

/-!
# A connected leaf configuration or a path through many sets

Apply V (5.1) to the simple shadow. In the connected-subgraph alternative,
choose one actual edge per shadow edge, preserving valency one at every
specified leaf. In the path alternative, make the same edge choices along
the returned vertex sequence. All prescribed vertex intersections stay fixed.
-/

public section
namespace GraphMinor.GM05.Full
open Graph Set GM01
variable {α β : Type*}

/-- Graph Minors V, (5.1), pages 100–101, for hosts with loops and parallel edges.
Find the rooted connected configuration with actual valency-one leaves, or
an actual path starting at the root and meeting exactly `q + 1` sets.
`GM05.theorem_5_1_simple` is the simple-host version. Its correction `2 ≤ p`
is retained. -/
theorem theorem_5_1_proof {G : Graph α β} (hV : V(G).Finite) (hc : GraphConnected G)
    {v : α} {p q : ℕ} (hp : 2 ≤ p) (S : Fin (p ^ q) → Set α)
    (hS : ∀ j, S j ⊆ V(G)) (hd : Pairwise fun i j => Disjoint (S i) (S j))
    (hne : ∀ j, (S j).Nonempty) (hv : ∃ j, v ∈ S j) :
    (∃ (C : Graph α β) (emb : Fin p ↪ Fin (p ^ q)) (leaf : Fin p → α),
      C ≤ G ∧ GraphConnected C ∧ v ∈ V(C) ∧
      ∀ i, leaf i ≠ v ∧ IsLeafOf C (leaf i) ∧ S (emb i) ∩ V(C) = {leaf i}) ∨
    (∃ P : Path α β, P.IsIn G ∧ P.seq.first = v ∧
      (metIndices S P.verts).card = q + 1) := by
  rcases GM05.theorem_5_1_simple hV ((graphConnected_iff_simpleShadow_connected _).mp hc)
    hp S hS hd hne hv with ⟨C, emb, leaf, hC, hconn, hvC, hleaf⟩ | ⟨P, hP, hfirst, hmet⟩
  · obtain ⟨K, hK, hverts, hconnK, hleafK⟩ := exists_connected_lift_with_leaves hC hconn
    refine Or.inl ⟨K, emb, leaf, hK, hconnK, hverts.symm ▸ hvC, fun i => ?_⟩
    exact ⟨(hleaf i).1, hleafK _ (hleaf i).2.1, by rw [hverts]; exact (hleaf i).2.2⟩
  · obtain ⟨K, hK, hshadow, hnoloops, hsimple⟩ := exists_simple_subgraph_lift hP
    let Q : Path α β := ⟨P, K, hshadow, hnoloops, hsimple⟩
    exact Or.inr ⟨Q, hK, hfirst, hmet⟩

end GraphMinor.GM05.Full
