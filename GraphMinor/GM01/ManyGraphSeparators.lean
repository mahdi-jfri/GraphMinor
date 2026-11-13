module

public import GraphMinor.GM01.ManySeparators
public import GraphMinor.GM01.SeparatorGraphBridge

/-!
# Many connected separators in a general graph

Graph Minors I, (4.2), pages 55–56, applies Menger and (2.7) to general
graphs. Transfer the disjoint connected separator sets to the underlying
simple graph. The proved Menger/(2.7) argument gives a small separator
there, which maps back with exactly the same cardinality. Loops and
parallel edges therefore do not add a hypothesis to the separator bound.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The Menger/(2.7) small-separator argument for finite general graphs,
as used in the proof of GM01 (4.2), pages 55–56. -/
theorem exists_small_graph_separator_of_many_separators {α β : Type*} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (G : Graph α β) (hfin : V(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G) (A B : Set α)
    (D : Fin (θ ^ (2 * θ)) → Set α) (hDsub : ∀ i, D i ⊆ V(G))
    (hDconn : ∀ i, GraphConnected (G.induce (D i)))
    (hDdisj : Pairwise fun i j ↦ Disjoint (D i) (D j))
    (hDsep : ∀ i, GraphSeparates G (D i) A B) :
    ∃ X ⊆ V(G), X.ncard < θ ^ 2 / 2 ∧ GraphSeparates G X A B := by
  let : Finite V(G) := hfin.to_subtype
  let K := SimpleGraph.toSubgraph G.toSimpleGraph le_top
  let K' := fun i ↦ simpleInducedVertices G (D i)
  have hKdisj : Pairwise fun i j ↦ Disjoint (K' i).verts (K' j).verts := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hDdisj hij) hxi hxj
  have hKsep : ∀ i, Separates K (K' i).verts (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B) :=
    fun i ↦ (graphSeparates_iff_simple_subgraph G (D i) A B).mp (hDsep i)
  obtain ⟨S, _, hcard, hsep⟩ := exists_small_separator_of_many_disjoint_separators hθ heven
    (G := K) Set.finite_univ (simplification_mem_gridFree G hG)
    (fun _ _ ↦ mem_univ _) (fun _ _ ↦ mem_univ _) K'
    (fun i ↦ simpleInducedVertices_le G (D i))
    (fun i ↦ simpleInducedVertices_connected G (D i) (hDsub i) (hDconn i)) hKdisj hKsep
  obtain ⟨X, hX, hcardX, hsepX⟩ := graph_separator_of_simple_separator G A B S hsep
  exact ⟨X, hX, hcardX ▸ hcard, hsepX⟩

end GraphMinor.GM01
