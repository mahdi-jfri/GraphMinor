module

public import GraphMinor.GM05.Defs
import GraphMinor.GM05.BagPruning
import GraphMinor.GM05.MinorWidth

/-!
# The complete-graph part of Graph Minors V, (1.4)

A single bag gives the upper bound. Pruning a decomposition finds a bag
containing some vertex and all its neighbours. In a complete graph that is
every vertex, so the same bound is necessary.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

/-- The complete-graph assertion of Graph Minors V, (1.4), page 93:
"For $n \ge 1$, the complete graph $K_n$ has tree-width $n - 1$, and for $\theta \ge 2$ the $\theta$-grid has tree-width $\theta$."
Every decomposition has a bag containing all vertices, and one bag suffices. -/
theorem treeWidth_completeGraph {n : ℕ} (hn : 1 ≤ n) :
    treeWidth (SimpleGraph.toSubgraph (⊤ : SimpleGraph (Fin n)) le_top) = n - 1 := by
  classical
  let G := SimpleGraph.toSubgraph (⊤ : SimpleGraph (Fin n)) le_top
  apply Nat.le_antisymm
  · have htd : IsTreeDecomposition G (⊥ : SimpleGraph Unit) (fun _ ↦ univ) := by
      refine ⟨IsTree.of_subsingleton, iUnion_const _, ?_, ?_⟩
      · intro x y hxy
        exact ⟨(), mem_univ x, mem_univ y⟩
      · intro a c b hp
        exact inter_subset_left
    apply treeWidth_le_of_isTreeDecomposition htd
    intro t
    simpa only [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using
      (show n ≤ n - 1 + 1 by omega)
  · change n - 1 ≤ treeWidth G
    have hfin : G.verts.Finite := finite_univ
    obtain ⟨ι, _, T, χ, htd, hw⟩ := treeWidthLE_treeWidth hfin
    have hne : G.verts.Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
    obtain ⟨v, hvG, t, hvt, hN⟩ := htd.exists_vertex_neighbours_in_bag hne
    have hbag : χ t = univ := by
      apply eq_univ_of_forall
      intro x
      by_cases hx : x = v
      · exact hx ▸ hvt
      · exact hN (Ne.symm hx)
    have hb := hw t
    rw [hbag] at hb
    simp only [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hb
    omega

end GraphMinor.GM05
