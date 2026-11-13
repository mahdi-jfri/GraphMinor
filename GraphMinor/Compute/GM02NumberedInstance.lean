module

public import GraphMinor.Compute.GM02TerminatedInput
public import GraphMinor.GM02.SimpleGraphRenaming
import GraphMinor.GM02.TerminationGraphMaps

/-!
# Numbered recursive instances for II (3.2)

A bijection from the actual child vertices to `Fin n` gives a plain
simple terminated input. Restrict the graph and endpoint pairs to the
actual vertices, then rename both by that bijection. The number of pairs,
feasibility, and every width bound are preserved. These facts justify
recursive answers independently of the chosen numbering.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph SimpleGraph Set Classical GraphMinor.GM02
universe u v

/-- The simple terminated instance obtained by a supplied numbering of its
actual vertices, for the recursive calls on II pages 316–317. -/
noncomputable def gm02NumberedInstance {α : Type u} {β : Type v} {n : ℕ}
    (G : Graph α β) (A : Termination V(G)) (e : V(G) ≃ Fin n) : GM02SimpleTerminatedInput where
  n := n
  G := ((pathGraph G).induce V(G)).map e
  decAdj := Classical.decRel _
  A := (A.onVertices.mapEmbedding e.toEmbedding).rebase (Set.subset_univ _)

/-- The numbered graph is the original path graph pulled back through old names. -/
theorem gm02NumberedInstance_graph {α : Type u} {β : Type v} {n : ℕ}
    (G : Graph α β) (A : Termination V(G)) (e : V(G) ≃ Fin n) :
    (gm02NumberedInstance G A e).G =
      (pathGraph G).comap (fun i => (e.symm i).val) := by
  change (((pathGraph G).induce V(G)).map e) = _
  have hm := SimpleGraph.comap_symm ((pathGraph G).induce V(G)) e
  exact hm.symm

/-- The numbered matching is likewise the original matching pulled back through old names. -/
theorem gm02NumberedInstance_pairGraph {α : Type u} {β : Type v} {n : ℕ}
    (G : Graph α β) (A : Termination V(G)) (e : V(G) ≃ Fin n) :
    (gm02NumberedInstance G A e).A.pairGraph =
      A.pairGraph.comap (fun i => (e.symm i).val) := by
  change ((A.onVertices.mapEmbedding e.toEmbedding).rebase (Set.subset_univ _)).pairGraph = _
  rw [Termination.rebase_pairGraph, Termination.mapEquiv_pairGraph,
    Termination.onVertices_pairGraph]
  rfl

/-- Numbering does not change the index of a termination. -/
theorem gm02NumberedInstance_index {α : Type u} {β : Type v} {n : ℕ}
    (G : Graph α β) (A : Termination V(G)) (e : V(G) ≃ Fin n) :
    (gm02NumberedInstance G A e).A.index = A.index := by
  change ((A.onVertices.mapEmbedding e.toEmbedding).rebase (Set.subset_univ _)).index = A.index
  rw [Termination.rebase_index, Termination.mapEmbedding_index, Termination.onVertices_index]

/-- The numbered graph has exactly as many vertices as the original graph. -/
theorem gm02NumberedInstance_size {α : Type u} {β : Type v} {n : ℕ}
    (G : Graph α β) (A : Termination V(G)) (e : V(G) ≃ Fin n) :
    (gm02NumberedInstance G A e).n = V(G).ncard := by
  change n = Nat.card V(G)
  exact (Nat.card_congr e).trans (Nat.card_fin n) |>.symm

/-- Feasibility is independent of the numbering used by a recursive call. -/
theorem gm02NumberedInstance_feasible_iff {α : Type u} {β : Type v} {n : ℕ}
    (G : Graph α β) (A : Termination V(G)) (e : V(G) ≃ Fin n) :
    (gm02NumberedInstance G A e).A.Feasible
      (Graph.ofSimpleGraph (gm02NumberedInstance G A e).G) ↔ A.Feasible G := by
  change ((A.onVertices.mapEmbedding e.toEmbedding).rebase (Set.subset_univ _)).Feasible
    (Graph.ofSimpleGraph (((pathGraph G).induce V(G)).map e)) ↔ A.Feasible G
  rw [Termination.feasible_rebase_iff]
  exact (feasible_simpleIso_iff A.onVertices
    (SimpleGraph.Iso.map e ((pathGraph G).induce V(G)))).trans (feasible_onVertices_iff G A)

/-- Every bag-width bound is preserved by the child-instance numbering. -/
theorem gm02NumberedInstance_treeWidthLE_iff {α : Type u} {β : Type v} {n : ℕ}
    (G : Graph α β) (A : Termination V(G)) (e : V(G) ≃ Fin n) (w : ℕ) :
    TreeWidthLE (Graph.ofSimpleGraph (gm02NumberedInstance G A e).G) w ↔ TreeWidthLE G w := by
  exact (treeWidthLE_simpleIso_iff
    (SimpleGraph.Iso.map e ((pathGraph G).induce V(G))) w).symm.trans
      (treeWidthLE_onVertices_iff G w)

/-- Numerical widths agree, so a recursive width report is valid for the
original child graph. -/
theorem gm02NumberedInstance_width {α : Type u} {β : Type v} {n : ℕ}
    (G : Graph α β) (A : Termination V(G)) (e : V(G) ≃ Fin n)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    (gm02NumberedInstance G A e).width = treeWidth G hV hE := by
  apply Nat.le_antisymm
  · apply (treeWidth_le_iff _ _ _ _).2
    exact (gm02NumberedInstance_treeWidthLE_iff G A e _).2
      ((treeWidth_le_iff G hV hE _).1 le_rfl)
  · apply (treeWidth_le_iff G hV hE _).2
    exact (gm02NumberedInstance_treeWidthLE_iff G A e _).1
      ((treeWidth_le_iff _ _ _ _).1 le_rfl)

end GraphMinor.Compute
