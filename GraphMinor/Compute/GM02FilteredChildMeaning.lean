module

public import GraphMinor.Compute.GM02FilteredChildInput
public import GraphMinor.Compute.GM02CompactNumberedInstance

/-!
# Meaning of compact filtered child inputs

When an actual child has the computed vertex set and filtered path
shadow, the executable representation is its compact numbered instance.
Both constructions pull graph edges and terminal pairs back through the
same old-name map. Therefore their feasibility and width statements
agree with those of the actual child graph.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

private theorem pairGraph_injective {n : ℕ} {S : Set (Fin n)}
    (A B : Termination S) (h : A.pairGraph = B.pairGraph) : A = B := by
  apply Termination.ext_pairs
  ext p
  refine Sym2.inductionOn p ?_
  intro u v
  exact A.pairGraph_adj_iff.symm.trans ((congrArg (fun F => F.Adj u v) h).to_iff.trans
    B.pairGraph_adj_iff)

/-- Filtered compaction is the actual child's compact numbered representation. -/
theorem gm02FilteredChildInput_eq_numbered {n : ℕ} {β : Type*}
    (F : SimpleGraph (Fin n)) (A B : Finset (Fin n)) (G : Graph (Fin n) β)
    (T : Termination V(G)) (hV : V(G) = {v : Fin n | v ∉ Bᶜ})
    (hF : pathGraph G = gm02FilteredSide F A B) :
    gm02FilteredChildInput F A B (T.rebase (by rw [← hV]; exact T.support_subset)) =
      gm02CompactNumberedInstance G T Bᶜ hV := by
  have hG : (gm02FilteredChildInput F A B
      (T.rebase (by rw [← hV]; exact T.support_subset))).G =
      (gm02CompactNumberedInstance G T Bᶜ hV).G := by
    exact (congrArg (fun H => H.comap (compactEmb Bᶜ)) hF).symm.trans
      (gm02CompactNumberedInstance_graph G T Bᶜ hV).symm
  have hT : (gm02FilteredChildInput F A B
      (T.rebase (by rw [← hV]; exact T.support_subset))).A =
      (gm02CompactNumberedInstance G T Bᶜ hV).A := by
    apply pairGraph_injective
    simp only [gm02FilteredChildInput, gm02CompactTermination_pairGraph,
      Termination.rebase_pairGraph]
    exact (gm02CompactNumberedInstance_pairGraph G T Bᶜ hV).symm
  unfold gm02FilteredChildInput gm02CompactNumberedInstance gm02NumberedInstance at hG hT ⊢
  congr 1

/-- The compact filtered feasibility answer is exactly the actual child's answer. -/
theorem gm02FilteredChildInput_feasible_iff {n : ℕ} {β : Type*}
    (F : SimpleGraph (Fin n)) (A B : Finset (Fin n)) (G : Graph (Fin n) β)
    (T : Termination V(G)) (hV : V(G) = {v : Fin n | v ∉ Bᶜ})
    (hF : pathGraph G = gm02FilteredSide F A B) :
    let x := gm02FilteredChildInput F A B
      (T.rebase (by rw [← hV]; exact T.support_subset))
    x.A.Feasible (Graph.ofSimpleGraph x.G) ↔ T.Feasible G := by
  dsimp only
  rw [gm02FilteredChildInput_eq_numbered F A B G T hV hF]
  exact gm02CompactNumberedInstance_feasible_iff G T Bᶜ hV

/-- Compact filtered width bounds are exactly the actual child's width bounds. -/
theorem gm02FilteredChildInput_treeWidthLE_iff {n : ℕ} {β : Type*}
    (F : SimpleGraph (Fin n)) (A B : Finset (Fin n)) (G : Graph (Fin n) β)
    (T : Termination V(G)) (hV : V(G) = {v : Fin n | v ∉ Bᶜ})
    (hF : pathGraph G = gm02FilteredSide F A B) (k : ℕ) :
    TreeWidthLE (Graph.ofSimpleGraph (gm02FilteredChildInput F A B
      (T.rebase (by rw [← hV]; exact T.support_subset))).G) k ↔ TreeWidthLE G k := by
  rw [gm02FilteredChildInput_eq_numbered F A B G T hV hF]
  exact gm02CompactNumberedInstance_treeWidthLE_iff G T Bᶜ hV k

end GraphMinor.Compute
