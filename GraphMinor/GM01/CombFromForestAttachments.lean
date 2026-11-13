module

public import GraphMinor.GM01.CombFromPathAttachments
import GraphMinor.GM01.RootedBinaryFromForestMinor

/-!
# The comb contraction from the selected forest-tree minors

In Graph Minors I, page 60, each selected attached subdivision has a
`Y_(γ−1)` minor. Root its connected supporting graph at the endpoint
of its attachment path. The arbitrary-root binary-minor lemma gives
`H_(γ−1)` there. The proved contraction along the common covering
path now gives the rooted comb. No attachment-root location within
the forest model is assumed.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function GraphMinor.GM09

/-- The page-60 contraction with the printed forest-tree minors in
the selected attached sets, rooted at their actual path endpoints. -/
theorem rootedPathComb_of_forest_attachments_on_path {α β : Type*} [Nonempty β] {γ δ : ℕ}
    (hγ : 0 < γ) (hδ : 0 < δ) (G : RootedGraph α β)
    (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    {Q : Graph α β} {last : α} (hQ : IsGraphPathWithEnds G.graph Q G.root.val last)
    (B : Fin δ → RootedGraph α β) (hBG : ∀ i, (B i).graph ≤ G.graph)
    (hBC : ∀ i, GraphConnected (B i).graph)
    (hMinor : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (B i).graph)
    (hDis : ∀ i, Disjoint V(Q) V((B i).graph))
    (hBD : Pairwise fun i j ↦ Disjoint V((B i).graph) V((B j).graph))
    (a : Fin δ → α) (hA : ∀ i, a i ∈ V(Q)) (P : Fin δ → Graph α β)
    (hP : ∀ i, IsGraphPathWithEnds G.graph (P i) (a i) (B i).root.val)
    (hPQ : ∀ i, V(P i) ∩ V(Q) = {a i})
    (hSelf : ∀ i, V(P i) ∩ V((B i).graph) = {(B i).root.val})
    (hOther : ∀ i j, i ≠ j → Disjoint V(P i) V((B j).graph))
    (hPP : Pairwise fun i j ↦ Disjoint V(P i) V(P j)) :
    HasRootedMinor (rootedPathComb γ δ hδ) G := by
  classical
  have hModels : ∀ i, HasRootedMinor (binaryRootedTree (γ - 1)) (B i) := by
    intro i
    exact rootedBinaryTree_of_forestTree_minor (B i)
      (hVfin.subset (hBG i).vertexSet_mono) (hEfin.subset (hBG i).edgeSet_mono)
      (hBC i) (hMinor i)
  let MB := fun i ↦ Classical.choice (hModels i)
  exact rootedPathComb_of_binary_attachments_on_path hγ hδ G hQ B hBG MB hDis hBD
    a hA P hP hPQ hSelf hOther hPP

end GraphMinor.GM01
