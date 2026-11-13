module

public import GraphMinor.GM01.PathCombs
public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.RootedGraphs
import GraphMinor.GM01.RootedSubgraphBranchModels
import GraphMinor.GM01.ConnectedInducedSets
import GraphMinor.GM01.Basic

/-!
# A comb model from its spine pieces and binary arms

For the page-60 contraction of Graph Minors I, retain the connected
pieces of the covering path as the spine branches and the binary
models in the selected attached trees as the arms. Edges join
successive spine pieces and join each piece to its arm root. The
supporting graphs are disjoint, so these branches form the actual
rooted comb model.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

private def combArmBranch {α β : Type*} {γ δ : ℕ} (hγ : 0 < γ)
    (C : Fin δ → Set α) (GB : Fin δ → RootedGraph α β)
    (MB : ∀ i, RootedMinorModel (binaryRootedTree (γ - 1)) (GB i)) :
    (pathComb γ δ).verts → Set α
  | ⟨.inl i,_⟩ => C i
  | ⟨.inr (i,word),hw⟩ => (MB i).branch ⟨word, by
      change word.length < γ at hw
      change word.length ≤ γ - 1
      omega⟩

/-- Assemble the connected spine pieces and disjoint rooted binary
arms in the contraction on page 60 of GM01. All branch conditions
follow from these subgraphs and the displayed joining edges. -/
noncomputable def rootedCombModelOfBinaryArms {α β : Type*} {γ δ : ℕ}
    (hγ : 0 < γ) (hδ : 0 < δ) (G : RootedGraph α β)
    (C : Fin δ → Set α) (hC : ∀ i, C i ⊆ V(G.graph))
    (hCC : ∀ i, GraphConnected (G.graph.induce (C i)))
    (hCD : Pairwise fun i j ↦ Disjoint (C i) (C j))
    (hRoot : G.root.val ∈ C ⟨0,hδ⟩)
    (hSpine : ∀ i j, (pathGraph δ).Adj i j →
      ∃ e x, x ∈ C i ∧ ∃ y, y ∈ C j ∧ G.graph.IsLink e x y)
    (GB : Fin δ → RootedGraph α β) (hGB : ∀ i, (GB i).graph ≤ G.graph)
    (MB : ∀ i, RootedMinorModel (binaryRootedTree (γ - 1)) (GB i))
    (hDis : ∀ i j, Disjoint (C i) V((GB j).graph))
    (hBD : Pairwise fun i j ↦ Disjoint V((GB i).graph) V((GB j).graph))
    (hJoin : ∀ i, ∃ e x, x ∈ C i ∧ G.graph.IsLink e x (GB i).root.val) :
    RootedMinorModel (rootedPathComb γ δ hδ) G := by
  let B := combArmBranch hγ C GB MB
  have hSub : ∀ v, B v ⊆ V(G.graph) := by
    rintro ⟨v,hv⟩ x hx
    cases v with
    | inl i => exact hC i hx
    | inr p => exact (hGB p.1).vertexSet_mono ((MB p.1).branch_subset _ hx)
  have hDisjoint : Pairwise fun u v ↦ Disjoint (B u) (B v) := by
    rintro ⟨u,hu⟩ ⟨v,hv⟩ hne
    cases u with
    | inl i =>
      cases v with
      | inl j => exact hCD (fun h ↦ hne (Subtype.ext (congrArg Sum.inl h)))
      | inr p => exact (hDis i p.1).mono_right ((MB p.1).branch_subset _)
    | inr p =>
      obtain ⟨i,word⟩ := p
      cases v with
      | inl j => exact ((hDis j i).mono_right ((MB i).branch_subset _)).symm
      | inr p' =>
        obtain ⟨j,word'⟩ := p'
        by_cases hij : i = j
        · subst j
          apply (MB i).branch_disjoint
          intro heq
          exact hne (Subtype.ext (congrArg (fun w ↦ Sum.inr (i,w.val)) heq))
        · exact (hBD hij).mono ((MB i).branch_subset _) ((MB j).branch_subset _)
  have hConn : ∀ v, GraphConnected (G.graph.induce (B v)) := by
    rintro ⟨v,hv⟩
    cases v with
    | inl i => exact hCC i
    | inr p =>
      exact graphConnected_induce_of_subgraph
        (((GB p.1).graph.induce_le ((MB p.1).branch_subset _)).trans (hGB p.1))
        ((MB p.1).branch_connected _)
  have hAdj : ∀ {u v : (pathComb γ δ).verts}, (pathComb γ δ).coe.Adj u v →
      ∃ e x, x ∈ B u ∧ ∃ y, y ∈ B v ∧ G.graph.IsLink e x y := by
    rintro ⟨u,hu⟩ ⟨v,hv⟩ huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact hSpine i j huv
      | inr p =>
        obtain ⟨j,word⟩ := p
        have hij : i = j := huv.1
        have hw : word = [] := huv.2.1
        subst j
        subst word
        obtain ⟨e,x,hx,he⟩ := hJoin i
        exact ⟨e,x,hx,(GB i).root.val,(MB i).root_mem,he⟩
    | inr p =>
      obtain ⟨i,word⟩ := p
      cases v with
      | inl j =>
        have hij : i = j := huv.1
        have hw : word = [] := huv.2.1
        subst j
        subst word
        obtain ⟨e,x,hx,he⟩ := hJoin i
        exact ⟨e,(GB i).root.val,(MB i).root_mem,x,hx,he.symm⟩
      | inr p' =>
        obtain ⟨j,word'⟩ := p'
        have hij : i = j := huv.1
        subst j
        have hw : word.length ≤ γ - 1 := by change word.length < γ at hu; omega
        have hw' : word'.length ≤ γ - 1 := by change word'.length < γ at hv; omega
        have hBinary : (binaryTree (γ - 1)).Adj word word' := ⟨hw,hw',huv.2.2.2⟩
        let e : E((binaryRootedTree (γ - 1)).graph) := ⟨s(word,word'),hBinary⟩
        obtain ⟨x,hx,y,hy,hxy⟩ := (MB i).edge_links e ⟨word,hw⟩ ⟨word',hw'⟩ ⟨rfl,hBinary⟩
        exact ⟨((MB i).edgeMap e).val,x,hx,y,hy,hxy.mono (hGB i)⟩
  exact rootedModelOfSubgraphBranchSets (pathComb γ δ) G B hSub hDisjoint hConn hAdj
    (rootedPathComb γ δ hδ).root hRoot

end GraphMinor.GM01
