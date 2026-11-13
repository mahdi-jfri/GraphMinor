module

public import GraphMinor.GM01.RootedSubgraphBranchModels
public import GraphMinor.GM01.PathCombs
public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.ConnectedInducedSets

/-!
# A one-cell comb from a binary arm

For the initial contractions in Graph Minors I, Part 3, page 59,
a connected root piece attached to a model of `H_(γ−1)` gives
`P(γ,1)`. Use the root piece for its sole spine vertex and the
binary model's branches for the attached words. The joining edge
and all internal binary edges give the required branch incidences.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

private def oneCellBranch {α β : Type*} {γ : ℕ} (C : Set α) {GB : RootedGraph α β}
    (MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB) : (pathComb γ 1).verts → Set α
  | ⟨.inl _, _⟩ => C
  | ⟨.inr (_, word), hw⟩ => MB.branch ⟨word, by change word.length < γ at hw; change word.length ≤ γ - 1; omega⟩

/-- Attach one binary arm to a connected root piece, obtaining the
one-cell comb used in the contractions at the start of GM01 Part 3. -/
noncomputable def rootedOneCellCombModelOfBinaryArm {α β : Type*} {γ : ℕ}
    (hγ : 0 < γ) (G : RootedGraph α β) (C : Set α) (hC : C ⊆ V(G.graph))
    (hconn : GraphConnected (G.graph.induce C)) (hroot : G.root.val ∈ C)
    (GB : RootedGraph α β) (hGB : GB.graph ≤ G.graph)
    (MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB)
    (hdis : Disjoint C V(GB.graph))
    (hjoin : ∃ e x, x ∈ C ∧ G.graph.IsLink e x GB.root.val) :
    RootedMinorModel (rootedPathComb γ 1 (by decide)) G := by
  let B := oneCellBranch C MB
  have hB : ∀ v, B v ⊆ V(G.graph) := by
    rintro ⟨v, hv⟩ x hx
    cases v with
    | inl i => exact hC hx
    | inr pair => exact hGB.vertexSet_mono (MB.branch_subset _ hx)
  have hBD : Pairwise fun u v ↦ Disjoint (B u) (B v) := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ hne
    cases u with
    | inl i =>
      cases v with
      | inl j => exact False.elim (hne (Subtype.ext (congrArg Sum.inl (Subsingleton.elim i j))))
      | inr pair => exact hdis.mono_right (MB.branch_subset _)
    | inr pair =>
      obtain ⟨i, word⟩ := pair
      cases v with
      | inl j => exact (hdis.mono_right (MB.branch_subset _)).symm
      | inr pair' =>
        obtain ⟨j, word'⟩ := pair'
        apply MB.branch_disjoint
        intro heq
        exact hne (Subtype.ext (congrArg Sum.inr (Prod.ext (Subsingleton.elim i j) (congrArg Subtype.val heq))))
  have hBC : ∀ v, GraphConnected (G.graph.induce (B v)) := by
    rintro ⟨v, hv⟩
    cases v with
    | inl i => exact hconn
    | inr pair =>
        exact graphConnected_induce_of_subgraph
          ((GB.graph.induce_le (MB.branch_subset _)).trans hGB) (MB.branch_connected _)
  have hAdj : ∀ {u v : (pathComb γ 1).verts}, (pathComb γ 1).coe.Adj u v →
      ∃ e x, x ∈ B u ∧ ∃ y, y ∈ B v ∧ G.graph.IsLink e x y := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    cases u with
    | inl i =>
      cases v with
      | inl j =>
        have hi := i.isLt
        have hj := j.isLt
        rcases pathGraph_adj.mp huv with h | h <;> omega
      | inr pair =>
        obtain ⟨j, word⟩ := pair
        have hw : word = [] := huv.2.1
        subst word
        obtain ⟨e, x, hx, he⟩ := hjoin
        exact ⟨e, x, hx, GB.root.val, MB.root_mem, he⟩
    | inr pair =>
      obtain ⟨i, word⟩ := pair
      cases v with
      | inl j =>
        have hw : word = [] := huv.2.1
        subst word
        obtain ⟨e, x, hx, he⟩ := hjoin
        exact ⟨e, GB.root.val, MB.root_mem, x, hx, he.symm⟩
      | inr pair' =>
        obtain ⟨j, word'⟩ := pair'
        have hw : word.length ≤ γ - 1 := by change word.length < γ at hu; omega
        have hw' : word'.length ≤ γ - 1 := by change word'.length < γ at hv; omega
        have hBinary : (binaryTree (γ - 1)).Adj word word' := ⟨hw, hw', huv.2.2.2⟩
        let e : E((binaryRootedTree (γ - 1)).graph) := ⟨s(word,word'), hBinary⟩
        obtain ⟨x, hx, y, hy, hxy⟩ := MB.edge_links e ⟨word, hw⟩ ⟨word', hw'⟩ ⟨rfl, hBinary⟩
        exact ⟨(MB.edgeMap e).val, x, hx, y, hy, hxy.mono hGB⟩
  exact rootedModelOfSubgraphBranchSets (pathComb γ 1) G B hB hBD hBC hAdj
    (rootedPathComb γ 1 (by decide)).root hroot


/-- The single spine branch is exactly the chosen root piece. Thus a
specified attachment in that piece survives the half contraction in
GM01 (5.1), pages 60–61. -/
theorem rootedOneCellCombModelOfBinaryArm_root_branch {α β : Type*} {γ : ℕ}
    (hγ : 0 < γ) (G : RootedGraph α β) (C : Set α) (hC : C ⊆ V(G.graph))
    (hconn : GraphConnected (G.graph.induce C)) (hroot : G.root.val ∈ C)
    (GB : RootedGraph α β) (hGB : GB.graph ≤ G.graph)
    (MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB)
    (hdis : Disjoint C V(GB.graph))
    (hjoin : ∃ e x, x ∈ C ∧ G.graph.IsLink e x GB.root.val) :
    (rootedOneCellCombModelOfBinaryArm hγ G C hC hconn hroot GB hGB MB hdis hjoin).branch
      (rootedPathComb γ 1 (by decide)).root = C := by
  unfold rootedOneCellCombModelOfBinaryArm
  dsimp only
  exact rootedModelOfSubgraphBranchSets_branch _ _ _ _ _ _ _ _ _ _

end GraphMinor.GM01
