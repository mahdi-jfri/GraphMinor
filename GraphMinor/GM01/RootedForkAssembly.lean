module

public import GraphMinor.GM01.RootedForkBranches
public import GraphMinor.GM01.RootedBranchModels
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.SubgraphIso

/-!
# Assembling the two arms of the rooted fork

Graph Minors I, (4.1), page 55, contracts a connected root piece and
retains the skipped binary tree and the final path comb. Their supporting
graphs are disjoint. An edge from the root piece to each model root
joins these three parts into `Q(γ,δ)`. The branch-set constructor proves
the edge injection, while the fork-branch lemmas prove disjointness and
connectivity. This lemma constructs the model from those actual pieces.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Assemble a rooted fork from a connected root piece, two disjoint
rooted arm models and the two actual edges joining their roots to that
piece. This is the final contraction operation in GM01 (4.1), page 55. -/
noncomputable def rootedForkModelOfArms {α β : Type*} {γ δ : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (G : RootedGraph α β)
    (C : Set α) (hCsub : C ⊆ V(G.graph)) (hCconn : GraphConnected (G.graph.induce C))
    (hroot : G.root.val ∈ C) {GP GB : RootedGraph α β}
    (hGP : GP.graph ≤ G.graph) (hGB : GB.graph ≤ G.graph)
    (MP : RootedMinorModel (rootedPathComb (γ - 1) (δ - 1) (by omega)) GP)
    (MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB)
    (hCP : Disjoint C V(GP.graph)) (hCB : Disjoint C V(GB.graph))
    (hPB : Disjoint V(GP.graph) V(GB.graph))
    (hjoinP : ∃ e x, x ∈ C ∧ G.graph.IsLink e x GP.root.val)
    (hjoinB : ∃ e x, x ∈ C ∧ G.graph.IsLink e x GB.root.val) :
    RootedMinorModel (rootedForkGraph γ δ hγ hδ) G := by
  let Q := rootedFork γ δ hδ
  let B := rootedForkBranch hδ C MP MB
  have hBsub : ∀ v : Q.verts, B v ⊆ V(G.graph) := by
    rintro ⟨v, hv⟩ x hx
    cases v with
    | none => exact hCsub hx
    | some v =>
      cases v with
      | inl p => exact hGP.vertexSet_mono (MP.branch_subset ⟨p, hv⟩ hx)
      | inr word => exact hGB.vertexSet_mono (MB.branch_subset ⟨word, hv⟩ hx)
  have hAdj : ∀ {u v : Q.verts}, Q.coe.Adj u v →
      ∃ e x, x ∈ B u ∧ ∃ y, y ∈ B v ∧ G.graph.IsLink e x y := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    cases u with
    | none =>
      cases v with
      | none => exact False.elim huv
      | some v =>
        cases v with
        | inl p =>
          have hp : p = rootedForkAnchor δ hδ := huv
          have hproot : (⟨p, hv⟩ : (pathComb (γ - 1) (δ - 1)).verts) =
              (rootedPathComb (γ - 1) (δ - 1) (by omega)).root := Subtype.ext hp
          have hpMem : GP.root.val ∈ MP.branch ⟨p, hv⟩ := hproot.symm ▸ MP.root_mem
          obtain ⟨e, x, hx, hlink⟩ := hjoinP
          exact ⟨e, x, hx, GP.root.val, hpMem, hlink⟩
        | inr word =>
          have hw : word = [] := huv
          have hwroot : (⟨word, hv⟩ : (binaryTree (γ - 1)).verts) =
              (binaryRootedTree (γ - 1)).root := Subtype.ext hw
          have hbMem : GB.root.val ∈ MB.branch ⟨word, hv⟩ := hwroot.symm ▸ MB.root_mem
          obtain ⟨e, x, hx, hlink⟩ := hjoinB
          exact ⟨e, x, hx, GB.root.val, hbMem, hlink⟩
    | some u =>
      cases u with
      | inl p =>
        cases v with
        | none =>
          have hp : p = rootedForkAnchor δ hδ := huv
          have hproot : (⟨p, hu⟩ : (pathComb (γ - 1) (δ - 1)).verts) =
              (rootedPathComb (γ - 1) (δ - 1) (by omega)).root := Subtype.ext hp
          have hpMem : GP.root.val ∈ MP.branch ⟨p, hu⟩ := hproot.symm ▸ MP.root_mem
          obtain ⟨e, x, hx, hlink⟩ := hjoinP
          exact ⟨e, GP.root.val, hpMem, x, hx, hlink.symm⟩
        | some v =>
          cases v with
          | inl q =>
            have hpq : (pathComb (γ - 1) (δ - 1)).Adj p q := huv
            let edge : E(toGraph (pathComb (γ - 1) (δ - 1))) := ⟨s(p,q), hpq⟩
            obtain ⟨x, hx, y, hy, hlink⟩ := MP.edge_links edge ⟨p, hu⟩ ⟨q, hv⟩ ⟨rfl, hpq⟩
            exact ⟨(MP.edgeMap edge).val, x, hx, y, hy, hlink.mono hGP⟩
          | inr word => exact False.elim huv
      | inr word =>
        cases v with
        | none =>
          have hw : word = [] := huv
          have hwroot : (⟨word, hu⟩ : (binaryTree (γ - 1)).verts) =
              (binaryRootedTree (γ - 1)).root := Subtype.ext hw
          have hbMem : GB.root.val ∈ MB.branch ⟨word, hu⟩ := hwroot.symm ▸ MB.root_mem
          obtain ⟨e, x, hx, hlink⟩ := hjoinB
          exact ⟨e, GB.root.val, hbMem, x, hx, hlink.symm⟩
        | some v =>
          cases v with
          | inl p => exact False.elim huv
          | inr word' =>
            have hwords : (binaryTree (γ - 1)).Adj word word' := huv
            let edge : E(toGraph (binaryTree (γ - 1))) := ⟨s(word,word'), hwords⟩
            obtain ⟨x, hx, y, hy, hlink⟩ := MB.edge_links edge ⟨word, hu⟩ ⟨word', hv⟩ ⟨rfl, hwords⟩
            exact ⟨(MB.edgeMap edge).val, x, hx, y, hy, hlink.mono hGB⟩
  let r : Q.verts := (rootedForkGraph γ δ hγ hδ).root
  let M := rootedModelOfBranchSets Q.coe G B hBsub
    (rootedForkBranch_pairwise_disjoint hδ C MP MB hCP hCB hPB)
    (rootedForkBranch_connected hδ C hCconn hGP hGB MP MB) hAdj r hroot
  let e := subgraphSimpleGraphIso Q
  let e' : GraphMinor.Iso (toGraph Q) (Graph.ofSimpleGraph Q.coe) :=
    { vertexEquiv := e.vertexEquiv.symm
      edgeEquiv := e.edgeEquiv.symm
      isLink_iff := fun edge x y ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (e.isLink_iff (e.edgeEquiv.symm edge) (e.vertexEquiv.symm x)
            (e.vertexEquiv.symm y)).symm }
  exact M.comapSource e' rfl

end GraphMinor.GM01
