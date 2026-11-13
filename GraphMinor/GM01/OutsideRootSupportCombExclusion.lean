module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.PathCombs
import GraphMinor.GM01.MarkedHalfContraction
import GraphMinor.GM01.CombJoinModels
import GraphMinor.GM01.GraphSeparators

/-!
# The comb exclusion in a component outside the root support

Graph Minors I, (5.1), pages 60–61, joins the outside component to
the root support by a path with no interior vertex in either set.
Root the component at its path endpoint. The chosen-half contraction
in the root support gives a one-cell comb retaining the other
endpoint in its spine branch. A shorter comb in the component could
then be joined along the path to produce the excluded longer comb.
This proves the exclusion needed for the length-induction bound.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The contraction and rooted-minor exclusion in the proof of GM01
(5.1), pages 60–61. The length-induction width bound is applied only
after this geometric exclusion has been proved. -/
theorem exists_root_outside_support_not_shorter_comb {α β : Type*} {γ δ : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (G : RootedGraph α β)
    (hConn : GraphConnected G.graph)
    (hNo : ¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G)
    (S : Set α) (hS : S ⊆ V(G.graph)) (hRoot : G.root.val ∈ S)
    (hSC : GraphConnected (G.graph.induce S))
    (hMinor : HasRootedMinor (binaryRootedTree γ)
      (⟨G.graph.induce S,⟨G.root.val,hRoot⟩⟩ : RootedGraph α β))
    (C : Graph α β) (hCG : C ≤ G.graph) (hCC : GraphConnected C)
    (hDis : Disjoint S V(C)) :
    ∃ v : V(C), ¬ HasRootedMinor (rootedPathComb γ (δ - 1) (by omega))
      (⟨C,v⟩ : RootedGraph α β) := by
  obtain ⟨w,hw⟩ := hCC.1
  have hwG := hCG.vertexSet_mono hw
  obtain ⟨Q,hQ⟩ := exists_path_of_adj_reachable hwG
    (hConn.2 w hwG G.root.val G.root.property)
  obtain ⟨v,hv,p,hp,P,_,hP,hPC,hPS⟩ := hQ.exists_isFromToPathWithEnds hw hRoot
  refine ⟨⟨v,hv⟩,?_⟩
  intro hShort
  let G₁ : RootedGraph α β := ⟨G.graph.induce S,⟨G.root.val,hRoot⟩⟩
  let G₂ : RootedGraph α β := ⟨C,⟨v,hv⟩⟩
  obtain ⟨MRoot⟩ := hMinor
  obtain ⟨M₁,hpM₁⟩ := exists_one_cell_comb_model_marking_target hγ G₁ hSC MRoot p hp
  obtain ⟨M₂⟩ := hShort
  have hpLast : p ∈ M₁.branch (pathCombLastSpine γ 1 (by decide)) := hpM₁
  let M := rootedModelOfCombJoin (γ := γ) (a := 1) (b := δ - 1) (by decide) (by omega)
    G G₁ G₂ (G.graph.induce_le hS) hCG rfl hDis M₁ M₂ hpLast hP.symm hPS hPC
  have hJoined : HasRootedMinor (rootedPathComb γ (1 + (δ - 1)) (by omega)) G := ⟨M⟩
  have hLength : 1 + (δ - 1) = δ := by omega
  apply hNo
  have transfer : ∀ (m : ℕ) (hm : 0 < m), m = δ →
      HasRootedMinor (rootedPathComb γ m hm) G →
      HasRootedMinor (rootedPathComb γ δ (by omega)) G := by
    intro m hm heq h
    subst m
    exact h
  exact transfer _ _ hLength hJoined

end GraphMinor.GM01
