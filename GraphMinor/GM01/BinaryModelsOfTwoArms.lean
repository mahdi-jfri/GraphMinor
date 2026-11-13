module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.RootedGraphs
import GraphMinor.GM01.RootedSubgraphBranchModels
import GraphMinor.GM01.ConnectedInducedSets

/-!
# Joining two binary arms to a root piece

The packing in Graph Minors I, (5.2), page 61, starts with a rooted
binary tree in the initial part of a fork. Join two disjoint models
of height `γ−1` to the connected root piece. A nonroot word chooses
its arm by its last bit, and its remaining word chooses the branch
inside that arm. The root piece is the empty-word branch.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

private theorem dropLast_mem_binary {γ : ℕ} {word : List Bool}
    (hw : word ∈ (binaryTree γ).verts) (hne : word ≠ []) :
    word.dropLast ∈ (binaryTree (γ - 1)).verts := by
  have hlen := congrArg List.length (List.dropLast_append_getLast hne)
  change word.length ≤ γ at hw
  change word.dropLast.length ≤ γ - 1
  simp only [List.length_append,List.length_singleton] at hlen
  omega

private def binaryTwoArmBranch {α β : Type*} {γ : ℕ} (C : Set α)
    (B : Bool → RootedGraph α β)
    (MB : ∀ bit, RootedMinorModel (binaryRootedTree (γ - 1)) (B bit))
    (v : (binaryTree γ).verts) : Set α :=
  if h : v.val = [] then C else
    (MB (v.val.getLast h)).branch ⟨v.val.dropLast,dropLast_mem_binary v.property h⟩

/-- Two disjoint rooted binary arms, joined by actual edges to the
root piece, form the binary tree used at the start of the packing
in GM01 (5.2), page 61. -/
noncomputable def rootedBinaryTreeModelOfTwoArms {α β : Type*} {γ : ℕ}
    (G : RootedGraph α β) (C : Set α) (hC : C ⊆ V(G.graph))
    (hCC : GraphConnected (G.graph.induce C)) (hRoot : G.root.val ∈ C)
    (B : Bool → RootedGraph α β) (hBG : ∀ bit, (B bit).graph ≤ G.graph)
    (MB : ∀ bit, RootedMinorModel (binaryRootedTree (γ - 1)) (B bit))
    (hDis : ∀ bit, Disjoint C V((B bit).graph))
    (hBD : Pairwise fun a b ↦ Disjoint V((B a).graph) V((B b).graph))
    (hJoin : ∀ bit, ∃ e x, x ∈ C ∧ G.graph.IsLink e x (B bit).root.val) :
    RootedMinorModel (binaryRootedTree γ) G := by
  let A := binaryTwoArmBranch C B MB
  have hSub : ∀ v, A v ⊆ V(G.graph) := by
    intro v
    by_cases hv : v.val = []
    · simpa only [A,binaryTwoArmBranch,hv,↓reduceDIte] using hC
    · simp only [A,binaryTwoArmBranch,hv,↓reduceDIte]
      exact ((MB _).branch_subset _).trans (hBG _).vertexSet_mono
  have hAD : Pairwise fun u v ↦ Disjoint (A u) (A v) := by
    intro u v huv
    by_cases hu : u.val = []
    · have hv : v.val ≠ [] := fun hv ↦ huv (Subtype.ext (hu.trans hv.symm))
      simp only [A,binaryTwoArmBranch,hu,hv,↓reduceDIte]
      exact (hDis _).mono_right ((MB _).branch_subset _)
    · by_cases hv : v.val = []
      · simp only [A,binaryTwoArmBranch,hu,hv,↓reduceDIte]
        exact ((hDis _).mono_right ((MB _).branch_subset _)).symm
      · simp only [A,binaryTwoArmBranch,hu,hv,↓reduceDIte]
        by_cases hbit : u.val.getLast hu = v.val.getLast hv
        · rw [hbit]
          apply (MB _).branch_disjoint
          intro heq
          have hdrop : u.val.dropLast = v.val.dropLast := congrArg Subtype.val heq
          apply huv
          apply Subtype.ext
          calc
            u.val = u.val.dropLast ++ [u.val.getLast hu] := (List.dropLast_append_getLast hu).symm
            _ = v.val.dropLast ++ [v.val.getLast hv] := by rw [hdrop,hbit]
            _ = v.val := List.dropLast_append_getLast hv
        · exact (hBD hbit).mono ((MB _).branch_subset _) ((MB _).branch_subset _)
  have hAC : ∀ v, GraphConnected (G.graph.induce (A v)) := by
    intro v
    by_cases hv : v.val = []
    · simpa only [A,binaryTwoArmBranch,hv,↓reduceDIte] using hCC
    · simp only [A,binaryTwoArmBranch,hv,↓reduceDIte]
      exact graphConnected_induce_of_subgraph
        (((B _).graph.induce_le ((MB _).branch_subset _)).trans (hBG _)) ((MB _).branch_connected _)
  have hParent : ∀ (u v : (binaryTree γ).verts) (bit : Bool), v.val = bit :: u.val →
      ∃ e x, x ∈ A u ∧ ∃ y, y ∈ A v ∧ G.graph.IsLink e x y := by
    rintro ⟨u,huMem⟩ ⟨v,hvMem⟩ bit hv
    change v = bit :: u at hv
    subst v
    by_cases hu : u = []
    · subst u
      simp only [A,binaryTwoArmBranch,List.cons_ne_nil,↓reduceDIte,List.getLast_singleton,
        List.dropLast_singleton]
      obtain ⟨e,x,hx,he⟩ := hJoin bit
      exact ⟨e,x,hx,(B bit).root.val,(MB bit).root_mem,he⟩
    · have hU := dropLast_mem_binary huMem hu
      have hV := dropLast_mem_binary hvMem (List.cons_ne_nil bit u)
      have hDrop : (bit :: u).dropLast = bit :: u.dropLast := List.dropLast_cons_of_ne_nil hu
      have hBinary : (binaryTree (γ - 1)).Adj u.dropLast (bit :: u).dropLast :=
        ⟨hU,hV,Or.inl ⟨bit,hDrop⟩⟩
      let edge : E((binaryRootedTree (γ - 1)).graph) := ⟨s(u.dropLast,(bit :: u).dropLast),hBinary⟩
      obtain ⟨x,hx,y,hy,hxy⟩ := (MB (u.getLast hu)).edge_links edge
        ⟨u.dropLast,hU⟩ ⟨(bit :: u).dropLast,hV⟩ ⟨rfl,hBinary⟩
      have hLast : (bit :: u).getLast (List.cons_ne_nil bit u) = u.getLast hu := List.getLast_cons hu
      have hy' : y ∈ (MB ((bit :: u).getLast (List.cons_ne_nil bit u))).branch
          ⟨(bit :: u).dropLast,hV⟩ := hLast.symm ▸ hy
      simp only [A,binaryTwoArmBranch,hu,List.cons_ne_nil,↓reduceDIte]
      exact ⟨((MB _).edgeMap edge).val,x,hx,y,hy',hxy.mono (hBG _)⟩
  have hAdj : ∀ {u v : (binaryTree γ).verts}, (binaryTree γ).coe.Adj u v →
      ∃ e x, x ∈ A u ∧ ∃ y, y ∈ A v ∧ G.graph.IsLink e x y := by
    intro u v huv
    rcases huv.2.2 with ⟨bit,hv⟩ | ⟨bit,hu⟩
    · exact hParent u v bit hv
    · obtain ⟨e,y,hy,x,hx,he⟩ := hParent v u bit hu
      exact ⟨e,x,hx,y,hy,he.symm⟩
  exact rootedModelOfSubgraphBranchSets (binaryTree γ) G A hSub hAD hAC hAdj
    (binaryRootedTree γ).root (by
      change G.root.val ∈ binaryTwoArmBranch C B MB ⟨[],binaryTree_root_mem γ⟩
      simpa only [binaryTwoArmBranch,↓reduceDIte] using hRoot)

end GraphMinor.GM01
