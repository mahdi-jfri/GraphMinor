module

public import GraphMinor.GM01.TreeDegrees
import GraphMinor.GM01.RootedModelMinor
import GraphMinor.GM01.RootedEmbeddings

/-!
# Ordinary models underlying rooted binary-tree models

Graph Minors I, page 60, extracts a subdivision from the rooted
`H_γ` model in `X_0`. Forget the root while keeping its branch.
At positive height a represented root edge supplies a target edge
label, so extending the edge map introduces no nonemptiness
assumption. The proved rooted-to-ordinary conversion then supplies
the model used by the subcubic subdivision construction.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- A positive-height binary-tree model supplies an actual target
edge label, through its edge from `[]` to `[false]`. -/
theorem RootedMinorModel.binaryTree_nonempty_edge_labels {α β : Type*} {γ : ℕ}
    (hγ : 0 < γ) (G : RootedGraph α β)
    (M : RootedMinorModel (binaryRootedTree γ) G) : Nonempty β := by
  have hadj : (binaryTree γ).Adj [] [false] :=
    ⟨Nat.zero_le _, by change 1 ≤ γ; omega, Or.inl ⟨false, rfl⟩⟩
  let e : E((binaryRootedTree γ).graph) := ⟨s([], [false]), hadj⟩
  exact ⟨(M.edgeMap e).val⟩

/-- The ordinary binary-tree model retains the original target root
in the branch of its empty word, for GM01 Section 5, page 60. -/
theorem RootedMinorModel.binaryTree_minor_model {α β : Type*} {γ : ℕ}
    (hγ : 0 < γ) (G : RootedGraph α β)
    (M : RootedMinorModel (binaryRootedTree γ) G) :
    ∃ (ηv : (binaryTree γ).verts → Set α) (ηe : Sym2 (binaryTree γ).verts → β),
      IsMinorModel (Graph.ofSimpleGraph (binaryTree γ).coe) G.graph ηv ηe ∧
      G.root.val ∈ ηv (binaryRootedTree γ).root := by
  let : Nonempty β := M.binaryTree_nonempty_edge_labels hγ G
  let root : (binaryTree γ).verts := ⟨[], binaryTree_root_mem γ⟩
  let M' : RootedMinorModel
      (⟨Graph.ofSimpleGraph (binaryTree γ).coe, ⟨root, mem_univ _⟩⟩ :
        RootedGraph (binaryTree γ).verts (Sym2 (binaryTree γ).verts)) G :=
    M.comapSource (subgraphSimpleGraphIso (binaryTree γ)) rfl
  obtain ⟨ηv, ηe, hbranches, _, hmodel⟩ :=
    M'.exists_isMinorModel_of_simple_with_branches (binaryTree γ).coe root G
  refine ⟨ηv, ηe, hmodel, ?_⟩
  change G.root.val ∈ ηv root
  rw [hbranches root]
  exact M'.root_mem

end GraphMinor.GM01
