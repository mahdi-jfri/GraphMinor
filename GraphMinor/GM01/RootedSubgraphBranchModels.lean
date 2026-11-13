module

public import GraphMinor.GM01.RootedBranchModels
public import GraphMinor.GM01.Defs
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.SubgraphIso

/-!
# Branch models with a simple-subgraph source

The source trees in Graph Minors I, Part 3, are represented as simple
subgraphs on their word and spine labels. Connected disjoint branches
with the required joining edges give a rooted model. Apply the proved
simple-graph branch constructor and transfer its source through the
canonical isomorphism from the graph on those labels.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The connected branch-set constructor for a simple-subgraph source,
used for the rooted source contractions in GM01 Part 3, page 59. -/
noncomputable def rootedModelOfSubgraphBranchSets {α β ν : Type*}
    (H : (⊤ : SimpleGraph ν).Subgraph) (G : RootedGraph α β)
    (B : H.verts → Set α) (hB : ∀ v, B v ⊆ V(G.graph))
    (hdisj : Pairwise fun u v ↦ Disjoint (B u) (B v))
    (hconn : ∀ v, GraphConnected (G.graph.induce (B v)))
    (hadj : ∀ {u v}, H.coe.Adj u v → ∃ e x, x ∈ B u ∧ ∃ y, y ∈ B v ∧ G.graph.IsLink e x y)
    (root : H.verts) (hroot : G.root.val ∈ B root) :
    RootedMinorModel (⟨toGraph H, root⟩ : RootedGraph ν (Sym2 ν)) G := by
  let M := rootedModelOfBranchSets H.coe G B hB hdisj hconn hadj root hroot
  let iso := subgraphSimpleGraphIso H
  let iso' : GraphMinor.Iso (toGraph H) (Graph.ofSimpleGraph H.coe) :=
    { vertexEquiv := iso.vertexEquiv.symm
      edgeEquiv := iso.edgeEquiv.symm
      isLink_iff := fun e u v ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (iso.isLink_iff (iso.edgeEquiv.symm e) (iso.vertexEquiv.symm u) (iso.vertexEquiv.symm v)).symm }
  exact M.comapSource iso' rfl


/-- The simple-subgraph branch constructor retains each specified branch. -/
theorem rootedModelOfSubgraphBranchSets_branch {α β ν : Type*}
    (H : (⊤ : SimpleGraph ν).Subgraph) (G : RootedGraph α β)
    (B : H.verts → Set α) (hB : ∀ v, B v ⊆ V(G.graph))
    (hdisj : Pairwise fun u v ↦ Disjoint (B u) (B v))
    (hconn : ∀ v, GraphConnected (G.graph.induce (B v)))
    (hadj : ∀ {u v}, H.coe.Adj u v → ∃ e x, x ∈ B u ∧ ∃ y, y ∈ B v ∧ G.graph.IsLink e x y)
    (root : H.verts) (hroot : G.root.val ∈ B root) (v : H.verts) :
    (rootedModelOfSubgraphBranchSets H G B hB hdisj hconn hadj root hroot).branch v = B v := by
  unfold rootedModelOfSubgraphBranchSets
  exact rootedModelOfBranchSets_branch H.coe G B hB hdisj hconn hadj root hroot ⟨v,Set.mem_univ _⟩

end GraphMinor.GM01
