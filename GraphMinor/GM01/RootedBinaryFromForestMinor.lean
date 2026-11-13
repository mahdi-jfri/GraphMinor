module

public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.RootedBinaryInForest
import GraphMinor.GM01.RootAnOrdinaryModel
import GraphMinor.GM01.RootedModelComposition
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.SubgraphIso
import GraphMinor.Minor.Basic

/-!
# Rooting the binary minor in an attached tree minor

In the page-60 contraction of Graph Minors I, an attachment can enter
its three-branch-tree subdivision anywhere. An ordinary tree model in
a connected target can be rooted at some source vertex by following
a path to its first branch. At that source vertex, the proved
third-arm construction supplies the rooted binary tree. Compose the
two models to retain the actual target attachment as root.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- An attached `Y_γ` minor supplies rooted `H_γ` at any chosen target
vertex, the arbitrary-entry detail in the GM01 page-60 contraction. -/
theorem rootedBinaryTree_of_forestTree_minor {α β : Type*} [Nonempty β] {γ : ℕ}
    (G : RootedGraph α β) (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    (hconn : GraphConnected G.graph) (h : IsIsoMinor (forestTreeGraph γ) G.graph) :
    HasRootedMinor (binaryRootedTree γ) G := by
  let : Nonempty (forestTree γ).verts := ⟨⟨none, forestTree_centre_mem γ⟩⟩
  have hSimple : IsIsoMinor (Graph.ofSimpleGraph (forestTree γ).coe) G.graph :=
    (subgraphSimpleGraphIso (forestTree γ)).isIsoMinor_left h
  obtain ⟨ηv,ηe,hModel⟩ := exists_isMinorModel_of_isIsoMinor hVfin hEfin hSimple
  obtain ⟨r,⟨M⟩⟩ := exists_rooted_model_of_ordinary G hconn hModel
  let iso := subgraphSimpleGraphIso (forestTree γ)
  let iso' : GraphMinor.Iso (toGraph (forestTree γ)) (Graph.ofSimpleGraph (forestTree γ).coe) :=
    { vertexEquiv := iso.vertexEquiv.symm
      edgeEquiv := iso.edgeEquiv.symm
      isLink_iff := fun edge x y ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (iso.isLink_iff (iso.edgeEquiv.symm edge) (iso.vertexEquiv.symm x)
            (iso.vertexEquiv.symm y)).symm }
  have hRooted : HasRootedMinor
      (⟨forestTreeGraph γ,r⟩ : RootedGraph ForestTreeVertex (Sym2 ForestTreeVertex)) G :=
    ⟨M.comapSource iso' rfl⟩
  exact (rootedBinaryTree_of_forestTree r).trans hRooted

end GraphMinor.GM01
