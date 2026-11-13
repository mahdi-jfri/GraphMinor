module

public import GraphMinor.GM01.PathCombs
public import GraphMinor.GM01.RootedPathAttachment
public import GraphMinor.GM01.RootedModelOfMinor
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.SubgraphIso

/-!
# The rooted comb model inside the union graph

The subdivision construction on page 55 of Graph Minors I retains an
ordinary comb model with the first centre in its root branch. Root that
model at the centre, then adjoin the separate root path to that branch.
The resulting graph `H` therefore retains the original rooted comb,
with the ambient root. The explicit vertex and edge isomorphism between
the source representations transfers this model to the paper's comb.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- The graph `H` formed on page 55 retains the rooted comb, with the
ambient root, after the separate path has been added. -/
theorem rootedPathComb_minor_in_union {α β : Type*} {γ δ : ℕ} (hδ : 0 < δ)
    (G : RootedGraph α β) {N R : Graph α β} (hN : N ≤ G.graph)
    {ηv : (pathComb γ δ).verts → Set α} {ηe : Sym2 (pathComb γ δ).verts → β}
    (hModel : IsMinorModel (Graph.ofSimpleGraph (pathComb γ δ).coe) N ηv ηe)
    (a : α) (ha : a ∈ ηv (rootedPathComb γ δ hδ).root)
    (hR : IsGraphPathWithEnds G.graph R G.root.val a)
    (hmeet : V(N) ∩ V(R) ⊆ {a}) :
    HasRootedMinor (rootedPathComb γ δ hδ)
      (⟨subgraphUnion G.graph N R, ⟨G.root.val, Or.inr hR.left_mem⟩⟩ : RootedGraph α β) := by
  let r := (rootedPathComb γ δ hδ).root
  have haN : a ∈ V(N) := hModel.vertex_subset r (mem_univ _) ha
  let M := rootedModelOfMinorModel hModel r ⟨a, haN⟩ ha
  let L := M.attachRootPath hN G.root.val hR hmeet
  let e := subgraphSimpleGraphIso (pathComb γ δ)
  let e' : GraphMinor.Iso (toGraph (pathComb γ δ))
      (Graph.ofSimpleGraph (pathComb γ δ).coe) :=
    { vertexEquiv := e.vertexEquiv.symm
      edgeEquiv := e.edgeEquiv.symm
      isLink_iff := fun edge x y ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (e.isLink_iff (e.edgeEquiv.symm edge) (e.vertexEquiv.symm x)
            (e.vertexEquiv.symm y)).symm }
  exact ⟨L.comapSource e' rfl⟩

end GraphMinor.GM01
