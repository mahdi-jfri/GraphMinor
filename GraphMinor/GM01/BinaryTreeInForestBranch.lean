module

public import GraphMinor.GM01.ForestBranchComplements
public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.RootedSubgraphBranchModels
import GraphMinor.GM01.RootedSubgraphModelMinor
import GraphMinor.GM01.Basic

/-!
# The binary tree inside each forest-tree branch

For the lower bound used in Graph Minors I, (1.2), page 40,
each branch of `Y` is a binary tree one level shorter. Map a word
to the same word with its chosen branch label. Singleton branches
verify the resulting ordinary minor inside that branch itself.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The binary tree one level shorter occurs inside every branch of
`Y`, as used to iterate the page-40 tree-width lower bound. -/
theorem binaryTree_isIsoMinor_forestTreeBranch (h : ℕ) (i : Fin 3) :
    IsIsoMinor (toGraph (binaryTree h))
      ((forestTreeGraph (h + 1)).induce (forestTreeBranchVertices (h + 1) i)) := by
  let G : RootedGraph ForestTreeVertex (Sym2 ForestTreeVertex) :=
    ⟨(forestTreeGraph (h + 1)).induce (forestTreeBranchVertices (h + 1) i),
      ⟨some (i, []), ⟨by change 0 + 1 ≤ h + 1; omega, [], rfl⟩⟩⟩
  let f (x : (binaryTree h).verts) : ForestTreeVertex := some (i, x.val)
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg Prod.snd (Option.some.inj he))
  have hmem : ∀ x : (binaryTree h).verts, f x ∈ V(G.graph) := by
    intro x
    exact ⟨Nat.add_le_add_right x.property 1, x.val, rfl⟩
  let M := rootedModelOfSubgraphBranchSets (binaryTree h) G
    (fun x ↦ {f x}) (fun x ↦ singleton_subset_iff.mpr (hmem x))
    (fun _ _ hxy ↦ disjoint_singleton.mpr (fun he ↦ hxy (hf he)))
    (fun x ↦ by
      refine ⟨⟨f x, rfl⟩, ?_⟩
      intro u hu v hv
      have hu' : u = f x := hu
      have hv' : v = f x := hv
      subst u
      subst v
      exact .refl)
    (by
      intro x y hxy
      have ha : (forestTree (h + 1)).Adj (f x) (f y) := by
        refine ⟨Nat.add_le_add_right x.property 1, Nat.add_le_add_right y.property 1, ?_⟩
        rcases hxy.2.2 with ⟨bit, he⟩ | ⟨bit, he⟩
        · exact Or.inl ⟨(by intro hn; cases hn),
            by simp only [f, he, forestTreeParent]⟩
        · exact Or.inr ⟨(by intro hn; cases hn),
            by simp only [f, he, forestTreeParent]⟩
      exact ⟨s(f x, f y), f x, rfl, f y, rfl, ⟨rfl, ha⟩, hmem x, hmem y⟩)
    ⟨[], binaryTree_root_mem h⟩ rfl
  have hle : G.graph ≤ forestTreeGraph (h + 1) :=
    (forestTreeGraph (h + 1)).induce_le (fun _ hv ↦ hv.1)
  exact M.isIsoMinor_of_subgraph_source (binaryTree_vertices_finite h)
    (binaryRootedTree h).root G
    ((forestTree_vertices_finite (h + 1)).subset hle.vertexSet_mono)
    ((finite_edgeSet_of_finite_verts (forestTree_vertices_finite (h + 1))).subset hle.edgeSet_mono)

end GraphMinor.GM01
