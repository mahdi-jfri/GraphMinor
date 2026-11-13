module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.PathCombs
import GraphMinor.GM01.BinaryHalfOneCell
import GraphMinor.GM01.RootBranchExtension
import GraphMinor.GM01.RootedModelComposition
import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM09.Section2c

/-!
# Keeping the actual attachment in the contracted half

In Graph Minors I, (5.1), pages 60–61, the attachment to `B_0` may
lie on a replacing path rather than at a source vertex. Join it to
the first branch of the rooted binary model that it reaches. Choose
the source half containing that branch's source vertex and contract
that half into the one-cell comb root. The joining path meets no
other model branch, so add it to the root branch. This keeps both
the original ambient root and the actual attachment vertex.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function GraphMinor.GM09

/-- The suitably chosen half contraction in GM01 (5.1), pages 60–61,
at an actual target attachment vertex. The original root is retained,
and the attachment belongs to the new comb's root branch. -/
theorem exists_one_cell_comb_model_marking_target {α β : Type*} {γ : ℕ}
    (hγ : 0 < γ) (G : RootedGraph α β) (hConn : GraphConnected G.graph)
    (M : RootedMinorModel (binaryRootedTree γ) G) (x : α) (hx : x ∈ V(G.graph)) :
    ∃ L : RootedMinorModel (rootedPathComb γ 1 (by decide)) G,
      x ∈ L.branch (rootedPathComb γ 1 (by decide)).root := by
  let Z : Set α := ⋃ v, M.branch v
  have hRootZ : G.root.val ∈ Z := mem_iUnion.mpr ⟨(binaryRootedTree γ).root,M.root_mem⟩
  obtain ⟨P,hP⟩ := exists_path_of_adj_reachable hx (hConn.2 x hx G.root.val G.root.property)
  obtain ⟨p,⟨_,hpZ⟩,R,_,hR₀,hRZ,_⟩ := hP.exists_first_hit ⟨G.root.val,hP.right_mem,hRootZ⟩
  have hR := hR₀.mono hP.le
  obtain ⟨v,hpv⟩ := mem_iUnion.mp hpZ
  obtain ⟨K,hvK⟩ := exists_one_cell_comb_model_marking_binary_vertex hγ v
  let L₀ := K.trans M
  have hpL₀ : p ∈ L₀.branch (rootedPathComb γ 1 (by decide)).root :=
    (M.mem_liftSet_iff _ p).mpr ⟨v,hvK,hpv⟩
  have hSubZ : ∀ w, L₀.branch w ⊆ Z := by
    intro w y hy
    change y ∈ M.liftSet (K.branch w) at hy
    obtain ⟨z,_,hyz⟩ := (M.mem_liftSet_iff _ y).mp hy
    exact mem_iUnion.mpr ⟨z,hyz⟩
  have hDis : ∀ w, w ≠ (rootedPathComb γ 1 (by decide)).root → Disjoint (L₀.branch w) V(R) := by
    intro w hw
    apply disjoint_left.mpr
    intro y hy hyR
    have hyp : y = p := mem_singleton_iff.mp
      (show y ∈ ({p} : Set α) from hRZ ▸ ⟨hyR,hSubZ w hy⟩)
    exact disjoint_left.mp (L₀.branch_disjoint hw) hy (hyp.symm ▸ hpL₀)
  obtain ⟨L,_,hxL⟩ := exists_root_branch_extension_along_path L₀ hpL₀ hR hDis
  exact ⟨L,hxL⟩

end GraphMinor.GM01
