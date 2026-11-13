module

public import GraphMinor.GM01.RootedPathAttachment

/-!
# Extending a root branch while keeping the original target root

In Graph Minors I, (5.1), pages 60–61, the contracted root half must
contain the ambient root and the attachment vertex. A path to a
point of the root branch may be added when it avoids all other
branches. Temporarily distinguish that point, attach the path, then
restore the original distinguished root. Every old branch is retained.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- Distinguish another target vertex already lying in the root branch.
The graph, branches, and represented edges are unchanged. -/
def RootedMinorModel.retarget {α β γ δ : Type*}
    {H : RootedGraph α β} {G : RootedGraph γ δ} (M : RootedMinorModel H G)
    (root : V(G.graph)) (hroot : root.val ∈ M.branch H.root) :
    RootedMinorModel H (⟨G.graph,root⟩ : RootedGraph γ δ) where
  branch := M.branch
  branch_subset := M.branch_subset
  branch_disjoint := M.branch_disjoint
  branch_connected := M.branch_connected
  edgeMap := M.edgeMap
  edge_links := M.edge_links
  root_mem := hroot

/-- Changing the distinguished target root retains each branch exactly. -/
theorem RootedMinorModel.retarget_branch {α β γ δ : Type*}
    {H : RootedGraph α β} {G : RootedGraph γ δ} (M : RootedMinorModel H G)
    (root : V(G.graph)) (hroot : root.val ∈ M.branch H.root) (v : V(H.graph)) :
    (M.retarget root hroot).branch v = M.branch v := by
  unfold RootedMinorModel.retarget
  rfl

/-- Add a path ending in the root branch while keeping the original
target root. This retains a marked attachment in GM01 (5.1). -/
theorem exists_root_branch_extension_along_path {α β γ δ : Type*}
    {H : RootedGraph α β} {G : RootedGraph γ δ} (M : RootedMinorModel H G)
    {x p : γ} (hp : p ∈ M.branch H.root) {R : Graph γ δ}
    (hR : IsGraphPathWithEnds G.graph R x p)
    (hDis : ∀ v : V(H.graph), v ≠ H.root → Disjoint (M.branch v) V(R)) :
    ∃ L : RootedMinorModel H G, (∀ v, M.branch v ⊆ L.branch v) ∧ x ∈ L.branch H.root := by
  let target : V(G.graph) := ⟨p,M.branch_subset H.root hp⟩
  let M' := M.retarget target hp
  have hDis' : ∀ v : V(H.graph), v ≠ H.root → Disjoint (M'.branch v) V(R) := by
    intro v hv
    rw [RootedMinorModel.retarget_branch]
    exact hDis v hv
  let A := M'.attachRootPathOfDisjointBranches le_rfl x hR hDis'
  let A' : RootedMinorModel H
      (⟨G.graph,⟨x,hR.le.vertexSet_mono hR.left_mem⟩⟩ : RootedGraph γ δ) :=
    A.mono (subgraphUnion_le le_rfl hR.le) rfl
  have hSub : ∀ v, M.branch v ⊆ A'.branch v := by
    intro v
    have h := M'.branch_subset_attachRootPathOfDisjointBranches le_rfl x hR hDis' v
    rw [RootedMinorModel.retarget_branch] at h
    exact h
  let L : RootedMinorModel H G := A'.retarget G.root (hSub H.root M.root_mem)
  refine ⟨L,?_,?_⟩
  · intro v
    rw [RootedMinorModel.retarget_branch]
    exact hSub v
  · rw [RootedMinorModel.retarget_branch]
    exact A'.root_mem

end GraphMinor.GM01
