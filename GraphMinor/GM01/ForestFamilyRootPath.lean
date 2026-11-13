module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM09.Defs
import GraphMinor.GM01.RootedPathAttachment

/-!
# Extending a packed root support along its joining path

In Graph Minors I, (5.2), page 61, replace the new root support
`X'_0` by `X'_0 ∪ V(P)` to reach the original ambient root. The
joining path meets the component only at its chosen root. Add it
to the rooted binary model's root branch. The other supports stay
disjoint from the path, and their ordinary minors pass to the
ambient induced graphs without changing their vertex sets.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The root-path extension `X'_0 ∪ V(P)` in GM01 (5.2), page 61,
with the rooted minor and all disjointness proved in the ambient graph. -/
theorem exists_rooted_forest_family_with_root_path {α β : Type*} {γ n : ℕ}
    (G G₀ : RootedGraph α β) (hG₀G : G₀.graph ≤ G.graph)
    (F : RootedForestFamily G₀ γ n) {P : Graph α β}
    (hP : IsGraphPathWithEnds G.graph P G.root.val G₀.root.val)
    (hMeet : V(P) ∩ V(G₀.graph) = {G₀.root.val}) :
    ∃ F' : RootedForestFamily G γ n,
      F'.rootSet = F.rootSet ∪ V(P) ∧ ∀ i, F'.otherSet i = F.otherSet i := by
  let S := F.rootSet ∪ V(P)
  have hS : S ⊆ V(G.graph) := union_subset (F.root_subset.trans hG₀G.vertexSet_mono) hP.le.vertexSet_mono
  have hRoot : G.root.val ∈ S := Or.inr hP.left_mem
  let N : RootedGraph α β := ⟨G₀.graph.induce F.rootSet,⟨G₀.root.val,F.root_mem⟩⟩
  have hNG : N.graph ≤ G.graph := (G₀.graph.induce_le F.root_subset).trans hG₀G
  obtain ⟨M⟩ := F.root_minor
  have hNP : V(N.graph) ∩ V(P) ⊆ {G₀.root.val} := by
    intro x hx
    exact hMeet ▸ ⟨hx.2,F.root_subset hx.1⟩
  let L := M.attachRootPath hNG G.root.val hP hNP
  have hUnionG : subgraphUnion G.graph N.graph P ≤ G.graph := subgraphUnion_le hNG hP.le
  have hUnionS : subgraphUnion G.graph N.graph P ≤ G.graph.induce S := by
    refine ⟨Subset.rfl,?_⟩
    intro e x y he
    exact ⟨he.mono hUnionG,he.left_mem,he.right_mem⟩
  have hRootMinor : HasRootedMinor (binaryRootedTree γ)
      (⟨G.graph.induce S,⟨G.root.val,hRoot⟩⟩ : RootedGraph α β) := ⟨L.mono hUnionS rfl⟩
  have hOther : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (G.graph.induce (F.otherSet i)) := by
    intro i
    have hInd : G₀.graph.induce (F.otherSet i) ≤ G.graph.induce (F.otherSet i) :=
      ⟨Subset.rfl,fun _ _ _ he ↦ ⟨he.1.mono hG₀G,he.2.1,he.2.2⟩⟩
    obtain ⟨K,hK,edges,hEdges,hIso⟩ := F.other_minor i
    exact ⟨K,hK.trans hInd,edges,hEdges,hIso⟩
  have hPD : ∀ i, Disjoint V(P) (F.otherSet i) := by
    intro i
    apply disjoint_left.mpr
    intro x hxP hxD
    have hxr : x = G₀.root.val := mem_singleton_iff.mp
      (show x ∈ ({G₀.root.val} : Set α) from hMeet ▸ ⟨hxP,F.other_subset i hxD⟩)
    exact disjoint_left.mp (F.root_disjoint i) (hxr.symm ▸ F.root_mem) hxD
  let F' : RootedForestFamily G γ n := {
    rootSet := S
    otherSet := F.otherSet
    root_subset := hS
    other_subset := fun i ↦ (F.other_subset i).trans hG₀G.vertexSet_mono
    other_disjoint := F.other_disjoint
    root_disjoint := fun i ↦ (F.root_disjoint i).union_left (hPD i)
    root_mem := hRoot
    root_minor := hRootMinor
    other_minor := hOther }
  exact ⟨F',rfl,fun _ ↦ rfl⟩

end GraphMinor.GM01
