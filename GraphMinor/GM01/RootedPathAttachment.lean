module

public import GraphMinor.GM01.RootedGraphs
public import GraphMinor.GM01.SubdivisionConnected

/-!
# Moving a model root along an attached path

The graph `H` on page 55 of Graph Minors I includes the path from the
ambient root to the first comb centre. Add that path to the branch of
the source root. The path meets the old graph only at its old root, so
it misses every other branch. Paths in the old root branch and in the
added path join at that root, proving connectivity of the enlarged
branch and retaining the model's edge injection.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- Move the target root along a path disjoint from every nonroot branch.
The source-root branch gains exactly the vertices of that path. -/
noncomputable def RootedMinorModel.attachRootPathOfDisjointBranches {α β γ δ : Type*}
    {H : RootedGraph α β} {N : RootedGraph γ δ} (M : RootedMinorModel H N)
    {G R : Graph γ δ} (hN : N.graph ≤ G) (root : γ)
    (hR : IsGraphPathWithEnds G R root N.root.val)
    (hDisj : ∀ v : V(H.graph), v ≠ H.root → Disjoint (M.branch v) V(R)) :
    RootedMinorModel H
      (⟨subgraphUnion G N.graph R, ⟨root, Or.inr hR.left_mem⟩⟩ : RootedGraph γ δ) := by
  classical
  let J := subgraphUnion G N.graph R
  have hNJ : N.graph ≤ J := le_subgraphUnion_left hN hR.le
  have hRJ : R ≤ J := le_subgraphUnion_right hN hR.le
  let B (v : V(H.graph)) := if v = H.root then M.branch v ∪ V(R) else M.branch v
  have old_subset : ∀ v, M.branch v ⊆ B v := by
    intro v
    by_cases hv : v = H.root
    · simp only [B, hv, ↓reduceIte]
      exact subset_union_left
    · simp only [B, hv, ↓reduceIte]
      exact Subset.rfl
  have new_subset : V(R) ⊆ B H.root := by
    intro x hx
    simp only [B, ↓reduceIte]
    exact Or.inr hx
  have other_disjoint := hDisj
  have hBsub : ∀ v, B v ⊆ V(J) := by
    intro v x hx
    by_cases hv : v = H.root
    · simp only [B, hv, ↓reduceIte] at hx
      exact hx.elim (fun h ↦ Or.inl (M.branch_subset H.root h)) Or.inr
    · simp only [B, hv, ↓reduceIte] at hx
      exact Or.inl (M.branch_subset v hx)
  have branch_lift : ∀ v, ∀ x ∈ M.branch v, ∀ y ∈ M.branch v,
      Relation.ReflTransGen (J.induce (B v)).Adj x y := by
    intro v x hx y hy
    apply Relation.ReflTransGen.mono ?_ x y ((M.branch_connected v).2 x hx y hy)
    intro a b hab
    obtain ⟨e, he⟩ := hab
    exact ⟨e, he.1.mono hNJ, old_subset v he.2.1, old_subset v he.2.2⟩
  refine
    { branch := B
      branch_subset := hBsub
      branch_disjoint := ?_
      branch_connected := ?_
      edgeMap := M.edgeMap.trans
        ⟨fun e ↦ ⟨e.val, hNJ.edgeSet_mono e.property⟩,
          fun _ _ heq ↦ Subtype.ext (congrArg (fun e : E(J) ↦ e.val) heq)⟩
      edge_links := ?_
      root_mem := ?_ }
  · intro u v huv
    by_cases hu : u = H.root
    · have hv : v ≠ H.root := fun hv ↦ huv (hu.trans hv.symm)
      simp only [B, hu, hv, ↓reduceIte]
      simpa only [hu] using (M.branch_disjoint huv).union_left (other_disjoint v hv).symm
    · by_cases hv : v = H.root
      · simp only [B, hu, hv, ↓reduceIte]
        simpa only [hv] using (M.branch_disjoint huv).union_right (other_disjoint u hu)
      · simpa only [B, hu, hv, ↓reduceIte] using M.branch_disjoint huv
  · intro v
    by_cases hv : v = H.root
    · subst v
      have htoOld : ∀ x ∈ B H.root,
          Relation.ReflTransGen (J.induce (B H.root)).Adj x N.root.val := by
        intro x hx
        simp only [B, ↓reduceIte] at hx
        rcases hx with hx | hx
        · exact branch_lift H.root x hx N.root.val M.root_mem
        · have hr := (graphConnected_of_isGraphPath hR).2 x hx N.root.val hR.right_mem
          apply Relation.ReflTransGen.mono ?_ x N.root.val hr
          intro a b hab
          obtain ⟨e, he⟩ := hab
          exact ⟨e, he.mono hRJ, new_subset he.left_mem, new_subset he.right_mem⟩
      exact ⟨⟨N.root.val, old_subset H.root M.root_mem⟩, fun x hx y hy ↦
        (htoOld x hx).trans (Std.Symm.symm _ _ (htoOld y hy))⟩
    · have hB : B v = M.branch v := by simp only [B, hv, ↓reduceIte]
      obtain ⟨x, hx⟩ := (M.branch_connected v).1
      refine ⟨⟨x, old_subset v hx⟩, ?_⟩
      intro a ha b hb
      exact branch_lift v a (hB ▸ ha) b (hB ▸ hb)
  · intro e u v he
    obtain ⟨x, hx, y, hy, hxy⟩ := M.edge_links e u v he
    exact ⟨x, old_subset u hx, y, old_subset v hy, hxy.mono hNJ⟩
  · exact new_subset hR.left_mem

/-- Extending the root branch along an avoiding path retains every old
branch vertex, including the original target root. -/
theorem RootedMinorModel.branch_subset_attachRootPathOfDisjointBranches {α β γ δ : Type*}
    {H : RootedGraph α β} {N : RootedGraph γ δ} (M : RootedMinorModel H N)
    {G R : Graph γ δ} (hN : N.graph ≤ G) (root : γ)
    (hR : IsGraphPathWithEnds G R root N.root.val)
    (hDisj : ∀ v : V(H.graph), v ≠ H.root → Disjoint (M.branch v) V(R))
    (v : V(H.graph)) :
    M.branch v ⊆ (M.attachRootPathOfDisjointBranches hN root hR hDisj).branch v := by
  dsimp only [RootedMinorModel.attachRootPathOfDisjointBranches]
  split_ifs
  · exact subset_union_left
  · exact Subset.rfl

/-- A path attached to the old graph only at its root is disjoint from
all other model branches, so it moves the target root as above. -/
noncomputable def RootedMinorModel.attachRootPath {α β γ δ : Type*}
    {H : RootedGraph α β} {N : RootedGraph γ δ} (M : RootedMinorModel H N)
    {G R : Graph γ δ} (hN : N.graph ≤ G) (root : γ)
    (hR : IsGraphPathWithEnds G R root N.root.val)
    (hmeet : V(N.graph) ∩ V(R) ⊆ {N.root.val}) :
    RootedMinorModel H
      (⟨subgraphUnion G N.graph R, ⟨root, Or.inr hR.left_mem⟩⟩ : RootedGraph γ δ) :=
  M.attachRootPathOfDisjointBranches hN root hR (by
    intro v hv
    apply disjoint_left.mpr
    intro x hx hxR
    have hroot : x = N.root.val := hmeet ⟨M.branch_subset v hx, hxR⟩
    exact disjoint_left.mp (M.branch_disjoint hv) hx (hroot.symm ▸ M.root_mem))

/-- Moving the target root along the separate path retains every old
branch vertex, in particular the last centre used in GM01 (4.10). -/
theorem RootedMinorModel.branch_subset_attachRootPath {α β γ δ : Type*}
    {H : RootedGraph α β} {N : RootedGraph γ δ} (M : RootedMinorModel H N)
    {G R : Graph γ δ} (hN : N.graph ≤ G) (root : γ)
    (hR : IsGraphPathWithEnds G R root N.root.val)
    (hmeet : V(N.graph) ∩ V(R) ⊆ {N.root.val}) (v : V(H.graph)) :
    M.branch v ⊆ (M.attachRootPath hN root hR hmeet).branch v := by
  dsimp only [RootedMinorModel.attachRootPath, RootedMinorModel.attachRootPathOfDisjointBranches]
  split_ifs
  · exact subset_union_left
  · exact Subset.rfl

end GraphMinor.GM01
