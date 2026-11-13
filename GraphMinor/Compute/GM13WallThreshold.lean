module

public import GraphMinor.Compute.Algorithm72

/-!
# Small width parameters in Graph Minors XIII, (7.1)

Two parallel edges have branch-width two. They cannot contain an elementary
wall of height at least two, since a model of that wall needs more than two
disjoint nonempty branch sets. Thus a threshold that forces such a wall is
at least three. This supplies the small-parameter check before using (3.3).
-/

public section
namespace GraphMinor.Compute

open GraphMinor GM13 Graph Set SimpleGraph Classical

private theorem two_le_width_of_parallel_edges71 {α β ι : Type*} [Fintype ι]
    {G : Graph α β} (hV : V(G).Finite) {a b : α} (hab : a ≠ b)
    {e₀ e₁ : β} (hne : e₀ ≠ e₁) (h₀ : G.IsLink e₀ a b) (h₁ : G.IsLink e₁ a b)
    {T : SimpleGraph ι} {τ : β → ι} (hbd : IsGraphBranchDecomposition G T τ) :
    2 ≤ graphBranchDecompWidth G T τ := by
  have hT : GM10.IsTernaryTree T := by
    rcases hbd.isTernaryOrEmpty with hempty | ht
    · exact (hempty.false (τ e₀)).elim
    · exact ht
  have hleaf : GM10.IsLeaf T (τ e₀) := hbd.bijOn.mapsTo h₀.edge_mem
  obtain ⟨w, hadj, _⟩ := hT.exists_adj_of_isLeaf hleaf
  have hcomp := GM10.treeComponent_eq_singleton_of_isLeaf hT hadj hleaf
  have hτne : τ e₀ ≠ τ e₁ := fun he => hne (hbd.bijOn.injOn h₀.edge_mem h₁.edge_mem he)
  have hnr : ¬ (T.deleteEdges {s(τ e₀, w)}).Reachable (τ e₀) (τ e₁) := by
    intro hr
    have hm : τ e₁ ∈ GM10.treeComponent T (τ e₀) s(τ e₀, w) := hr
    rw [hcomp, Set.mem_singleton_iff] at hm
    exact hτne hm.symm
  have hsub : ({a, b} : Set α) ⊆
      {v ∈ V(G) | ∃ f₁ ∈ E(G), ∃ f₂ ∈ E(G),
        ¬ (T.deleteEdges {s(τ e₀, w)}).Reachable (τ f₁) (τ f₂) ∧ G.Inc f₁ v ∧ G.Inc f₂ v} := by
    rintro v (rfl | rfl)
    · exact ⟨h₀.left_mem, e₀, h₀.edge_mem, e₁, h₁.edge_mem, hnr, h₀.inc_left, h₁.inc_left⟩
    · exact ⟨h₀.right_mem, e₀, h₀.edge_mem, e₁, h₁.edge_mem, hnr, h₀.inc_right, h₁.inc_right⟩
  have horder : 2 ≤ graphBranchEdgeOrder G T τ s(τ e₀, w) := by
    rw [graphBranchEdgeOrder, ← Set.ncard_pair hab]
    exact Set.ncard_le_ncard hsub (hV.subset fun _ h => h.1)
  have hle : graphBranchEdgeOrder G T τ s(τ e₀, w) ≤ graphBranchDecompWidth G T τ := by
    apply le_csSup ((Set.toFinite T.edgeSet).image _).bddAbove
    exact ⟨s(τ e₀, w), T.mem_edgeSet.mpr hadj, rfl⟩
  exact horder.trans hle

private def parallelPair71 : MultiDigraph 2 where
  edgeMult u v := if u.1 == 0 && v.1 == 1 then 2 else 0

private theorem parallelPair71_edges : parallelPair71.numEdges = 2 := by decide

private theorem parallelPair71_not_width_one :
    ¬ GraphBranchWidthLE parallelPair71.toGMDigraph.toGraph 1 := by
  have h₀ : parallelPair71.toGMDigraph.toGraph.IsLink (0, 1, 0) 0 1 := by
    exact ⟨⟨by decide, by decide, by decide⟩, Or.inr ⟨rfl, rfl⟩⟩
  have h₁ : parallelPair71.toGMDigraph.toGraph.IsLink (0, 1, 1) 0 1 := by
    exact ⟨⟨by decide, by decide, by decide⟩, Or.inr ⟨rfl, rfl⟩⟩
  rintro (hsmall | ⟨ι, hfin, T, τ, hbd, hw⟩)
  · change parallelPair71.toGMDigraph.edgeSet.ncard ≤ 1 at hsmall
    rw [parallelPair71.ncard_edgeSet_toGMDigraph, parallelPair71_edges] at hsmall
    omega
  · have hh := two_le_width_of_parallel_edges71 (G := parallelPair71.toGMDigraph.toGraph)
      parallelPair71.isFinite_toGMDigraph.finite_V
      (by decide : (0 : ℕ) ≠ 1) (by decide : ((0, 1, 0) : ℕ × ℕ × ℕ) ≠ (0, 1, 1)) h₀ h₁ hbd
    omega

private theorem parallelPair71_no_wall {h : ℕ} (hh : 2 ≤ h) :
    ¬ HasDigraphModel (elemWallEdges h) parallelPair71 := by
  rintro ⟨M, hM⟩
  let f : Fin (elemWallNumVerts h) → Fin 2 := fun u => (hM.1 u).1.choose
  have hf : ∀ u, f u ∈ M.branchSet u := fun u => (hM.1 u).1.choose_spec
  have hinj : Function.Injective f := by
    intro u v heq
    by_contra hne
    exact Finset.disjoint_left.mp (hM.2.1 u v hne) (hf u) (heq.symm ▸ hf v)
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  rw [elemWallNumVerts_eq] at hcard
  have hlarge : 18 ≤ (h + 1) * (2 * h + 2) :=
    Nat.mul_le_mul (show 3 ≤ h + 1 by omega) (show 6 ≤ 2 * h + 2 by omega)
  omega

/-- The wall threshold in XIII (7.1), page 89, is automatically at least three.
The two-vertex graph with two parallel edges supplies the small-case test. -/
theorem three_le_wall_threshold71 {h k : ℕ} (hh : 2 ≤ h)
    (h71 : HasPlanarGridThreshold (elemWallEdges h) k) : 3 ≤ k := by
  by_contra hk
  have hk2 : k ≤ 2 := by omega
  have hhigh : HasBranchWidthGe parallelPair71 k := by
    refine ⟨by rw [parallelPair71_edges], ?_⟩
    intro B hB hdec
    exact parallelPair71_not_width_one
      (graphBranchWidthLE_mono_width (by omega) hdec.graphBranchWidthLE)
  exact parallelPair71_no_wall hh (h71 parallelPair71 hhigh)

end GraphMinor.Compute
