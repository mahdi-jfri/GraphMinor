module

public import GraphMinor.GM01.CombPrefixes
import Lean.Elab.Tactic.Omega

/-!
# The ambient root belongs to the initial piece

For the contraction in Graph Minors I, (4.1), page 55, the initial piece
must contain the ambient root. The separate root path meets the
subdivided comb only at its first centre. That centre is outside the
later avoidance region, and adjoining the root path leaves the region
unchanged. Hence the ambient root is in its complementary initial piece.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The whole separate root path lies in each positive initial piece,
as used to retain the rooted prefix in GM01 (4.10), page 58. -/
theorem root_path_subset_combPrefix {α β : Type*} {γ L : ℕ} (hL : 0 < L)
    {G N R : Graph α β} (hN : N ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    {P : (pathComb γ L).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : ℕ) (hj : 0 < j) (hjL : 2 * j < L) :
    V(R) ⊆ combPrefix hL (subgraphUnion G N R) c j := by
  let cut : Fin L := ⟨2 * j - 1, by omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  have hcut : cut.val < last.val := by dsimp [cut, last]; omega
  have hRootNot : c (rootedPathComb γ L hL).root ∉ vertexAvoidanceRegion N
      (c ⟨Sum.inl last, pathComb_spine_mem γ L last⟩)
      (c ⟨Sum.inl cut, pathComb_spine_mem γ L cut⟩) :=
    comb_subdivision_earlier_not_mem_region hc hPN hE hRanges hInter cut ⟨0, hL⟩ last
      (by change 0 < 2 * j - 1; omega) hcut
  have hRegionEq := comb_root_path_region_eq hN hR.le hc hPN hE hRanges hInter cut last hcut
    (hcentres _) hmeet
  intro x hxR
  refine ⟨Or.inr hxR, ?_⟩
  have hj0 : 2 * j ≠ 0 := by omega
  simp only [combSpineRegion, hj0, ↓reduceIte, hjL, ↓reduceDIte]
  rw [hRegionEq]
  intro hx
  have hxN := (vertexAvoidanceRegion_subset N _ _ hx).1
  have hrootEq : x = c (rootedPathComb γ L hL).root := hmeet ⟨hxN, hxR⟩
  exact hRootNot (hrootEq ▸ hx)

/-- The connected prefix before a skipped block contains the ambient
root used by the fork contraction in GM01 (4.1). -/
theorem root_mem_combPrefix {α β : Type*} {γ L : ℕ} (hL : 0 < L)
    {G N R : Graph α β} (hN : N ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    {P : (pathComb γ L).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : ℕ) (hj : 0 < j) (hjL : 2 * j < L) :
    root ∈ combPrefix hL (subgraphUnion G N R) c j := by
  exact root_path_subset_combPrefix hL hN hc hcentres hPN hE hRanges hInter
    root hR hmeet j hj hjL hR.left_mem

end GraphMinor.GM01
