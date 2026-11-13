module

public import GraphMinor.GM01.CombRegions

/-!
# Formulas for the interior comb regions

The boundary constructions of Graph Minors I, (4.8) and (4.11), page 58,
use the regions with positive indices before the end of the spine.
Such a region is exactly reachability from the last centre after its
cut centre is deleted. The separate root path does not change it,
by the proved root-path invariance of the subdivision regions.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- A positive interior region is the avoidance region of its cut. -/
theorem combSpineRegion_eq_avoidance {α β : Type*} {γ L : ℕ} (hL : 0 < L)
    (H : Graph α β) (c : (pathComb γ L).verts → α) (j : ℕ) (hj : 0 < j) (hjL : j < L) :
    combSpineRegion hL H c j = vertexAvoidanceRegion H
      (c ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩)
      (c ⟨Sum.inl ⟨j - 1, by omega⟩, pathComb_spine_mem γ L _⟩) := by
  simp only [combSpineRegion, show j ≠ 0 by omega, hjL, ↓reduceIte, ↓reduceDIte]

/-- An interior region can be computed in the subdivided comb alone,
since its separate root path attaches before the cut. -/
theorem combSpineRegion_union_eq_subdivision_region {α β : Type*} {γ L : ℕ} (hL : 0 < L)
    {G N R : Graph α β} (hN : N ≤ G) (hR : R ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    {P : (pathComb γ L).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : ℕ) (hj : 0 < j) (hjL : j < L) :
    combSpineRegion hL (subgraphUnion G N R) c j = vertexAvoidanceRegion N
      (c ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩)
      (c ⟨Sum.inl ⟨j - 1, by omega⟩, pathComb_spine_mem γ L _⟩) := by
  rw [combSpineRegion_eq_avoidance hL _ c j hj hjL]
  exact comb_root_path_region_eq hN hR hc hPN hE hRanges hInter
    ⟨j - 1, by omega⟩ ⟨L - 1, by omega⟩ (by change j - 1 < L - 1; omega) (hcentres _) hmeet

end GraphMinor.GM01
