module

public import GraphMinor.GM01.CombSegmentsInRegions
public import GraphMinor.GM01.CombRegionFormulas

/-!
# Selected intervals in the regions of the rooted comb

The late piece in Graph Minors I, (4.14), page 59, is represented in
`H`, the subdivision with its separate root path. The root path does
not change a positive interior region. The selected-interval inclusion
in the subdivision therefore also places that interval in the
corresponding region of `H`.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- A represented cell interval at or beyond a positive cut lies in
the corresponding `H` region, for GM01 (4.14), page 59. -/
theorem combSegmentSupport_subset_combSpineRegion {α β : Type*} {γ L m : ℕ}
    (hL : 0 < L) {G N R : Graph α β} (hN : N ≤ G) (hR : R ≤ G)
    (c : (pathComb γ L).verts → α) (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j offset : ℕ) (hj : 0 < j) (hjL : j < L) (hjo : j ≤ offset)
    (hbound : offset + m ≤ L) :
    combSegmentSupport c P offset hbound ⊆ combSpineRegion hL (subgraphUnion G N R) c j := by
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  rw [combSpineRegion_union_eq_subdivision_region hL hN hR hc hcentres hPN hE hRanges hInter hmeet j hj hjL]
  exact combSegmentSupport_subset_later_region c hc hcentres P hPaths
    ⟨j - 1, by omega⟩ offset (by change j - 1 < offset; omega) hbound

end GraphMinor.GM01
