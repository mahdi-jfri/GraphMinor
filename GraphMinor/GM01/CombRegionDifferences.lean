module

public import GraphMinor.GM01.CombRegionFormulas
import GraphMinor.GM01.RegionDifferences
import GraphMinor.GM01.CombLaterRegions

/-!
# Connected strips between two comb cuts

The extension to `w_2` in Graph Minors I, (4.11), page 58, follows the
part of `H` between its early and late block ranges. With a positive
early cut this is a difference of two avoidance regions. The later
cut centre lies in the earlier region and is excluded from its own
region. The proved region-difference lemma gives connectivity of the
strip and places that later cut centre in it.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- A strip between positive interior comb cuts is connected and
contains its later cut centre, for GM01 (4.11), page 58. -/
theorem combSpineRegion_diff_connected {α β : Type*} {γ L : ℕ}
    (hL : 0 < L) {G N R : Graph α β} (hN : N ≤ G) (hR : R ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (a b : ℕ) (ha : 0 < a) (hab : a < b) (hbL : b < L) :
    GraphConnected ((subgraphUnion G N R).induce
      (combSpineRegion hL (subgraphUnion G N R) c a \ combSpineRegion hL (subgraphUnion G N R) c b)) ∧
    c ⟨Sum.inl ⟨b - 1, by omega⟩, pathComb_spine_mem γ L _⟩ ∈
      combSpineRegion hL (subgraphUnion G N R) c a \ combSpineRegion hL (subgraphUnion G N R) c b := by
  let H := subgraphUnion G N R
  let last : Fin L := ⟨L - 1, by omega⟩
  let low : Fin L := ⟨a - 1, by omega⟩
  let high : Fin L := ⟨b - 1, by omega⟩
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ u v, e.val = s(u,v) ∧
      V(P e) ∩ range c = {c u,c v} := by
    intro e
    obtain ⟨u, v, he, _, hRange⟩ := hPaths e
    exact ⟨u, v, he, hRange⟩
  have hA := combSpineRegion_eq_avoidance hL H c a ha (hab.trans hbL)
  have hB := combSpineRegion_eq_avoidance hL H c b (by omega) hbL
  have hAN := combSpineRegion_union_eq_subdivision_region hL hN hR hc hcentres hPN hE hRanges hInter hmeet
    a ha (hab.trans hbL)
  have hHigh : c ⟨Sum.inl high, pathComb_spine_mem γ L high⟩ ∈ combSpineRegion hL H c a := by
    rw [hAN]
    exact comb_subdivision_later_mem_region hc hcentres hPaths low high last
      (by dsimp [low, high]; omega) (by dsimp [high, last]; omega)
  have hHighNot : c ⟨Sum.inl high, pathComb_spine_mem γ L high⟩ ∉ combSpineRegion hL H c b := by
    rw [hB]
    intro h
    exact (vertexAvoidanceRegion_subset H _ _ h).2 rfl
  have hne : c ⟨Sum.inl last, pathComb_spine_mem γ L last⟩ ≠ c ⟨Sum.inl low, pathComb_spine_mem γ L low⟩ := by
    intro heq
    have h := congrArg (fun v : (pathComb γ L).verts ↦ (pathCombSpineIndex v.val).val) (hc heq)
    change last.val = low.val at h
    dsimp [last, low] at h
    omega
  refine ⟨?_, hHigh, hHighNot⟩
  rw [hA, hB]
  exact vertexAvoidanceRegion_diff_connected (Or.inl (hcentres _)) hne (hA ▸ hHigh)

end GraphMinor.GM01
