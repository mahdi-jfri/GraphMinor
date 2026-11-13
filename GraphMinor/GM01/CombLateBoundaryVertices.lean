module

public import GraphMinor.GM01.CombBoundaryCentres
import GraphMinor.GM01.PathLastEdgeCover
import GraphMinor.GM01.CombLaterRegions
import GraphMinor.GM01.PathsInRegions
import GraphMinor.GM01.CombPathsOutside

/-!
# The vertex on the late side of a block boundary

Before Graph Minors I, (4.11), page 58, `w_2` is the vertex in the late
block adjacent to the preceding block. If a spine edge is subdivided,
this need not be a source centre. Take the first neighbor of the cut
centre on its replacing path. The remaining path joins it to the next
centre while avoiding the cut, so it lies in the late region. The
whole replacing path avoids the following region, placing that neighbor
in the specified block.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The actual late boundary vertex defined before GM01 (4.11),
page 58. It may be internal to a replacing path. -/
theorem exists_comb_late_boundary_vertex {α β : Type*} {γ L n : ℕ}
    (hL : 0 < L) (h2n : 2 * n ≤ L) {G N R : Graph α β} (hN : N ≤ G) (hR : R ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (k : Fin n) (hk : 2 ≤ k.val) (hknext : k.val + 1 < n) :
    ∃ w ∈ combBlock hL (subgraphUnion G N R) c k,
      (subgraphUnion G N R).Adj
        (c ⟨Sum.inl ⟨2 * k.val - 1, by omega⟩, pathComb_spine_mem γ L _⟩) w := by
  let H := subgraphUnion G N R
  let low : Fin L := ⟨2 * k.val - 1, by omega⟩
  let next : Fin L := ⟨2 * k.val, by omega⟩
  let high : Fin L := ⟨2 * (k.val + 1) - 1, by omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  let u : (pathComb γ L).verts := ⟨Sum.inl low, pathComb_spine_mem γ L low⟩
  let v : (pathComb γ L).verts := ⟨Sum.inl next, pathComb_spine_mem γ L next⟩
  have huv : (pathComb γ L).coe.Adj u v := by
    apply pathComb_spine_adj (γ := γ)
    apply pathGraph_adj.mpr
    exact Or.inl (by change 2 * k.val - 1 + 1 = 2 * k.val; omega)
  let e : (pathComb γ L).coe.edgeSet := ⟨s(u,v), huv⟩
  obtain ⟨u', v', he, hP, _⟩ := hPaths e
  have hPair : s(u,v) = s(u',v') := he
  have hPath : IsGraphPathWithEnds N (P e) (c u) (c v) := by
    rcases Sym2.eq_iff.mp hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hP
    · exact hP.symm
  obtain ⟨ℓ, w, Q, hlink, hQP, hQ, hNot, _⟩ := exists_last_edge_with_vertex_cover hPath.symm
    (fun h ↦ huv.ne (hc h.symm))
  have hvRegion : c v ∈ vertexAvoidanceRegion N (c ⟨Sum.inl last, pathComb_spine_mem γ L last⟩) (c u) :=
    comb_subdivision_later_mem_region hc hcentres hPaths low next last
      (by dsimp [low, next]; omega) (by dsimp [next, last]; omega)
  have hwRegion := path_subset_vertexAvoidanceRegion hQ hvRegion hNot hQ.right_mem
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hEnds : ∀ z ∈ e.val, (pathCombSpineIndex z.val).val ≤ high.val := by
    intro z hz
    change z ∈ s(u,v) at hz
    rcases Sym2.mem_iff.mp hz with rfl | hz
    · change low.val ≤ high.val
      dsimp [low, high]
      omega
    · have hzv : z = v := hz
      subst z
      change next.val ≤ high.val
      dsimp [next, high]
      omega
  have hDisHigh := comb_subdivision_path_disjoint_later_region hc hPN hE hRanges hInter high
    (by dsimp [high, last]; omega) e hEnds
  have hLowEq := combSpineRegion_union_eq_subdivision_region hL hN hR hc hcentres hPN hE hRanges hInter hmeet
    (2 * k.val) (by omega) (by omega)
  have hHighEq := combSpineRegion_union_eq_subdivision_region hL hN hR hc hcentres hPN hE hRanges hInter hmeet
    (2 * (k.val + 1)) (by omega) (by omega)
  have hwBlock : w ∈ combBlock hL H c k := by
    change w ∈ orderedRegionBlock (fun t ↦ if t < n then combSpineRegion hL H c (2 * t) else ∅) k
    simp only [orderedRegionBlock, k.isLt, hknext, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [hLowEq]
      exact hwRegion
    · rw [hHighEq]
      exact fun h ↦ Set.disjoint_left.mp hDisHigh (hQP.vertexSet_mono hQ.right_mem) h
  exact ⟨w, hwBlock, ℓ, ((hlink.mono (hPN e)).mono (le_subgraphUnion_left hN hR)).symm⟩

end GraphMinor.GM01
