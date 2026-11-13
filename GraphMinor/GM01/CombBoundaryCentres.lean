module

public import GraphMinor.GM01.CombBlocks
public import GraphMinor.GM01.CombRegionFormulas
import GraphMinor.GM01.CombLaterRegions

/-!
# The cut centre belongs to the block before a boundary

For the vertex `w_2` defined before Graph Minors I, (4.11), page 58,
the adjacent earlier vertex is the spine cut centre. That centre is
outside its own later region and lies in the previous region, since
it is later than the previous cut. Hence it belongs to the preceding
block of the actual subdivided comb.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The spine cut centre immediately before a block in the page-55
partition of Graph Minors I. Block indices start at zero. -/
@[expose] def combBlockCutCentre {α : Type*} {γ L n : ℕ} (hL : 0 < L) (h2n : 2 * n ≤ L)
    (c : (pathComb γ L).verts → α) (k : Fin n) : α :=
  c ⟨Sum.inl ⟨2 * k.val - 1, by omega⟩, pathComb_spine_mem γ L _⟩

/-- The earlier end of the boundary edge lies in the preceding block,
as required by the definition of `w_2` before GM01 (4.11), page 58. -/
theorem comb_cut_centre_mem_preceding_block {α β : Type*} {γ L n : ℕ}
    (hL : 0 < L) (h2n : 2 * n ≤ L) {G N R : Graph α β} (hN : N ≤ G) (hR : R ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (k : Fin n) (hk : 2 ≤ k.val) :
    c ⟨Sum.inl ⟨2 * k.val - 1, by omega⟩, pathComb_spine_mem γ L _⟩ ∈
      combBlock hL (subgraphUnion G N R) c (⟨k.val - 1, by omega⟩ : Fin n) := by
  let H := subgraphUnion G N R
  let p : Fin n := ⟨k.val - 1, by omega⟩
  let cut : Fin L := ⟨2 * k.val - 1, by omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hp : 0 < p.val := by dsimp [p]; omega
  have hpL : 2 * p.val < L := by have hkn := k.isLt; dsimp [p]; omega
  have hkL : 2 * k.val < L := by have hkn := k.isLt; omega
  have hcutPrev : c ⟨Sum.inl cut, pathComb_spine_mem γ L cut⟩ ∈
      combSpineRegion hL H c (2 * p.val) := by
    rw [combSpineRegion_union_eq_subdivision_region hL hN hR hc hcentres hPN hE hRanges hInter hmeet
      (2 * p.val) (by omega) hpL]
    exact comb_subdivision_later_mem_region hc hcentres hPaths ⟨2 * p.val - 1, by omega⟩ cut last
      (by dsimp [cut, p]; omega) (by dsimp [cut, last]; omega)
  have hcutNot : c ⟨Sum.inl cut, pathComb_spine_mem γ L cut⟩ ∉
      combSpineRegion hL H c (2 * k.val) := by
    rw [combSpineRegion_eq_avoidance hL H c (2 * k.val) (by omega) hkL]
    intro h
    exact (vertexAvoidanceRegion_subset H _ _ h).2 rfl
  have hpnext : p.val + 1 < n := by have hkn := k.isLt; dsimp [p]; omega
  change _ ∈ orderedRegionBlock (fun t ↦ if t < n then combSpineRegion hL H c (2 * t) else ∅) p
  simp only [orderedRegionBlock, p.isLt, hpnext, ↓reduceIte]
  refine ⟨hcutPrev, ?_⟩
  have heq : 2 * (p.val + 1) = 2 * k.val := by dsimp [p]; omega
  rw [heq]
  exact hcutNot

end GraphMinor.GM01
