module

public import GraphMinor.GM01.CombSegmentModels
public import GraphMinor.GM01.CombBlocks
import GraphMinor.GM01.CombSegmentRegionInclusions
import GraphMinor.GM01.CombBlockConnectivity
import GraphMinor.GM01.CombBoundaryCentres
import GraphMinor.GM01.CombPrefixes
import GraphMinor.GM01.SelectedBoundaryPath
import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM01.SubdivisionConnected

/-!
# Rooting the retained late segment from its preceding block

Graph Minors I, (4.14), page 59, joins the middle subdivision to the
old late piece at `w_2`. Keep the cells after its block. Within the
connected boundary block, join `w_2` to the last spine centre, then
follow the next replacing path. This union meets the retained segment
only at its first centre. All its vertices stay in the late region,
so the root can be transported along the resulting clean path.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The clean path rooting the old late segment at `w_2` in GM01
(4.14), page 59. The two cells of its boundary block are omitted. -/
theorem exists_path_from_block_to_late_segment {α β : Type*} {γ L n m : ℕ}
    (hL : 0 < L) (h2n : 2 * n ≤ L) (hm : 0 < m)
    {G N R : Graph α β} (hN : N ≤ G)
    (c : (pathComb γ L).verts → α) (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb γ L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : Fin n) (hj : 0 < j.val) (hjnext : j.val + 1 < n)
    (hbound : 2 * (j.val + 1) + m ≤ L) {w : α}
    (hw : w ∈ combBlock hL (subgraphUnion G N R) c j) :
    let S := combSegmentSupport c P (2 * (j.val + 1)) hbound
    let t := (rootedCombSegment hm N c P (2 * (j.val + 1)) hbound).root.val
    ∃ Q : Graph α β, IsGraphPathWithEnds G Q w t ∧ V(Q) ∩ S = {t} ∧
      V(Q) ⊆ combSpineRegion hL (subgraphUnion G N R) c (2 * j.val) := by
  let H := subgraphUnion G N R
  let start := 2 * (j.val + 1)
  let f := combShiftEmbedding (γ := γ) start hbound
  let hf := fun {a b} (h : (pathComb γ m).coe.Adj a b) ↦ combShiftEmbedding_adj start hbound h
  let r := (rootedPathComb γ m hm).root
  let a : (pathComb γ L).verts := ⟨Sum.inl ⟨start - 1, by dsimp [start]; omega⟩, pathComb_spine_mem γ L _⟩
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hOnly : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hP, hRange⟩ := hPaths e
    exact ⟨a, b, he, hP, hRange⟩
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hOnly e
    exact ⟨a, b, he, hRange⟩
  let k : Fin n := ⟨j.val + 1, hjnext⟩
  have haBlock := comb_cut_centre_mem_preceding_block hL h2n hN hR.le hc hcentres P hE hOnly
    hInter hmeet k (by dsimp [k]; omega)
  have hprev : (⟨k.val - 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp [k])
  rw [hprev] at haBlock
  have haB : c a ∈ combBlock hL H c j := haBlock
  have hadj : (pathComb γ L).coe.Adj a (f r) := by
    apply pathComb_spine_adj (γ := γ)
    apply pathGraph_adj.mpr
    exact Or.inl (by change start - 1 + 1 = start + 0; dsimp [start]; omega)
  let e : (pathComb γ L).coe.edgeSet := ⟨s(a,f r), hadj⟩
  obtain ⟨u, v, he, hP, _⟩ := hOnly e
  have hPair : s(a,f r) = s(u,v) := he
  have hBoundary : IsGraphPathWithEnds N (P e) (c a) (c (f r)) := by
    rcases Sym2.eq_iff.mp hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hP
    · exact hP.symm
  have haOutside : a ∉ range f := by
    intro ha
    have h := (mem_range_combShiftEmbedding_iff start hbound a).mp ha
    change start ≤ start - 1 ∧ start - 1 < start + m at h
    dsimp [start] at h
    omega
  have hMeet := selected_subdivision_boundary_intersection f hf hc P hRanges hInter r a haOutside e rfl
  have hTailRegion := combSegmentSupport_subset_combSpineRegion hL hN hR.le c hc hcentres P hE hOnly
    hInter hmeet start start (by dsimp [start]; omega) (by omega) le_rfl hbound
  have hBlockDisj : Disjoint (combBlock hL H c j) (combSegmentSupport c P start hbound) := by
    apply Set.disjoint_left.mpr
    intro x hxB hxS
    have hxNot : x ∉ combSpineRegion hL H c start := by
      simpa only [combBlock, orderedRegionBlock, j.isLt, hjnext, ↓reduceIte] using hxB.2
    exact hxNot (hTailRegion hxS)
  have hBoundarySupport := path_subset_combSegmentSupport c P (start - 1)
    (by omega : start - 1 + 2 ≤ L) e rfl
    ⟨le_refl _, by change start - 1 < start - 1 + 2; omega⟩
    ⟨by change start - 1 ≤ start + 0; omega, by change start + 0 < start - 1 + 2; dsimp [start]; omega⟩
  have hBoundaryLow := hBoundarySupport.trans
    (combSegmentSupport_subset_combSpineRegion hL hN hR.le c hc hcentres P hE hOnly hInter hmeet
      (2 * j.val) (start - 1) (by omega) (by have := j.isLt; omega)
      (by dsimp [start]; omega) (by omega : start - 1 + 2 ≤ L))
  have hHG : H ≤ G := subgraphUnion_le hN hR.le
  have hBlockG : H.induce (combBlock hL H c j) ≤ G :=
    (H.induce_le (combBlock_subset_graph hL H c j)).trans hHG
  have hBlockConn := combBlock_connected hL h2n hN hc hV hPaths hInter hE root hR hmeet j
  let K := subgraphUnion G (H.induce (combBlock hL H c j)) (P e)
  have hKconn : GraphConnected K := graphConnected_subgraphUnion hBlockG (hBoundary.le.trans hN)
    hBlockConn (graphConnected_of_isGraphPath (hBoundary.mono hN)) ⟨c a, haB, hBoundary.left_mem⟩
  have hwK : w ∈ V(K) := Or.inl hw
  have htK : c (f r) ∈ V(K) := Or.inr hBoundary.right_mem
  obtain ⟨Q, hQ⟩ := exists_path_of_adj_reachable hwK (hKconn.2 w hwK (c (f r)) htK)
  have hKG : K ≤ G := subgraphUnion_le hBlockG (hBoundary.le.trans hN)
  refine ⟨Q, hQ.mono hKG, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      rcases hQ.le.vertexSet_mono hx.1 with hxB | hxP
      · exact False.elim (Set.disjoint_left.mp hBlockDisj hxB hx.2)
      · exact hMeet ▸ ⟨hxP, hx.2⟩
    · intro x hx
      have hxt : x = c (f r) := hx
      subst x
      exact ⟨hQ.right_mem, Or.inl (mem_range_self r)⟩
  · intro x hx
    rcases hQ.le.vertexSet_mono hx with hxB | hxP
    · simpa only [combBlock, orderedRegionBlock, j.isLt, ↓reduceIte] using hxB.1
    · exact hBoundaryLow hxP

end GraphMinor.GM01
