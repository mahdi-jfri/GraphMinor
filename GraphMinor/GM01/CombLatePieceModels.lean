module

public import GraphMinor.GM01.CombLateSegmentRootPaths
import GraphMinor.GM01.CombSegmentRegionInclusions
import GraphMinor.GM01.RootedPathAttachment

/-!
# The old late comb piece rooted at the second boundary

Graph Minors I, (4.14), page 59, retains the old late comb after
omitting the two cells in its boundary block. The selected segment
has its proved rooted subdivision model. Transport its root along
the clean path from the boundary vertex, keeping the whole target
inside the late region.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The actual rooted old late piece used in the longer-comb
construction of GM01 (4.14), page 59. -/
theorem exists_rooted_comb_late_piece {α β : Type*} {γ L n m : ℕ}
    (hL : 0 < L) (h2n : 2 * n ≤ L) (hm : 0 < m)
    {G N R : Graph α β} (hN : N ≤ G)
    (c : (pathComb γ L).verts → α) (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb γ L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : Fin n) (hj : 0 < j.val) (hjnext : j.val + 1 < n)
    (hbound : 2 * (j.val + 1) + m ≤ L) {w : α}
    (hw : w ∈ combBlock hL (subgraphUnion G N R) c j) :
    ∃ K : RootedGraph α β, K.graph ≤ G ∧
      V(K.graph) ⊆ combSpineRegion hL (subgraphUnion G N R) c (2 * j.val) ∧
      K.root.val = w ∧ HasRootedMinor (rootedPathComb γ m hm) K := by
  let start := 2 * (j.val + 1)
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hOnly : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hP, hRange⟩ := hPaths e
    exact ⟨a, b, he, hP, hRange⟩
  have hInterV := fun e f hne ↦ (hInter e f hne).1
  obtain ⟨Q, hQ, hMeet, hQRegion⟩ := exists_path_from_block_to_late_segment hL h2n hm hN c hc P hV hE
    hPaths hInterV root hR hmeet j hj hjnext hbound hw
  let A := rootedCombSegment hm N c P start hbound
  obtain ⟨hAN, _, MA, _⟩ := combSegment_model hm c hc hcentres P hOnly hInter start hbound
  have hAG : A.graph ≤ G := hAN.trans hN
  have hMeetA : V(A.graph) ∩ V(Q) ⊆ {A.root.val} := by
    intro x hx
    exact hMeet ▸ ⟨hx.2, hx.1⟩
  let K : RootedGraph α β := ⟨subgraphUnion G A.graph Q, ⟨w, Or.inr hQ.left_mem⟩⟩
  have hKG : K.graph ≤ G := subgraphUnion_le hAG hQ.le
  have hARegion := combSegmentSupport_subset_combSpineRegion hL hN hR.le c hc hcentres P hE hOnly
    hInterV hmeet (2 * j.val) start (by omega) (by have := j.isLt; omega)
    (by dsimp [start]; omega) hbound
  have hKRegion : V(K.graph) ⊆ combSpineRegion hL (subgraphUnion G N R) c (2 * j.val) :=
    union_subset hARegion hQRegion
  exact ⟨K, hKG, hKRegion, rfl, ⟨MA.attachRootPath hAG w hQ hMeetA⟩⟩

end GraphMinor.GM01
