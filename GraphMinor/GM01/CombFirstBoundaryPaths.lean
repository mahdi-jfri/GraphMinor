module

public import GraphMinor.GM01.CombLayerBoundaries
public import GraphMinor.GM01.CombLayerBlockSets
import GraphMinor.GM01.RegionBoundaryPaths
import GraphMinor.GM01.CombPrefixRoot
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.ConnectedInducedSets
import GraphMinor.GM01.SubdivisionConnected

/-!
# Extending a comb attachment to its first boundary

Graph Minors I, (4.8), page 58, extends an attachment in `H` to `w_1`.
The late blocks are avoided inside a connected prefix, or in all of
`H` at the last layer. In layers zero and one the target is the root
and there are no early blocks. In later layers the target is the cut
just after the early prefix. A path to that cut stays in its later
region until its last vertex, so it avoids the early prefix as well.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The extension inside `H` used in GM01 (4.8), page 58, proved from
the actual subdivision and root path. The target may belong to the
early block set, so it alone is removed from the forbidden set. -/
theorem exists_comb_first_boundary_path {α β : Type*} {γ L n T ν : ℕ}
    (hL : 0 < L) (hν : 3 ≤ ν) (h2n : 2 * n ≤ L) (hn : n = ν * T + 1)
    (G : RootedGraph α β) {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb γ L).verts → α} (hc : Injective c)
    {P : (pathComb γ L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb γ L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c)
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c (rootedPathComb γ L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (i : Fin (T + 1)) (hbound : 2 * (ν * (i.val - 1)) ≤ L) {x : α}
    (hxH : x ∈ V(subgraphUnion G.graph N R))
    (hxAvoid : x ∉ layerLateBlocks (fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k) ν i.val ∪
      layerEarlyBlocks (fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k) ν i.val) :
    let H := subgraphUnion G.graph N R
    let S := fun k : Fin n ↦ combBlock hL H c k
    let w := firstLayerBoundary G c ν i.val (by omega) hbound
    ∃ Q : Graph α β, IsGraphPathWithEnds H Q x w ∧
      Disjoint V(Q) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}) := by
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let A := layerLateBlocks S ν i.val
  let B := layerEarlyBlocks S ν i.val
  let w := firstLayerBoundary G c ν i.val (by omega : 0 < ν) hbound
  change ∃ Q : Graph α β, IsGraphPathWithEnds H Q x w ∧ Disjoint V(Q) ((A ∪ B) \ {w})
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hreg := combSpineRegion_antitone hL hN hR.le hc hcentres hPN hE hRanges hInter hmeetR
  have hNconn := subdivision_connected (pathComb_connected (γ := γ) hL).coe
    (rootedPathComb γ L hL).root N c P hV (fun e ↦ by
      obtain ⟨a, b, he, hab, hP, _⟩ := hPaths e
      exact ⟨a, b, he, hab, hP⟩)
  have hHconn : GraphConnected H := graphConnected_subgraphUnion hN hR.le hNconn
    (graphConnected_of_isGraphPath hR) ⟨_, hcentres _, hR.right_mem⟩
  have hcentresH : ∀ v, c v ∈ V(H) := fun v ↦ Or.inl (hcentres v)
  have hpT : ν * (i.val - 1) ≤ ν * T := Nat.mul_le_mul_left ν (by omega)
  let p : Fin n := ⟨ν * (i.val - 1), by omega⟩
  have hB : B = combPrefix hL H c p.val :=
    layerEarlyBlocks_eq_combPrefix hL H c hreg ν i.val p rfl
  have hdata : GraphConnected (H.induce (V(H) \ A)) ∧
      G.root.val ∈ V(H) \ A ∧ combPrefix hL H c p.val ⊆ V(H) \ A := by
    by_cases hiT : i.val < T
    · have hmul := Nat.mul_le_mul_left ν (Nat.succ_le_of_lt hiT)
      change ν * (i.val + 1) ≤ ν * T at hmul
      have hpos : 0 < ν * (i.val + 1) := Nat.mul_pos (by omega) (by omega)
      let q : Fin n := ⟨ν * (i.val + 1) - 1, by omega⟩
      have hq : q.val + 1 = ν * (i.val + 1) := by dsimp [q]; omega
      have hA : A = combSpineRegion hL H c (2 * q.val) :=
        layerLateBlocks_eq_combSpineRegion hL H c hreg ν i.val q hq
      have hqpos : 0 < q.val := by
        have hm := Nat.mul_le_mul_left ν (Nat.succ_le_succ (Nat.zero_le i.val))
        change ν * 1 ≤ ν * (i.val + 1) at hm
        simp only [Nat.mul_one] at hm
        dsimp [q]
        omega
      have hqL : 2 * q.val < L := by have hqn := q.isLt; omega
      have hpq : p.val ≤ q.val := by
        have hm := Nat.mul_le_mul_left ν (Nat.sub_le i.val 1)
        rw [Nat.mul_add, Nat.mul_one] at hq
        change ν * (i.val - 1) ≤ q.val
        omega
      have hconn := (combPrefix_connected hL hHconn c hcentresH q.val hqpos hqL).1
      have hroot := root_mem_combPrefix hL hN hc hcentres hPN hE hRanges hInter
        G.root.val hR hmeetR q.val hqpos hqL
      rw [hA]
      refine ⟨hconn, hroot, ?_⟩
      intro z hz
      exact ⟨hz.1, fun h ↦ hz.2 (hreg (Nat.mul_le_mul_left 2 hpq) h)⟩
    · have hiEq : i.val = T := by omega
      have hlate : n < ν * (i.val + 1) := by
        rw [hiEq, Nat.mul_add, Nat.mul_one]
        omega
      have hA : A = ∅ := layerLateBlocks_eq_empty S hlate
      rw [hA, Set.sdiff_empty]
      exact ⟨graphConnected_induce_of_subgraph le_rfl hHconn,
        Or.inr hR.left_mem, fun _ hz ↦ hz.1⟩
  have hx : x ∈ V(H) \ A := ⟨hxH, fun h ↦ hxAvoid (Or.inl h)⟩
  by_cases hiSmall : i.val ≤ 1
  · have hw : w = G.root.val := by simp only [w, firstLayerBoundary, hiSmall, ↓reduceDIte]
    have hBempty : B = ∅ := layerEarlyBlocks_eq_empty S hiSmall
    have hle : H.induce (V(H) \ A) ≤ H := by
      refine ⟨fun _ h ↦ h.1, ?_⟩
      intro e a b he
      exact he.1
    obtain ⟨Q, hQ⟩ := exists_path_of_adj_reachable hx (hdata.1.2 x hx G.root.val hdata.2.1)
    refine ⟨Q, hw.symm ▸ hQ.mono hle, ?_⟩
    apply Set.disjoint_left.mpr
    intro z hz hzCut
    have hzA : z ∈ A := by simpa only [hBempty, Set.union_empty] using hzCut.1
    exact (hQ.le.vertexSet_mono hz).2 hzA
  · have hppos : 0 < p.val := Nat.mul_pos (by omega) (by omega)
    have hpL : 2 * p.val < L := by have hpn := p.isLt; omega
    let cut : α := c ⟨Sum.inl ⟨2 * p.val - 1, by omega⟩, pathComb_spine_mem γ L _⟩
    have hw : w = cut := by simp only [w, firstLayerBoundary, hiSmall, ↓reduceDIte]; rfl
    have hcutPrefix := (combPrefix_connected hL hHconn c hcentresH p.val hppos hpL).2
    have hcut : cut ∈ V(H) \ A := hdata.2.2 hcutPrefix
    let last : α := c ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩
    have hRegion : combSpineRegion hL H c (2 * p.val) = vertexAvoidanceRegion H last cut := by
      simp only [combSpineRegion, show 2 * p.val ≠ 0 by omega, hpL, ↓reduceIte, ↓reduceDIte]
      rfl
    have hxRegion : x ∈ vertexAvoidanceRegion H last cut := by
      rw [← hRegion]
      by_contra hnot
      have hxB : x ∈ B := by rw [hB]; exact ⟨hxH, hnot⟩
      exact hxAvoid (Or.inr hxB)
    obtain ⟨Q, hQ, hAvoid⟩ := exists_path_to_region_boundary_avoiding hdata.1 hx hcut hxRegion
    refine ⟨Q, hw.symm ▸ hQ, ?_⟩
    rw [hB, combPrefix, hRegion, hw]
    exact hAvoid

end GraphMinor.GM01
