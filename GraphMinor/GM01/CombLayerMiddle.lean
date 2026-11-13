module

public import GraphMinor.GM01.CombLayerBlockSets
public import GraphMinor.GM01.CombRegionDifferences
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.PathCombTrees

/-!
# The connected part between the early and late blocks

The path extension in Graph Minors I, (4.11), page 58, takes place
inside `H` outside `A ∪ B`. For the first two layers this is a connected
prefix. For later layers it is a connected strip between two positive
cuts. In both cases it contains the cut centre immediately before the
late range, which is adjacent to `w_2`.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The part of `H` between the printed sets `A` and `B` is connected
and contains its late cut centre, as used in GM01 (4.11), page 58. -/
theorem comb_layer_middle_connected {α β : Type*} {γ L n T ν : ℕ}
    (hL : 0 < L) (hν : 3 ≤ ν) (h2n : 2 * n ≤ L) (hn : n = ν * T + 1)
    (G : RootedGraph α β) {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb γ L).verts → α} (hc : Injective c)
    {P : (pathComb γ L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb γ L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (i : Fin (T + 1)) (q : Fin n) (hq : q.val + 1 = ν * (i.val + 1)) :
    let H := subgraphUnion G.graph N R
    let S := fun k : Fin n ↦ combBlock hL H c k
    GraphConnected (H.induce (V(H) \ (layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val))) ∧
      c ⟨Sum.inl ⟨2 * q.val - 1, by omega⟩, pathComb_spine_mem γ L _⟩ ∈
        V(H) \ (layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) := by
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let A := layerLateBlocks S ν i.val
  let B := layerEarlyBlocks S ν i.val
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hP, _⟩ := hPaths e
    exact hP.le
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
  have hreg := combSpineRegion_antitone hL hN hR.le hc hcentres hPN hE hRanges hInter hmeet
  have hA : A = combSpineRegion hL H c (2 * q.val) :=
    layerLateBlocks_eq_combSpineRegion hL H c hreg ν i.val q hq
  have hqpos : 0 < q.val := by
    have hm := Nat.mul_le_mul_left ν (Nat.succ_le_succ (Nat.zero_le i.val))
    change ν * 1 ≤ ν * (i.val + 1) at hm
    simp only [Nat.mul_one] at hm
    omega
  have hqL : 2 * q.val < L := by omega
  change GraphConnected (H.induce (V(H) \ (A ∪ B))) ∧
    c ⟨Sum.inl ⟨2 * q.val - 1, by omega⟩, pathComb_spine_mem γ L _⟩ ∈ V(H) \ (A ∪ B)
  by_cases hiSmall : i.val ≤ 1
  · have hB : B = ∅ := layerEarlyBlocks_eq_empty S hiSmall
    rw [hB, Set.union_empty, hA]
    have hNconn := subdivision_connected (pathComb_connected (γ := γ) hL).coe
      (rootedPathComb γ L hL).root N c P hV (fun e ↦ by
        obtain ⟨a, b, he, hab, hP, _⟩ := hPaths e
        exact ⟨a, b, he, hab, hP⟩)
    have hHconn : GraphConnected H := graphConnected_subgraphUnion hN hR.le hNconn
      (graphConnected_of_isGraphPath hR) ⟨_, hcentres _, hR.right_mem⟩
    exact combPrefix_connected hL hHconn c (fun v ↦ Or.inl (hcentres v)) q.val hqpos hqL
  · have hpT : ν * (i.val - 1) ≤ ν * T := Nat.mul_le_mul_left ν (by omega)
    let p : Fin n := ⟨ν * (i.val - 1), by omega⟩
    have hB : B = combPrefix hL H c p.val := layerEarlyBlocks_eq_combPrefix hL H c hreg ν i.val p rfl
    have hp : 0 < p.val := Nat.mul_pos (by omega) (by omega)
    have hpq : p.val < q.val := by
      have hm := Nat.mul_le_mul_left ν (Nat.sub_le i.val 1)
      rw [Nat.mul_add, Nat.mul_one] at hq
      change ν * (i.val - 1) < q.val
      omega
    have hSet : V(H) \ (A ∪ B) = combSpineRegion hL H c (2 * p.val) \ combSpineRegion hL H c (2 * q.val) := by
      rw [hA, hB]
      ext x
      constructor
      · intro hx
        have hxP : x ∈ combSpineRegion hL H c (2 * p.val) := by
          by_contra hnot
          exact hx.2 (Or.inr ⟨hx.1, hnot⟩)
        exact ⟨hxP, fun h ↦ hx.2 (Or.inl h)⟩
      · intro hx
        refine ⟨combSpineRegion_subset hL H c _ hx.1, ?_⟩
        rintro (h | h)
        · exact hx.2 h
        · exact h.2 hx.1
    rw [hSet]
    exact combSpineRegion_diff_connected hL hN hR.le hc hcentres P hE hOnly hInter hmeet
      (2 * p.val) (2 * q.val) (by omega) (by omega) hqL

end GraphMinor.GM01
