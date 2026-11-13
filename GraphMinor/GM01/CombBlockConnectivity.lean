module

public import GraphMinor.GM01.CombBlocks
import GraphMinor.GM01.CombLaterRegions
import GraphMinor.GM01.RegionDifferences
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.PathCombTrees
import Lean.Elab.Tactic.Omega

/-!
# Connectivity of the comb blocks

Graph Minors I, page 55, asserts that each induced block `B_j = H | S_j`
is connected. The first block is the complement of an avoidance region,
the middle blocks are differences of two regions, and the last block is
a whole region. Later cut centres belong to earlier regions, so the
proved connectivity lemmas apply in each case. Connectivity of `H` is
derived from the replacing paths and the separate root path.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- Every induced block in the page-55 decomposition is connected. The
bound `2n ≤ δ` ensures that all block boundaries precede the last spine
vertex; the numerical choice in the paper gives an even larger tail. -/
theorem combBlock_connected {α β : Type*} {γ δ n : ℕ} (hδ : 0 < δ) (htail : 2 * n ≤ δ)
    {G N R : Graph α β} (hN : N ≤ G)
    {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    {P : (pathComb γ δ).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb γ δ).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ δ).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c)
    (hE : E(N) = ⋃ e, E(P e)) (root : α)
    (hRootPath : IsGraphPathWithEnds G R root (c (rootedPathComb γ δ hδ).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ δ hδ).root})
    (k : Fin n) :
    GraphConnected ((subgraphUnion G N R).induce
      (combBlock hδ (subgraphUnion G N R) c k)) := by
  let H := subgraphUnion G N R
  let spine (i : Fin δ) : (pathComb γ δ).verts :=
    ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩
  let last : Fin δ := ⟨δ - 1, by omega⟩
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hPathOnly : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hP, hRange⟩ := hPaths e
    exact ⟨a, b, he, hP, hRange⟩
  have hNconn := subdivision_connected (pathComb_connected (γ := γ) hδ).coe
    (rootedPathComb γ δ hδ).root N c P hV (fun e ↦ by
      obtain ⟨a, b, he, hab, hP, _⟩ := hPaths e
      exact ⟨a, b, he, hab, hP⟩)
  have hHconn : GraphConnected H := graphConnected_subgraphUnion hN hRootPath.le hNconn
    (graphConnected_of_isGraphPath hRootPath)
    ⟨_, hcentres _, hRootPath.right_mem⟩
  have hcentresH : ∀ v, c v ∈ V(H) := fun v ↦ Or.inl (hcentres v)
  have hneCut : ∀ q : Fin δ, q.val < δ - 1 → c (spine last) ≠ c (spine q) := by
    intro q hq heq
    have hval := congrArg (fun v : (pathComb γ δ).verts ↦
      (pathCombSpineIndex v.val).val) (hc heq)
    change δ - 1 = q.val at hval
    omega
  have hregion : ∀ m, 0 < m → m < δ →
      GraphConnected (H.induce (combSpineRegion hδ H c m)) := by
    intro m hm hmd
    have hmne : m ≠ 0 := Nat.ne_of_gt hm
    simp only [combSpineRegion, hmne, ↓reduceIte, hmd, ↓reduceDIte]
    exact vertexAvoidanceRegion_connected (hcentresH (spine last))
      (hneCut ⟨m - 1, by omega⟩ (by change m - 1 < δ - 1; omega))
  have hcompl : ∀ m, 0 < m → m < δ →
      GraphConnected (H.induce (V(H) \ combSpineRegion hδ H c m)) := by
    intro m hm hmd
    have hmne : m ≠ 0 := Nat.ne_of_gt hm
    simp only [combSpineRegion, hmne, ↓reduceIte, hmd, ↓reduceDIte]
    exact vertexAvoidanceRegion_compl_connected hHconn _ _ (hcentresH _)
  have hdiff : ∀ a b, 0 < a → a < b → b < δ →
      GraphConnected (H.induce
        (combSpineRegion hδ H c a \ combSpineRegion hδ H c b)) := by
    intro a b ha hab hbd
    have hane : a ≠ 0 := Nat.ne_of_gt ha
    have hbne : b ≠ 0 := by omega
    have had : a < δ := by omega
    simp only [combSpineRegion, hane, hbne, ↓reduceIte, had, hbd, ↓reduceDIte]
    apply vertexAvoidanceRegion_diff_connected (hcentresH (spine last))
      (hneCut ⟨a - 1, by omega⟩ (by change a - 1 < δ - 1; omega))
    rw [comb_root_path_region_eq hN hRootPath.le hc hPN hE hRanges hInter
      ⟨a - 1, by omega⟩ last (by change a - 1 < δ - 1; omega) (hcentres _) hmeet]
    exact comb_subdivision_later_mem_region hc hcentres hPathOnly
      ⟨a - 1, by omega⟩ ⟨b - 1, by omega⟩ last
      (by change a - 1 < b - 1; omega) (by change b - 1 ≤ δ - 1; omega)
  have hk : k.val < n := k.isLt
  change GraphConnected (H.induce (combBlock hδ H c k))
  unfold combBlock orderedRegionBlock
  by_cases hnext : k.val + 1 < n
  · simp only [hk, hnext, ↓reduceIte]
    by_cases hk0 : k.val = 0
    · rw [hk0, Nat.mul_zero, combSpineRegion_zero]
      exact hcompl 2 (by omega) (by omega)
    · exact hdiff (2 * k.val) (2 * (k.val + 1)) (by omega) (by omega) (by omega)
  · simp only [hk, hnext, ↓reduceIte, sdiff_empty]
    by_cases hk0 : k.val = 0
    · rw [hk0, Nat.mul_zero, combSpineRegion_zero]
      simpa only [Graph.induce_vertexSet] using hHconn
    · exact hregion (2 * k.val) (by omega) (by omega)

end GraphMinor.GM01
