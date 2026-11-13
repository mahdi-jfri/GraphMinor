module

public import GraphMinor.GM01.CombBlocks
import Lean.Elab.Tactic.Omega

/-!
# Identifying the final block with its subdivision region

The final block on page 55 of Graph Minors I retains the whole region
`R_{2n−2}`. Its cut is the zero-based spine position `2n−3`. Adjoining the
separate root path leaves that region unchanged. This identity connects
the last-block arm to the cut and path avoidance lemmas of the subdivision.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The actual last block of `H` is the avoidance region of its preceding
cut, computed in the subdivision alone. -/
theorem comb_lastBlock_eq_region {α β : Type*} {γ L n : ℕ}
    (hL : 0 < L) (hn : 2 ≤ n) (htail : 2 * n ≤ L)
    {G N R : Graph α β} (hN : N ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    {P : (pathComb γ L).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root}) :
    combBlock hL (subgraphUnion G N R) c (⟨n - 1, by omega⟩ : Fin n) =
      vertexAvoidanceRegion N
        (c ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩)
        (c ⟨Sum.inl ⟨2 * n - 3, by omega⟩, pathComb_spine_mem γ L _⟩) := by
  have hnlt : n - 1 < n := by omega
  have hnnot : ¬ n - 1 + 1 < n := by omega
  have hzero : 2 * (n - 1) ≠ 0 := by omega
  have hlong : 2 * (n - 1) < L := by omega
  simp only [combBlock, orderedRegionBlock, hnlt, hnnot, ↓reduceIte, sdiff_empty,
    combSpineRegion, hzero, hlong, ↓reduceDIte]
  have hindex : 2 * (n - 1) - 1 = 2 * n - 3 := by omega
  have hEq := comb_root_path_region_eq hN hR.le hc hPN hE hRanges hInter
    ⟨2 * n - 3, by omega⟩ ⟨L - 1, by omega⟩
    (by change 2 * n - 3 < L - 1; omega) (hcentres _) hmeet
  simpa only [hindex] using hEq

end GraphMinor.GM01
