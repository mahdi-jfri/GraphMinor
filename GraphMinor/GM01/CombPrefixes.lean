module

public import GraphMinor.GM01.CombBlocks
import GraphMinor.GM01.RegionDifferences
import Lean.Elab.Tactic.Omega

/-!
# The initial piece before a skipped block

The root piece contracted in Graph Minors I, (4.1), page 55, starts with
the graph before the skipped block. It is the complement of the boundary
region `R_{2j}`. This complement is connected and contains the preceding
cut centre. Earlier blocks lie in it, while the skipped block and all
later blocks are disjoint from it. These set facts identify the initial
piece used for the two attachment paths.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The vertices before block `j`, namely the complement of `R_{2j}`
in the page-55 comb graph. -/
def combPrefix {α β : Type*} {γ L : ℕ} (hL : 0 < L) (H : Graph α β)
    (c : (pathComb γ L).verts → α) (j : ℕ) : Set α :=
  V(H) \ combSpineRegion hL H c (2 * j)

/-- Every block lies in its initial boundary region and in the graph. -/
theorem combBlock_subset_graph {α β : Type*} {γ L n : ℕ} (hL : 0 < L)
    (H : Graph α β) (c : (pathComb γ L).verts → α) (i : Fin n) :
    combBlock hL H c i ⊆ V(H) := by
  intro x hx
  have hxR : x ∈ combSpineRegion hL H c (2 * i.val) := by
    have hi := i.isLt
    simpa only [combBlock, orderedRegionBlock, hi, ↓reduceIte] using hx.1
  exact combSpineRegion_subset hL H c _ hxR

/-- The initial piece is connected and contains the cut centre just
before the skipped block. -/
theorem combPrefix_connected {α β : Type*} {γ L : ℕ} (hL : 0 < L)
    {H : Graph α β} (hH : GraphConnected H) (c : (pathComb γ L).verts → α)
    (hcentres : ∀ v, c v ∈ V(H)) (j : ℕ) (hj : 0 < j) (hjL : 2 * j < L) :
    GraphConnected (H.induce (combPrefix hL H c j)) ∧
      c ⟨Sum.inl ⟨2 * j - 1, by omega⟩, pathComb_spine_mem γ L _⟩ ∈ combPrefix hL H c j := by
  have hj0 : 2 * j ≠ 0 := by omega
  simp only [combPrefix, combSpineRegion, hj0, ↓reduceIte, hjL, ↓reduceDIte]
  refine ⟨vertexAvoidanceRegion_compl_connected hH _ _ (hcentres _), hcentres _, ?_⟩
  intro hx
  exact (vertexAvoidanceRegion_subset H _ _ hx).2 rfl

/-- A block before a boundary lies in the initial piece at that boundary. -/
theorem combBlock_subset_prefix {α β : Type*} {γ L n : ℕ} (hL : 0 < L)
    (H : Graph α β) (c : (pathComb γ L).verts → α)
    (hR : Antitone (combSpineRegion hL H c)) (i j : Fin n) (hij : i < j) :
    combBlock hL H c i ⊆ combPrefix hL H c j.val := by
  intro x hx
  refine ⟨combBlock_subset_graph hL H c i hx, ?_⟩
  have hi : i.val < n := i.isLt
  have hinext : i.val + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt hij) j.isLt
  have hxnot : x ∉ combSpineRegion hL H c (2 * (i.val + 1)) := by
    simpa only [combBlock, orderedRegionBlock, hi, hinext, ↓reduceIte] using hx.2
  intro hxj
  exact hxnot (hR (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hij)) hxj)

/-- The initial piece before block `j` is disjoint from every block at
or after `j`. -/
theorem combPrefix_disjoint_block {α β : Type*} {γ L n : ℕ} (hL : 0 < L)
    (H : Graph α β) (c : (pathComb γ L).verts → α)
    (hR : Antitone (combSpineRegion hL H c)) (j i : Fin n) (hji : j ≤ i) :
    Disjoint (combPrefix hL H c j.val) (combBlock hL H c i) := by
  apply Set.disjoint_left.mpr
  intro x hx hxBlock
  have hi := i.isLt
  have hxR : x ∈ combSpineRegion hL H c (2 * i.val) := by
    simpa only [combBlock, orderedRegionBlock, hi, ↓reduceIte] using hxBlock.1
  exact hx.2 (hR (Nat.mul_le_mul_left 2 hji) hxR)

end GraphMinor.GM01
