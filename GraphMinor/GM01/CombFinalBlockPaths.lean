module

public import GraphMinor.GM01.CombBlocks
public import GraphMinor.GM01.GraphSeparators

/-!
# Paths from a late boundary to the final block

After (4.11), Graph Minors I, page 59, chooses the path `P_3` in `H`
from `w_2` to the last block, with no internal vertex in that block.
The late region is connected and contains the last spine centre.
Take a path to that centre and stop at its first vertex in the final
block. Its vertices remain in the late region.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- The path `P_3` chosen after GM01 (4.11), page 59. The only vertex
of the path in the final block is its final vertex. -/
theorem exists_path_to_final_combBlock {α β : Type*} {γ L n : ℕ}
    (hL : 0 < L) (hn : 0 < n) (h2n : 2 * n ≤ L)
    {H : Graph α β} (hconn : GraphConnected H)
    {c : (pathComb γ L).verts → α} (hc : Function.Injective c)
    (hcentres : ∀ v, c v ∈ V(H))
    (q : Fin n) {w : α} (hw : w ∈ combSpineRegion hL H c (2 * q.val)) :
    ∃ z ∈ combBlock hL H c (⟨n - 1, by omega⟩ : Fin n),
      ∃ P : Graph α β, IsGraphPathWithEnds H P w z ∧
        V(P) ⊆ combSpineRegion hL H c (2 * q.val) ∧
        V(P) ∩ combBlock hL H c (⟨n - 1, by omega⟩ : Fin n) = {z} := by
  let last : Fin n := ⟨n - 1, by omega⟩
  let t := c ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩
  have hqL : 2 * q.val < L := by have := q.isLt; omega
  have hlL : 2 * last.val < L := by dsimp [last]; omega
  have hlate := combSpineRegion_connected hL hconn hc hcentres (2 * q.val) hqL
  have hlast := combSpineRegion_connected hL hconn hc hcentres (2 * last.val) hlL
  have htLast : t ∈ combBlock hL H c last := by
    have hnot : ¬ last.val + 1 < n := by dsimp [last]; omega
    simpa only [combBlock, orderedRegionBlock, last.isLt, hnot, ↓reduceIte,
      sdiff_empty] using hlast.2
  have hregionH := combSpineRegion_subset hL H c (2 * q.val)
  obtain ⟨Q, hQ⟩ := exists_path_of_adj_reachable hw (hlate.1.2 w hw t hlate.2)
  have hQH := hQ.mono (H.induce_le hregionH)
  obtain ⟨w', hw', z, hz, P, hPQ, hP⟩ := hQH.exists_isFromToPathWithEnds
    (X := {w}) (Y := combBlock hL H c last) rfl htLast
  have hww : w' = w := hw'
  subst w'
  exact ⟨z, hz, P, hP.1, hPQ.vertexSet_mono.trans hQ.le.vertexSet_mono, hP.2.2⟩

end GraphMinor.GM01
