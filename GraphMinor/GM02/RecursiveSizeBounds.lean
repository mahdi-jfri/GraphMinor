module

public import GraphMinor.GM02.InducedTerminatedGraphs

/-!
# Vertex-size bounds in the alternating recursion

In A1, the separator balances all vertices. A side consists of the
separator and one exclusive side, so its size is at most two thirds of
the old size plus one third of the order bound. Above the base-case
threshold this is at most three quarters of the old size. The additional
terminal protection in corrected (2.9) only deletes vertices. In A2, both
induced graphs are simply no larger than the original graph.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The side-size estimate in the definition of A1, Graph Minors II, page 317. -/
theorem recursive_A1_side_size {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : (V(G)).Finite) (hsep : IsSeparation G H H') {w : ℕ}
    (horder : (V(H) ∩ V(H')).ncard ≤ w)
    (hL : 3 * (V(H) \ V(H')).ncard ≤ 2 * (V(G) \ (V(H) ∩ V(H'))).ncard)
    (hR : 3 * (V(H') \ V(H)).ncard ≤ 2 * (V(G) \ (V(H) ∩ V(H'))).ncard) :
    3 * V(H).ncard ≤ 2 * V(G).ncard + w ∧ 3 * V(H').ncard ≤ 2 * V(G).ncard + w := by
  have hH := hV.subset hsep.1.vertexSet_mono
  have hH' := hV.subset hsep.2.1.vertexSet_mono
  have hX : V(H) ∩ V(H') ⊆ V(G) := Set.inter_subset_left.trans hsep.1.vertexSet_mono
  have hGparts := Set.ncard_inter_add_ncard_sdiff_eq_ncard (V(G)) (V(H) ∩ V(H')) hV
  rw [Set.inter_eq_right.mpr hX] at hGparts
  have hHparts := Set.ncard_inter_add_ncard_sdiff_eq_ncard (V(H)) (V(H')) hH
  have hH'parts := Set.ncard_inter_add_ncard_sdiff_eq_ncard (V(H')) (V(H)) hH'
  rw [Set.inter_comm (V(H')) (V(H))] at hH'parts
  omega

/-- The A1 recursive calls have at most three quarters as many vertices
outside the base case, even with the corrected induced graphs of (2.9). -/
theorem recursive_A1_child_shrink {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : (V(G)).Finite) (hsep : IsSeparation G H H') {A : Termination V(G)}
    (C : CrossingScheme G H H' A) {w : ℕ} (hlarge : 4 * w < V(G).ncard)
    (horder : (V(H) ∩ V(H')).ncard ≤ w)
    (hL : 3 * (V(H) \ V(H')).ncard ≤ 2 * (V(G) \ (V(H) ∩ V(H'))).ncard)
    (hR : 3 * (V(H') \ V(H)).ncard ≤ 2 * (V(G) \ (V(H) ∩ V(H'))).ncard) :
    (4 * V(C.inducedLeft).ncard ≤ 3 * V(G).ncard ∧ V(C.inducedLeft).ncard < V(G).ncard) ∧
      (4 * V(C.inducedRight).ncard ≤ 3 * V(G).ncard ∧ V(C.inducedRight).ncard < V(G).ncard) := by
  have hsize := recursive_A1_side_size hV hsep horder hL hR
  have hleft : V(C.inducedLeft).ncard ≤ V(H).ncard :=
    Set.ncard_le_ncard (by simp only [CrossingScheme.inducedLeft, Graph.vertexSet_deleteVerts]; exact Set.sdiff_subset)
      (hV.subset hsep.1.vertexSet_mono)
  have hright : V(C.inducedRight).ncard ≤ V(H').ncard :=
    Set.ncard_le_ncard (by simp only [CrossingScheme.inducedRight, Graph.vertexSet_deleteVerts]; exact Set.sdiff_subset)
      (hV.subset hsep.2.1.vertexSet_mono)
  omega

/-- The A2 calls do not increase the graph's vertex count, Graph Minors II,
page 317. This also applies to every corrected crossing-scheme deletion. -/
theorem recursive_A2_child_size {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : (V(G)).Finite) (hsep : IsSeparation G H H') {A : Termination V(G)}
    (C : CrossingScheme G H H' A) :
    V(C.inducedLeft).ncard ≤ V(G).ncard ∧ V(C.inducedRight).ncard ≤ V(G).ncard := by
  constructor
  · apply Set.ncard_le_ncard _ hV
    simp only [CrossingScheme.inducedLeft, Graph.vertexSet_deleteVerts]
    exact Set.sdiff_subset.trans hsep.1.vertexSet_mono
  · apply Set.ncard_le_ncard _ hV
    simp only [CrossingScheme.inducedRight, Graph.vertexSet_deleteVerts]
    exact Set.sdiff_subset.trans hsep.2.1.vertexSet_mono

end GraphMinor.GM02
