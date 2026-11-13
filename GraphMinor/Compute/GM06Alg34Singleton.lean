module

public import GraphMinor.Compute.GM06Alg34Graph
public import GraphMinor.Compute.GM06Alg34TagPartition
import GraphMinor.GM06.Section3Basic

/-!
# Finite graph and division updates for singleton deletion

For (3.3)(i), page 120, remove the singleton vertex from the active
vertex list and remove every list representing its singleton block.
Filtering by the represented set handles repeated labels and repeated
representations of the same block. The resulting finite graph is exactly
the vertex-deleted graph, and the resulting division is its required
set difference. Thus the paper's reduction preserves feasibility.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set Graph GM06

/-- Remove a label from an active vertex list. -/
def gm06EraseVertex {n : ℕ} (vs : List (Fin n)) (v : Fin n) : List (Fin n) :=
  vs.filter (fun a => a != v)

/-- Remove every list representing the singleton block at `v`. -/
def gm06EraseSingletonBlocks {n : ℕ} (D : List (List (Fin n))) (v : Fin n) :
    List (List (Fin n)) := D.filter (fun B => decide (B.toFinset ≠ {v}))

/-- The filtered active labels are exactly the old labels minus the deleted vertex. -/
theorem gm06EraseVertex_block {n : ℕ} (vs : List (Fin n)) (v : Fin n) :
    GM06DrawingData.block (gm06EraseVertex vs v) = GM06DrawingData.block vs \ {v} := by
  ext a
  simp [GM06DrawingData.block, gm06EraseVertex]

private theorem gm06_block_eq_singleton {n : ℕ} (B : List (Fin n)) (v : Fin n) :
    B.toFinset = {v} ↔ GM06DrawingData.block B = {v} := by
  constructor
  · intro h
    ext a
    simpa only [List.mem_toFinset, Finset.mem_singleton, Set.mem_singleton_iff, GM06DrawingData.block, mem_ofPred_eq] using
      (show a ∈ B.toFinset ↔ a ∈ ({v} : Finset (Fin n)) from h ▸ Iff.rfl)
  · intro h
    ext a
    simpa only [List.mem_toFinset, Finset.mem_singleton, Set.mem_singleton_iff, GM06DrawingData.block, mem_ofPred_eq] using
      (show a ∈ GM06DrawingData.block B ↔ a ∈ ({v} : Set (Fin n)) from h ▸ Iff.rfl)

/-- Filtering all singleton representations gives exactly the division
with the singleton set removed, even when a block has repeated labels. -/
theorem gm06EraseSingletonBlocks_sets {n : ℕ} (D : List (List (Fin n))) (v : Fin n) :
    gm06BlockSets (gm06EraseSingletonBlocks D v) = gm06BlockSets D \ {{v}} := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    have hb := List.mem_filter.mp hB
    refine ⟨⟨B, hb.1, rfl⟩, ?_⟩
    change GM06DrawingData.block B ≠ {v}
    exact fun heq => (of_decide_eq_true hb.2) ((gm06_block_eq_singleton B v).mpr heq)
  · rintro ⟨⟨B, hB, rfl⟩, hne⟩
    refine ⟨B, List.mem_filter.mpr ⟨hB, ?_⟩, rfl⟩
    apply decide_eq_true
    exact fun heq => hne ((gm06_block_eq_singleton B v).mp heq)

/-- Filtering the active labels implements vertex deletion in the finite graph. -/
theorem gm06EraseVertex_graph (x : GM06DrawingData) (vs : List (Fin x.n)) (v : Fin x.n) :
    x.graph.induce (GM06DrawingData.block (gm06EraseVertex vs v)) =
      (x.graph.induce (GM06DrawingData.block vs)).deleteVerts {v} := by
  apply Graph.ext
  · simp only [Graph.vertexSet_deleteVerts, Graph.vertexSet_induce, gm06EraseVertex_block]
  · intro e a b
    simp only [Graph.induce_isLink, Graph.deleteVerts_isLink, gm06EraseVertex_block,
      mem_sdiff, mem_singleton_iff]
    tauto

/-- The finite graph/partition update implements exactly the
feasibility equivalence in Graph Minors VI (3.3)(i). -/
theorem gm06EraseSingleton_isFeasible_iff (x : GM06DrawingData)
    (vs : List (Fin x.n)) (D : List (List (Fin x.n))) (v : Fin x.n)
    (hD : IsDivision (gm06BlockSets D))
    (hsub : divisionUnion (gm06BlockSets D) ⊆ GM06DrawingData.block vs)
    (hv : {v} ∈ gm06BlockSets D) :
    IsFeasible (x.graph.induce (GM06DrawingData.block vs)) (gm06BlockSets D) ↔
      IsFeasible (x.graph.induce (GM06DrawingData.block (gm06EraseVertex vs v)))
        (gm06BlockSets (gm06EraseSingletonBlocks D v)) := by
  rw [gm06EraseVertex_graph, gm06EraseSingletonBlocks_sets]
  exact theorem_3_3_i _ _ _ hD hsub hv

end GraphMinor.Compute
