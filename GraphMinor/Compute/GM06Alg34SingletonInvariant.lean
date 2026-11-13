module

public import GraphMinor.Compute.GM06Alg34Singleton

/-!
# Preserving the division conditions under singleton deletion

After removing a singleton block and its vertex, all other blocks stay
nonempty, disjoint, and contained in the active vertices. Disjointness
excludes the deleted vertex from every surviving block. The number of
active labels strictly decreases, even when the vertex list repeats labels.
These are the invariants needed to repeat (3.3)(i).
-/

public section
namespace GraphMinor.Compute

open Set GM06

/-- The finite singleton update preserves the division laws. -/
theorem gm06EraseSingletonBlocks_isDivision {n : ℕ} (D : List (List (Fin n)))
    (v : Fin n) (hD : IsDivision (gm06BlockSets D)) :
    IsDivision (gm06BlockSets (gm06EraseSingletonBlocks D v)) := by
  rw [gm06EraseSingletonBlocks_sets]
  exact ⟨hD.1.subset sdiff_subset, fun δ hδ => hD.2.1 δ hδ.1,
    hD.2.2.subset sdiff_subset⟩

/-- Every surviving block avoids the deleted vertex by the original
division's disjointness, and hence lies in the remaining active labels. -/
theorem gm06EraseSingletonBlocks_union_subset {n : ℕ} (vs : List (Fin n))
    (D : List (List (Fin n))) (v : Fin n) (hD : IsDivision (gm06BlockSets D))
    (hsub : divisionUnion (gm06BlockSets D) ⊆ GM06DrawingData.block vs)
    (hv : {v} ∈ gm06BlockSets D) :
    divisionUnion (gm06BlockSets (gm06EraseSingletonBlocks D v)) ⊆
      GM06DrawingData.block (gm06EraseVertex vs v) := by
  rw [gm06EraseSingletonBlocks_sets, gm06EraseVertex_block]
  rintro a ⟨δ, ⟨hδ, hne⟩, ha⟩
  refine ⟨hsub ⟨δ, hδ, ha⟩, ?_⟩
  intro hav
  have hdisj : Disjoint δ {v} := hD.2.2 hδ hv hne
  exact Set.disjoint_left.mp hdisj ha hav

/-- The vertex of any singleton block belongs to the active labels. -/
theorem gm06_singleton_vertex_mem {n : ℕ} (vs : List (Fin n))
    (D : List (List (Fin n))) (v : Fin n)
    (hsub : divisionUnion (gm06BlockSets D) ⊆ GM06DrawingData.block vs)
    (hv : {v} ∈ gm06BlockSets D) : v ∈ vs :=
  hsub ⟨{v}, hv, Set.mem_singleton v⟩

/-- On distinct active labels the list filter is precisely finite-set erasure. -/
theorem gm06EraseVertex_toFinset {n : ℕ} (vs : List (Fin n)) (v : Fin n) :
    (gm06EraseVertex vs v).toFinset = vs.toFinset.erase v := by
  ext a
  simp [gm06EraseVertex, and_comm]

/-- Removing an active vertex strictly decreases the number of active labels. -/
theorem gm06EraseVertex_card_lt {n : ℕ} (vs : List (Fin n)) (v : Fin n)
    (hv : v ∈ vs) :
    (gm06EraseVertex vs v).toFinset.card < vs.toFinset.card := by
  rw [gm06EraseVertex_toFinset]
  exact Finset.card_erase_lt_of_mem (List.mem_toFinset.mpr hv)

end GraphMinor.Compute
