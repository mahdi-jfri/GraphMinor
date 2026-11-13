module

public import GraphMinor.Compute.GM02FilterSide
public import GraphMinor.Compute.GM02RankEdgeWords

/-!
# Compact edge words for recursive children

The side edge filter already removes every endpoint outside its child
vertex set. Deleting those vertices therefore removes no further edge.
The rank-rewriting loop gives the canonical edge words of the compact
child graph directly from the filtered words.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- All endpoints retained by the side filter belong to the child vertex set. -/
theorem gm02FilteredSide_filter_survives {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (A B : Finset (Fin n)) :
    (edgeListOf (gm02FilteredSide F A B)).filter
      (fun p => decide (p.1 ∉ Bᶜ) && decide (p.2 ∉ Bᶜ)) =
        edgeListOf (gm02FilteredSide F A B) := by
  apply List.filter_eq_self.2
  intro p hp
  have hadj := ((mem_edgeListOf _ p).1 hp).2
  have hk := hadj.2
  simp only [keepCoreEdge, decide_eq_true_eq] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_compl, not_not]
  exact ⟨hk.1, hk.2.1⟩

/-- Compact child edge words are the filtered words with vertex ranks substituted. -/
theorem gm02CompactFilteredSide_edgeWords {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (A B : Finset (Fin n)) :
    flatEdges (edgeListOf ((gm02FilteredSide F A B).comap (compactEmb Bᶜ))) =
      (flatEdges (edgeListOf (gm02FilteredSide F A B))).map (compactRank Bᶜ) := by
  simpa only [gm02FilteredSide_filter_survives] using
    gm02CompactEdgeWords (gm02FilteredSide F A B) Bᶜ

/-- The filtered child has no more edges than its parent. -/
theorem gm02FilteredSide_edgeList_length_le {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (A B : Finset (Fin n)) :
    (edgeListOf (gm02FilteredSide F A B)).length ≤ (edgeListOf F).length := by
  rw [gm02FilteredSide_edgeList]
  exact List.length_filter_le _ _

end GraphMinor.Compute
