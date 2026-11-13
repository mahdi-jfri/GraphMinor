module

public import GraphMinor.Thomason.PartialDomination
public import Mathlib.Data.Finset.Powerset

/-!
# Subsets with an explicit bound on uncovered vertices

Thomason's Lemma 5 (1984), p. 263, counts subsets leaving few vertices
undominated. Keeping the uncovered bound separate from the subset size
allows the same insertion argument to use the actual degree estimate.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The `k`-subsets leaving at most `t` vertices undominated. -/
def residualBoundedSets (k t : ℕ) : Finset (Finset V) :=
  (univ : Finset V).powersetCard k |>.filter
    (fun Y => (undominatedVertices G Y).card ≤ t)

/-- Membership gives the selected size and the uncovered bound. -/
theorem mem_residualBoundedSets_iff (k t : ℕ) (Y : Finset V) :
    Y ∈ residualBoundedSets G k t ↔ Y.card = k ∧ (undominatedVertices G Y).card ≤ t := by
  simp only [residualBoundedSets, mem_filter, mem_powersetCard, subset_univ, true_and]

/-- An empty selection leaves exactly the order of the graph uncovered. -/
theorem empty_mem_residualBoundedSets :
    (∅ : Finset V) ∈ residualBoundedSets G 0 (Fintype.card V) := by
  rw [mem_residualBoundedSets_iff]
  simp

/-- Inserting a vertex with the stated partial domination property gives
the next selected size with its corresponding uncovered bound. -/
theorem insert_mem_residualBoundedSets {k t h : ℕ} {Y : Finset V} {v : V}
    (hY : Y ∈ residualBoundedSets G k t) (hvY : v ∉ Y)
    (hv : v ∈ verticesLeavingAtMost G (undominatedVertices G Y) h) :
    insert v Y ∈ residualBoundedSets G (k + 1) h := by
  obtain ⟨hcard, _⟩ := (mem_residualBoundedSets_iff G k t Y).mp hY
  apply (mem_residualBoundedSets_iff G (k + 1) h _).mpr
  refine ⟨by rw [card_insert_of_notMem hvY, hcard], ?_⟩
  have hh := (mem_filter.mp hv).2
  have heq : undominatedVertices G (insert v Y) =
      undominatedVertices G Y ∩ undominatedVertices G {v} := by
    rw [undominatedVertices_insert]
    ext x
    simp only [undominatedVertices, dominatedVertices_singleton, mem_sdiff, mem_inter, mem_univ, true_and]
  rwa [heq]

end GraphMinor.Thomason
