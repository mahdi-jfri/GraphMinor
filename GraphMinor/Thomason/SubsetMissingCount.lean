module

public import GraphMinor.Thomason.DominatingSets
public import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Counting uncovered vertices over all selected subsets

A vertex is missed by a selected set exactly when every selected
vertex misses it. Counting selected-set and uncovered-vertex pairs in
two orders gives the total uncovered count. This is a finite subset
version of the averaging step in Wood (2026), arXiv:2610.41060v1,
Lemma 7, pp. 5–6.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex is missed by a set exactly when the whole set lies among
that vertex's non-neighbours other than itself. -/
theorem mem_undominatedVertices_iff_subset_singleton (Y : Finset V) (v : V) :
    v ∈ undominatedVertices G Y ↔ Y ⊆ undominatedVertices G {v} := by
  simp only [undominatedVertices, Finset.subset_iff, mem_sdiff, mem_univ, true_and,
    dominatedVertices_singleton]
  simp only [dominatedVertices, mem_union, mem_biUnion, mem_insert,
    G.mem_neighborFinset, not_or, not_exists, not_and]
  constructor
  · rintro ⟨hv, hAdj⟩ y hy
    exact ⟨fun h => hv (h ▸ hy), fun h => hAdj y hy h.symm⟩
  · intro h
    exact ⟨fun hv => (h hv).1 rfl, fun y hy hyadj => (h hy).2 hyadj.symm⟩

/-- The exact double count of uncovered vertices over all `k`-subsets. -/
theorem sum_card_undominatedVertices_powersetCard (k : ℕ) :
    (∑ Y ∈ (univ : Finset V).powersetCard k, (undominatedVertices G Y).card) =
      ∑ v : V, (undominatedVertices G {v}).card.choose k := by
  let R : Finset V → V → Prop := fun Y v => v ∈ undominatedVertices G Y
  have hrow (Y : Finset V) : (univ : Finset V).bipartiteAbove R Y = undominatedVertices G Y := by
    ext v
    simp only [mem_bipartiteAbove, mem_univ, true_and, R]
  have hcol (v : V) : ((univ : Finset V).powersetCard k).bipartiteBelow R v =
      (undominatedVertices G {v}).powersetCard k := by
    ext Y
    simp only [mem_bipartiteBelow, mem_powersetCard, subset_univ, true_and,
      R, mem_undominatedVertices_iff_subset_singleton]
    exact and_comm
  have hc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    (s := (univ : Finset V).powersetCard k) (t := univ)
  simpa only [hrow, hcol, card_powersetCard] using hc

/-- The actual non-neighbour bound controls the total uncovered count
over all selections of a given size. -/
theorem sum_card_undominatedVertices_powersetCard_le (k D : ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1) :
    (∑ Y ∈ (univ : Finset V).powersetCard k, (undominatedVertices G Y).card) ≤
      Fintype.card V * D.choose k := by
  rw [sum_card_undominatedVertices_powersetCard]
  calc
    (∑ v : V, (undominatedVertices G {v}).card.choose k) ≤ ∑ _v : V, D.choose k := by
      apply sum_le_sum
      intro v _
      apply Nat.choose_le_choose
      rw [card_undominatedVertices_singleton]
      have hh := hdegree v
      omega
    _ = Fintype.card V * D.choose k := by simp

end GraphMinor.Thomason
