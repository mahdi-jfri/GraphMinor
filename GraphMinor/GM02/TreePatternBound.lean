module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Counting branch vertices in reduced tree patterns

In the finite-pattern argument for II (4.8), a branch tree has designated
attachment vertices. Once leaves outside those attachments are removed and
degree-two vertices are suppressed, every remaining vertex outside the
attachments has degree at least three. The degree sum of a tree bounds the
number of these remaining vertices in terms of the attachments. A coarse
factor of three suffices for finiteness.
-/

public section

namespace GraphMinor.GM02

open SimpleGraph Finset Classical
open scoped BigOperators

/-- A finite tree whose vertices outside `A` all have degree at least three
has at most three times as many vertices as there are vertices in `A`.
This coarse degree-sum bound suffices for counting reduced branch patterns. -/
theorem card_tree_le_three_card_attachments {α : Type*} [Fintype α]
    (T : SimpleGraph α) (hT : T.IsTree) (A : Finset α)
    (hdegree : ∀ a ∉ A, 3 ≤ T.degree a) :
    Fintype.card α ≤ 3 * A.card := by
  classical
  have hsum : 3 * (Finset.univ \ A).card ≤ ∑ a, T.degree a := by
    calc
      3 * (Finset.univ \ A).card = ∑ _a ∈ Finset.univ \ A, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ Finset.univ \ A, T.degree a := by
        apply Finset.sum_le_sum
        intro a ha
        exact hdegree a (Finset.mem_sdiff.1 ha).2
      _ ≤ ∑ a, T.degree a := Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have hcard : (Finset.univ \ A).card = Fintype.card α - A.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ]
  have hA : A.card ≤ Fintype.card α := Finset.card_le_univ A
  have hedge := hT.card_edgeFinset
  rw [T.sum_degrees_eq_twice_card_edges, hcard] at hsum
  omega

end GraphMinor.GM02
