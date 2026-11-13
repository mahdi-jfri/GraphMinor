module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Find

/-!
# Grouping component weights

The numerical step of II (2.6) first takes a component whose weight is at
least a third of the total, if one exists. Otherwise all weights are less
than a third. A shortest selection reaching a third then has weight less
than two thirds, since deleting its last element leaves less than a third.
-/

public section
namespace GraphMinor.GM02
open Finset Classical

/-- The component-weight grouping in II (2.6), pages 313–314. The first
case uses one large component, whose two-thirds bound suffices also for
algorithm (3.1), page 316. In the other case a minimal selection
reaching a third has no surplus of more than one small component. -/
theorem exists_two_thirds_weight_partition_of_two_thirds {ι : Type*} (s : Finset ι) (c : ι → ℕ)
    (hbound : ∀ i ∈ s, 3 * c i ≤ 2 * ∑ j ∈ s, c j) :
    ∃ a ⊆ s, (∑ j ∈ s, c j) ≤ 3 * (∑ j ∈ a, c j) ∧
      3 * (∑ j ∈ a, c j) ≤ 2 * (∑ j ∈ s, c j) := by
  let N := ∑ j ∈ s, c j
  by_cases hlarge : ∃ i ∈ s, N ≤ 3 * c i
  · obtain ⟨i, hi, hci⟩ := hlarge
    refine ⟨{i}, singleton_subset_iff.2 hi, ?_, ?_⟩
    · simpa using hci
    · have hh := hbound i hi
      change 3 * c i ≤ 2 * N at hh
      simpa using hh
  · have hsmall : ∀ i ∈ s, 3 * c i < N := by
      intro i hi
      exact Nat.lt_of_not_ge (fun h => hlarge ⟨i, hi, h⟩)
    have hex : ∃ n : ℕ, ∃ a ⊆ s, a.card = n ∧ N ≤ 3 * (∑ j ∈ a, c j) :=
      ⟨s.card, s, Subset.refl _, rfl, by omega⟩
    obtain ⟨a, has, hcard, hsum⟩ := Nat.find_spec hex
    refine ⟨a, has, hsum, ?_⟩
    by_cases ha : a.Nonempty
    · obtain ⟨i, hi⟩ := ha
      have herase : a.erase i ⊆ s := (erase_subset i a).trans has
      have hless : (a.erase i).card < Nat.find hex := by
        rw [← hcard]
        exact card_erase_lt_of_mem hi
      have hminimal := Nat.find_min hex hless
      have hlow : 3 * (∑ j ∈ a.erase i, c j) < N := by
        apply Nat.lt_of_not_ge
        intro h
        exact hminimal ⟨a.erase i, herase, rfl, h⟩
      have hsplit := sum_erase_add a c hi
      have hci := hsmall i (has hi)
      omega
    · have hz : a = ∅ := not_nonempty_iff_eq_empty.1 ha
      simp [hz]

/-- The half-weight hypothesis used in II (2.6) implies the two-thirds
bound needed by the component grouping. -/
theorem exists_two_thirds_weight_partition {ι : Type*} (s : Finset ι) (c : ι → ℕ)
    (hhalf : ∀ i ∈ s, 2 * c i ≤ ∑ j ∈ s, c j) :
    ∃ a ⊆ s, (∑ j ∈ s, c j) ≤ 3 * (∑ j ∈ a, c j) ∧
      3 * (∑ j ∈ a, c j) ≤ 2 * (∑ j ∈ s, c j) := by
  apply exists_two_thirds_weight_partition_of_two_thirds s c
  intro i hi
  have hh := hhalf i hi
  omega

end GraphMinor.GM02
