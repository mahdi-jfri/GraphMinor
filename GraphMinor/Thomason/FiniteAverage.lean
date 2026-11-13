module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Finite averaging outside a union of exceptional events

Bound the total weight on a finite family, remove the exceptional events,
and compare the remaining count with the weight bound. This is the finite
counting form of Markov's inequality and the union bound used to select
clique branches. The family need not consist of distinct vertex sets.
-/

public section
namespace GraphMinor.Thomason
open Finset
universe u v
/-- Remove all exceptional selections and apply the total uncovered
bound to the remaining family. A direct bound also suffices when the
number of exceptional selections is smaller than the family size. -/
theorem exists_mem_avoiding_of_weight_sum
    {C : Type u} [DecidableEq C] {I : Type v} [DecidableEq I]
    (S : Finset C) (indices : Finset I) (P : I → C → Prop) [∀ i, DecidablePred (P i)]
    (w : C → ℕ) (t : I → ℕ) (M U D T : ℕ)
    (hM : M ≤ S.card) (htotal : (∑ c ∈ S, w c) ≤ U)
    (hbound : ∀ c ∈ S, w c ≤ D)
    (hbad : ∀ i ∈ indices, (S.filter (P i)).card ≤ t i)
    (hcount : U < (M - ∑ i ∈ indices, t i) * (T + 1) ∨
      (D ≤ T ∧ (∑ i ∈ indices, t i) < M)) :
    ∃ c ∈ S, w c ≤ T ∧ ∀ i ∈ indices, ¬ P i c := by
  let F := indices.biUnion (fun i => S.filter (P i))
  let A := S \ F
  let badCount := ∑ i ∈ indices, t i
  have hF : F.card ≤ badCount := by
    calc
      F.card ≤ ∑ i ∈ indices, (S.filter (P i)).card := card_biUnion_le
      _ ≤ ∑ i ∈ indices, t i := by
        apply sum_le_sum
        intro i hi
        exact hbad i hi
  have hAcard : M - badCount ≤ A.card := by
    have hsplit := card_sdiff_add_card_inter S F
    have hsmall := card_le_card (inter_subset_right : S ∩ F ⊆ F)
    change A.card + (S ∩ F).card = S.card at hsplit
    omega
  have hex : ∃ Y ∈ A, w Y ≤ T := by
    rcases hcount with havg | ⟨hDT, hcount⟩
    swap
    · have hpos : 0 < A.card := lt_of_lt_of_le (Nat.sub_pos_of_lt hcount) hAcard
      obtain ⟨Y, hY⟩ := card_pos.mp hpos
      exact ⟨Y, hY, (hbound Y (mem_sdiff.mp hY).1).trans hDT⟩
    by_contra hnone
    have hbad (Y : C) (hY : Y ∈ A) : T + 1 ≤ w Y := by
      have hh : ¬ w Y ≤ T := fun h => hnone ⟨Y, hY, h⟩
      omega
    have hlower : A.card * (T + 1) ≤ ∑ Y ∈ S, w Y := by
      calc
        A.card * (T + 1) = ∑ _Y ∈ A, (T + 1) := by simp
        _ ≤ ∑ Y ∈ A, w Y := sum_le_sum hbad
        _ ≤ ∑ Y ∈ S, w Y :=
          sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => Nat.zero_le _)
    have hbound := (Nat.mul_le_mul_right (T + 1) hAcard).trans (hlower.trans htotal)
    exact (not_lt_of_ge hbound) havg
  obtain ⟨Y, hY, hdom⟩ := hex
  obtain ⟨hYS, hYF⟩ := mem_sdiff.mp hY
  refine ⟨Y, hYS, hdom, ?_⟩
  intro i hi hP
  exact hYF (mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨hYS, hP⟩⟩)

end GraphMinor.Thomason
