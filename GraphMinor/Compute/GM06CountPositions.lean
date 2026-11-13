module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Counting endpoint-list positions

Finite edge labels are list positions. A set of positions selected by
a predicate has cardinality equal to the length of the filtered list.
This connects finite incidence counts to the set cardinalities used
in the drawing's definition of valency.
-/

public section
namespace GraphMinor.Compute
open scoped BigOperators

/-- Counting positions satisfying a predicate agrees with filtering the list. -/
theorem gm06Ncard_indices_eq_filter_length {α : Type*} (xs : List α) (p : α → Prop)
    [DecidablePred p] :
    ({i : Fin xs.length | p xs[i.val]} : Set (Fin xs.length)).ncard =
      (xs.filter fun a => decide (p a)).length := by
  classical
  have hc : ({i : Fin xs.length | p xs[i.val]} : Set (Fin xs.length)).ncard =
      ∑ i : Fin xs.length, if p xs[i.val] then 1 else 0 := by
    rw [← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
    exact (Finset.sum_boole (R := ℕ) (fun i : Fin xs.length => p xs[i.val]) Finset.univ).symm
  rw [hc]
  clear hc
  induction xs with
  | nil => simp
  | cons a xs ih =>
    change (∑ i : Fin (xs.length + 1), if p (a :: xs)[i.val] then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ, ih]
    by_cases h : p a <;> simp [h, Nat.add_comm]

end GraphMinor.Compute
