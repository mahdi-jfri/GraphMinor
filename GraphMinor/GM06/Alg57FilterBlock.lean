module

public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.List.Rotate

/-!
# The rotation of a block of consecutive darts

A copy of a split vertex keeps a block of consecutive darts of the old rotation row, in the old
cyclic order (Section 9 of our proof of VI (5.7), outlined in `Alg57Algorithm.lean`). Here is the
rotation of such a filtered row (`formPerm_filter_symm_of_block`): inside the block the predecessor
is the old predecessor, except that the first dart of the block is preceded by the last one. The
block is given as an initial segment of a rotation of the row.
-/

public section

namespace GraphMinor.GM06

open Equiv

/-- Rotating a list and then filtering it is a rotation of filtering it. -/
theorem isRotated_filter_rotate {α : Type*} (l : List α) (p : α → Bool) (n : ℕ) :
    l.filter p ~r (l.rotate n).filter p := by
  rw [List.rotate_eq_drop_append_take_mod]
  conv_lhs => rw [← List.take_append_drop (n % l.length) l]
  rw [List.filter_append, List.filter_append]
  exact List.isRotated_append

/-- A filter keeping exactly the first `K` entries is `take K`. -/
theorem filter_eq_take_of_getElem {α : Type*} (l : List α) (p : α → Bool) (K : ℕ)
    (h : ∀ (j : ℕ) (hj : j < l.length), p l[j] = true ↔ j < K) : l.filter p = l.take K := by
  induction l generalizing K with
  | nil => simp
  | cons x xs ih =>
    cases K with
    | zero =>
      rw [List.take_zero, List.filter_eq_nil_iff]
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      have := (h j hj).not.mpr (by omega)
      simpa using this
    | succ K =>
      have hx : p x = true := (h 0 (by simp)).mpr (by omega)
      rw [List.filter_cons_of_pos hx, List.take_succ_cons,
        ih K (fun j hj => by
          have := h (j + 1) (by simpa using hj)
          simp only [List.getElem_cons_succ] at this
          rw [this]; omega)]

/-- The rotation of an initial segment: inside it, the predecessor is the old predecessor. -/
theorem formPerm_take_symm_getElem {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    {K : ℕ} (hK : K ≤ l.length) {j : ℕ} (hj1 : 1 ≤ j) (hjK : j < K) :
    (l.take K).formPerm.symm (l[j]'(by omega)) = l.formPerm.symm (l[j]'(by omega)) := by
  have hlen : (l.take K).length = K := by simp [hK]
  have h1 : l.formPerm (l[j - 1]'(by omega)) = l[j]'(by omega) := by
    rw [List.formPerm_apply_getElem _ hl]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h2 : (l.take K).formPerm ((l.take K)[j - 1]'(by omega)) = l[j]'(by omega) := by
    rw [List.formPerm_apply_getElem _ (hl.sublist (List.take_sublist _ _))]
    simp only [List.getElem_take, hlen]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have e1 : l.formPerm.symm (l[j]'(by omega)) = l[j - 1]'(by omega) := by
    rw [← h1]; simp
  have e2 : (l.take K).formPerm.symm (l[j]'(by omega)) = l[j - 1]'(by omega) := by
    rw [← h2]; simp
  rw [e1, e2]

/-- The rotation of an initial segment sends its last entry to its first. -/
theorem formPerm_take_symm_getElem_zero {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    {K : ℕ} (hK : K ≤ l.length) (hK1 : 1 ≤ K) :
    (l.take K).formPerm.symm (l[0]'(by omega)) = l[K - 1]'(by omega) := by
  have hlen : (l.take K).length = K := by simp [hK]
  have h2 : (l.take K).formPerm ((l.take K)[K - 1]'(by omega)) = l[0]'(by omega) := by
    rw [List.formPerm_apply_getElem _ (hl.sublist (List.take_sublist _ _))]
    simp only [List.getElem_take, hlen]
    congr 1
    rw [Nat.sub_add_cancel hK1, Nat.mod_self]
  rw [← h2]
  simp

/-- **The rotation of a block.** Let a row `l` without repetitions keep, under `p`, exactly the
first `K ≥ 1` entries of its rotation by `i`. In the filtered row, a kept dart other than the first
of the block has its old predecessor; the first of the block is preceded by the last. -/
theorem formPerm_filter_symm_of_block {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (p : α → Bool) (i : ℕ) {K : ℕ} (hK1 : 1 ≤ K) (hK : K ≤ l.length)
    (hp : ∀ (j : ℕ) (hj : j < l.length), p ((l.rotate i)[j]'(by simpa using hj)) = true ↔ j < K) :
    (∀ x ∈ l, p x = true → x ≠ (l.rotate i)[0]'(by simp; omega) →
      (l.filter p).formPerm.symm x = l.formPerm.symm x) ∧
    (l.filter p).formPerm.symm ((l.rotate i)[0]'(by simp; omega)) =
      (l.rotate i)[K - 1]'(by simp; omega) := by
  have hr : (l.rotate i).Nodup := (List.nodup_rotate).mpr hl
  have hrl : (l.rotate i).length = l.length := List.length_rotate l i
  have hfilt : (l.filter p).formPerm = ((l.rotate i).take K).formPerm := by
    rw [List.formPerm_eq_of_isRotated (hl.filter p) (isRotated_filter_rotate l p i),
      filter_eq_take_of_getElem (l.rotate i) p K (fun j hj => hp j (by omega))]
  have hrot : l.formPerm = (l.rotate i).formPerm := (List.formPerm_rotate l hl i).symm
  refine ⟨fun x hx hpx hxf => ?_, ?_⟩
  · rw [hfilt, hrot]
    have hx' : x ∈ l.rotate i := (List.mem_rotate).mpr hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
    have hjK : j < K := (hp j (by omega)).mp hpx
    have hj1 : 1 ≤ j := by
      by_contra h0
      exact hxf (by congr 1; omega)
    exact formPerm_take_symm_getElem (l.rotate i) hr (by omega) hj1 hjK
  · rw [hfilt]
    exact formPerm_take_symm_getElem_zero (l.rotate i) hr (by omega) hK1

end GraphMinor.GM06
