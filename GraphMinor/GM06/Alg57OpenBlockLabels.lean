module

public import GraphMinor.GM06.Alg57CutBlocks

/-!
# Labels inside a cut block

In the local comparison for VI (5.7), page 133, deleting an end
merges the two adjacent corner labels. Along an open part of a
rotation row containing only deleted ends, every corner therefore
has the label at the first end. We prove this by reading the row
from that end and inducting on the number of entries read.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- A label unchanged across every strict interior end of a cyclic
interval is constant from its first end up to its last end. -/
theorem label_eq_first_of_cyclic_interval {α β : Type*} [DecidableEq α]
    (row : List α) (hn : row.Nodup) (g : α → β) {a b q : α}
    (ha : a ∈ row) (hb : b ∈ row) (hab : a ≠ b) (hq : q ∈ row)
    (hqmem : q = a ∨ GM06DrawingData.cyclicBetween
      (row.idxOf a) (row.idxOf b) (row.idxOf q) = true)
    (hskip : ∀ d ∈ row, GM06DrawingData.cyclicBetween
      (row.idxOf a) (row.idxOf b) (row.idxOf d) = true →
        g (row.formPerm.symm d) = g d) : g q = g a := by
  rcases hqmem with rfl | hqmem
  · rfl
  have hi := List.idxOf_lt_length_of_mem ha
  have hb' := List.idxOf_lt_length_of_mem hb
  have hq' := List.idxOf_lt_length_of_mem hq
  have hn0 : 0 < row.length := by omega
  let xs := row.rotate (row.idxOf a)
  let K := (row.idxOf b + row.length - row.idxOf a) % row.length
  have hK : K < row.length := Nat.mod_lt _ hn0
  have hlen : xs.length = row.length := List.length_rotate _ _
  have hnx : xs.Nodup := List.nodup_rotate.mpr hn
  have hfirst : xs[0]'(by omega) = a := by
    rw [List.getElem_rotate]
    simp only [Nat.zero_add, Nat.mod_eq_of_lt hi, List.getElem_idxOf]
  have hlast : xs[K]'(by omega) = b := by
    rw [List.getElem_rotate, getElem_eq_iff_eq_idxOf hn hb]
    exact cyclic_closed_last hi hb'
  have hperm : row.formPerm = xs.formPerm := (List.formPerm_rotate row hn _).symm
  have hinterior (j : ℕ) (hj0 : 0 < j) (hjK : j < K) :
      GM06DrawingData.cyclicBetween (row.idxOf a) (row.idxOf b)
        (row.idxOf (xs[j]'(by omega))) = true := by
    have hclosed := (cyclic_closed_iff hi hb' (show j < row.length by omega)
      (idxOf_ne_of_ne ha hb hab)).mpr (show j < K + 1 by omega)
    have hja : xs[j]'(by omega) ≠ a := by
      intro he
      have hh := (getElem_eq_iff_eq_idxOf hnx (List.getElem_mem (by omega : 0 < xs.length))
        (by omega : j < xs.length)).mp (he.trans hfirst.symm)
      rw [hnx.idxOf_getElem] at hh
      omega
    have hjb : xs[j]'(by omega) ≠ b := by
      intro he
      have hh := (getElem_eq_iff_eq_idxOf hnx (List.getElem_mem (by omega : K < xs.length))
        (by omega : j < xs.length)).mp (he.trans hlast.symm)
      rw [hnx.idxOf_getElem] at hh
      omega
    have hidx : row.idxOf (xs[j]'(by omega)) = (j + row.idxOf a) % row.length := by
      dsimp only [xs]
      rw [List.getElem_rotate, hn.idxOf_getElem]
    rw [hidx]
    rcases hclosed with h | h | h
    · exact False.elim (hja (by
        dsimp only [xs]
        rw [List.getElem_rotate, getElem_eq_iff_eq_idxOf hn ha]
        exact h))
    · exact False.elim (hjb (by
        dsimp only [xs]
        rw [List.getElem_rotate, getElem_eq_iff_eq_idxOf hn hb]
        exact h))
    · exact h
  have hlabels : ∀ j, (hj : j < K) → g (xs[j]'(by omega)) = g a := by
    intro j
    induction j with
    | zero => intro hj; rw [hfirst]
    | succ j ih =>
      intro hj
      have hprev : row.formPerm.symm (xs[j + 1]'(by omega)) = xs[j]'(by omega) := by
        rw [hperm, Equiv.symm_apply_eq, List.formPerm_apply_getElem xs hnx]
        simp only [Nat.mod_eq_of_lt (show j + 1 < xs.length by omega)]
      have hh := hskip _ (List.mem_rotate.mp (List.getElem_mem (by omega : j + 1 < xs.length)))
        (hinterior (j + 1) (by omega) hj)
      rw [hprev] at hh
      exact hh.symm.trans (ih (by omega))
  let J := (row.idxOf q + row.length - row.idxOf a) % row.length
  have hJ : J < row.length := Nat.mod_lt _ hn0
  have hqrot : xs[J]'(by omega) = q := by
    rw [List.getElem_rotate, getElem_eq_iff_eq_idxOf hn hq]
    exact cyclic_closed_last hi hq'
  have hJK : J < K := by
    have hclosed := (cyclic_closed_iff hi hb' hJ (idxOf_ne_of_ne ha hb hab)).mp
      (Or.inr (Or.inr (by change GM06DrawingData.cyclicBetween _ _ (((row.idxOf q + row.length - row.idxOf a) % row.length + row.idxOf a) % row.length) = true; rw [cyclic_closed_last hi hq']; exact hqmem)))
    have hne : J ≠ K := by
      intro he
      have hqb : q = b := hqrot.symm.trans (by simpa only [he] using hlast)
      subst q
      unfold GM06DrawingData.cyclicBetween at hqmem
      split_ifs at hqmem <;> simp only [decide_eq_true_eq] at hqmem <;> omega
    omega
  rw [← hqrot]
  exact hlabels J hJK

end GraphMinor.GM06
