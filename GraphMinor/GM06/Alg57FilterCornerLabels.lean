module

public import GraphMinor.GM06.Alg57FilterBlock
import Mathlib.Data.List.Chain

/-!
# Corner labels when a row is filtered

The local comparison in Lemma 10 of the proof of VI (5.7), page 133,
removes nonlinkage ends. The two adjacent corners of each removed
end have the same region in the comparison drawing. Skipping those
ends therefore preserves the region of the predecessor of every
retained end. The proof scans the intervening finite row segment.
-/

public section
namespace GraphMinor.GM06

private theorem head_filter_label {α β : Type*} (keep : α → Bool) (g : α → β)
    (xs : List α) (last : α)
    (hc : List.IsChain (fun a b => keep a = false → g a = g b) (xs ++ [last])) :
    g ((xs.filter keep).headD last) = g (xs.headD last) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hk : keep a with
    | true => simp only [List.filter_cons_of_pos hk, List.headD_cons]
    | false =>
      rw [List.filter_cons_of_neg (by simp only [hk, Bool.false_eq_true, not_false_eq_true]), List.headD_cons]
      cases xs with
      | nil =>
        have hh := (List.isChain_cons_cons.mp hc).1 hk
        exact hh.symm
      | cons b xs =>
        obtain ⟨hab, hrest⟩ := List.isChain_cons_cons.mp hc
        exact (ih hrest).trans (hab hk).symm

/-- A row followed by its head follows its form permutation. -/
theorem formPerm_closed_chain {α : Type*} [DecidableEq α] (a : α) (xs : List α)
    (hn : (a :: xs).Nodup) :
    List.IsChain (fun x y => (a :: xs).formPerm x = y) ((a :: xs) ++ [a]) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi0 : i < (a :: xs).length := by
    simp only [List.length_append, List.length_singleton] at hi
    omega
  rw [List.getElem_append_left hi0, List.formPerm_apply_getElem _ hn]
  by_cases hi1 : i + 1 < (a :: xs).length
  · rw [List.getElem_append_left hi1]
    simp only [Nat.mod_eq_of_lt hi1]
  · have heq : i + 1 = (a :: xs).length := by omega
    rw [List.getElem_append_right (by omega)]
    simp only [heq, Nat.mod_self, Nat.sub_self, List.getElem_cons_zero]

/-- When deleting an end preserves a label across its two adjacent
corners, the filtered successor has the same label as the old one
at every retained end. -/
theorem formPerm_filter_label {α β : Type*} [DecidableEq α]
    (row : List α) (hn : row.Nodup) (keep : α → Bool) (g : α → β)
    (hskip : ∀ d ∈ row, keep d = false → g (row.formPerm d) = g d)
    {d : α} (hd : d ∈ row) (hkeep : keep d = true) :
    g ((row.filter keep).formPerm d) = g (row.formPerm d) := by
  obtain ⟨before, after, hrow⟩ := List.mem_iff_append.mp hd
  let rotated := d :: (after ++ before)
  have hr : row ~r rotated := by
    rw [hrow]
    exact List.isRotated_append
  have hnr : rotated.Nodup := hr.perm.nodup_iff.mp hn
  have hp : row.formPerm = rotated.formPerm := List.formPerm_eq_of_isRotated hn hr
  have hrf : row.filter keep ~r rotated.filter keep := by
    rw [hrow]
    simp only [List.filter_append, rotated, List.filter_cons_of_pos hkeep]
    exact List.isRotated_append
  have hpf : (row.filter keep).formPerm = (rotated.filter keep).formPerm :=
    List.formPerm_eq_of_isRotated (hn.filter keep) hrf
  have hchain := formPerm_closed_chain d (after ++ before) hnr
  have hlabels : List.IsChain (fun a b => keep a = false → g a = g b)
      (rotated ++ [d]) := by
    apply hchain.imp_of_mem_imp
    intro a b ha _ hab hk
    have ham : a ∈ row := by
      rcases List.mem_append.mp ha with ha | ha
      · exact hr.perm.mem_iff.mpr ha
      · have had : a = d := List.mem_singleton.mp ha
        exact had ▸ hd
    rw [← hab, ← hp]
    exact (hskip a ham hk).symm
  have htail : List.IsChain (fun a b => keep a = false → g a = g b) ((after ++ before) ++ [d]) :=
    hlabels.tail
  have hh := head_filter_label keep g (after ++ before) d htail
  rw [hpf, hp]
  change g (((d :: (after ++ before)).filter keep).formPerm d) =
    g ((d :: (after ++ before)).formPerm d)
  rw [List.filter_cons_of_pos hkeep]
  cases ht : after ++ before with
  | nil => simp only [List.filter_nil, List.formPerm_singleton, Equiv.Perm.one_apply]
  | cons a rest =>
    have hnext : (d :: a :: rest).formPerm d = a := List.formPerm_apply_head _ _ _ (ht ▸ hnr)
    rw [hnext]
    cases hf : (a :: rest).filter keep with
    | nil =>
      have he : g d = g a := by simpa only [ht, hf, List.headD_nil, List.headD_cons] using hh
      simpa only [hf, List.formPerm_singleton, Equiv.Perm.one_apply] using he
    | cons b bs =>
      have hnfilter : (d :: b :: bs).Nodup := by
        simpa only [rotated, ht, List.filter_cons_of_pos hkeep, hf] using hnr.filter keep
      rw [List.formPerm_apply_head _ _ _ hnfilter]
      simpa only [ht, hf, List.headD_cons] using hh

/-- The predecessor version: deleting ends merges their adjacent
corner labels without changing the label of a retained predecessor. -/
theorem formPerm_filter_symm_label {α β : Type*} [DecidableEq α]
    (row : List α) (hn : row.Nodup) (keep : α → Bool) (g : α → β)
    (hskip : ∀ d ∈ row, keep d = false → g (row.formPerm.symm d) = g d)
    {d : α} (hd : d ∈ row) (hkeep : keep d = true) :
    g ((row.filter keep).formPerm.symm d) = g (row.formPerm.symm d) := by
  have hh := formPerm_filter_label row.reverse (List.nodup_reverse.mpr hn) keep g
    (fun a ha hk => by
      simpa only [List.formPerm_reverse, Equiv.Perm.coe_inv] using
        (hskip a (List.mem_reverse.mp ha) hk)) (List.mem_reverse.mpr hd) hkeep
  simpa only [List.filter_reverse, List.formPerm_reverse, Equiv.Perm.coe_inv] using hh

end GraphMinor.GM06
