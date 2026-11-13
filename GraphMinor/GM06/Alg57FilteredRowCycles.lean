module

public import GraphMinor.GM06.Alg57FilterBlock

/-!
# The two- and three-end comparison rotations

The linkage-and-cuff comparison in Lemma 10 of VI (5.7), page 133,
retains two ends at an interior linkage vertex and three at an end.
Filtering preserves any already consecutive retained pair. The two
or three retained ends then determine the whole cyclic successor.
-/

public section
namespace GraphMinor.GM06

/-- Filtering preserves a retained end's successor whenever that
successor is itself retained. -/
theorem formPerm_filter_apply_of_keep_next {α : Type*} [DecidableEq α]
    (row : List α) (hn : row.Nodup) (keep : α → Bool) {d : α}
    (hd : d ∈ row) (hkd : keep d = true) (hkn : keep (row.formPerm d) = true) :
    (row.filter keep).formPerm d = row.formPerm d := by
  obtain ⟨before, after, hrow⟩ := List.mem_iff_append.mp hd
  let rotated := d :: (after ++ before)
  have hr : row ~r rotated := by rw [hrow]; exact List.isRotated_append
  have hnr : rotated.Nodup := hr.perm.nodup_iff.mp hn
  have hp := List.formPerm_eq_of_isRotated hn hr
  have hrf : row.filter keep ~r rotated.filter keep := by
    rw [hrow]
    simp only [List.filter_append, rotated, List.filter_cons_of_pos hkd]
    exact List.isRotated_append
  have hpf := List.formPerm_eq_of_isRotated (hn.filter keep) hrf
  rw [hp] at hkn ⊢
  rw [hpf]
  change ((d :: (after ++ before)).filter keep).formPerm d = (d :: (after ++ before)).formPerm d
  rw [List.filter_cons_of_pos hkd]
  cases ht : after ++ before with
  | nil => simp
  | cons a rest =>
    have hnext := List.formPerm_apply_head d a rest (ht ▸ hnr)
    have hka : keep a = true := by simpa only [rotated, ht, hnext] using hkn
    rw [hnext, List.filter_cons_of_pos hka]
    exact List.formPerm_apply_head _ _ _ (by
      simpa only [rotated, ht, List.filter_cons_of_pos hkd, List.filter_cons_of_pos hka]
        using hnr.filter keep)

private theorem two_le_length_of_mem_ne {α : Type*} [DecidableEq α]
    (row : List α) {a b : α} (ha : a ∈ row) (hb : b ∈ row) (hab : a ≠ b) : 2 ≤ row.length := by
  have hn : [a, b].Nodup := by simp [hab]
  have hs := hn.subperm (l₂ := row) (fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha
    · exact hb)
  simpa only [List.length_cons, List.length_nil] using hs.length_le

/-- A row consisting of two distinct ends swaps them. -/
theorem formPerm_of_two_ends {α : Type*} [DecidableEq α]
    (row : List α) (hn : row.Nodup) {a b : α} (hab : a ≠ b)
    (ha : a ∈ row) (hb : b ∈ row) (hmem : ∀ c ∈ row, c = a ∨ c = b) :
    row.formPerm a = b ∧ row.formPerm b = a := by
  have hlen := two_le_length_of_mem_ne row ha hb hab
  have hna := (List.formPerm_apply_mem_ne_self_iff row hn a ha).mpr hlen
  have hnb := (List.formPerm_apply_mem_ne_self_iff row hn b hb).mpr hlen
  exact ⟨(hmem _ (List.formPerm_apply_mem_of_mem ha)).resolve_left hna,
    (hmem _ (List.formPerm_apply_mem_of_mem hb)).resolve_right hnb⟩

/-- In a row of three distinct ends, one prescribed successor fixes
the other two. This reads the cuff adjacency after filtering. -/
theorem formPerm_of_three_ends {α : Type*} [DecidableEq α]
    (row : List α) (hn : row.Nodup) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ row) (hb : b ∈ row) (hc : c ∈ row)
    (hmem : ∀ d ∈ row, d = a ∨ d = b ∨ d = c) (hnext : row.formPerm b = c) :
    row.formPerm a = b ∧ row.formPerm c = a := by
  have hlen := two_le_length_of_mem_ne row ha hb hab
  have hna := (List.formPerm_apply_mem_ne_self_iff row hn a ha).mpr hlen
  have hnac : row.formPerm a ≠ c := by
    intro h
    exact hab (row.formPerm.injective (h.trans hnext.symm))
  have habnext : row.formPerm a = b :=
    ((hmem _ (List.formPerm_apply_mem_of_mem ha)).resolve_left hna).resolve_right hnac
  have hncb : row.formPerm c ≠ b := by
    intro h
    exact hac.symm (row.formPerm.injective (h.trans habnext.symm))
  have hncc : row.formPerm c ≠ c := by
    intro h
    exact hbc.symm (row.formPerm.injective (h.trans hnext.symm))
  exact ⟨habnext,
    (hmem _ (List.formPerm_apply_mem_of_mem hc)).resolve_right
      (fun h => h.elim hncb hncc)⟩

end GraphMinor.GM06
