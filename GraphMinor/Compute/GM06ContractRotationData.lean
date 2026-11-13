module

public import GraphMinor.Compute.GM06SpliceRotations
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-!
# Finite rotation invariants under contraction

The rotation update in Reduction 3 of VI (5.7), page 133, merges
the two endpoint rows and empties the retired row. Its four slices
are a permutation of the two old rows with the chosen ends removed.
Thus it introduces no duplicate word and preserves disjointness
between vertex rows. Every other word still belongs to exactly its
old vertex, except that the retired vertex is replaced by the
retained one. These are the finite incidence invariants needed
when the contraction command is repeated.
-/

public section
namespace GraphMinor.Compute

private theorem mem_eraseIdx_iff_of_nodup {xs : List ℕ} (hn : xs.Nodup)
    {p : ℕ} (hp : p < xs.length) (v : ℕ) :
    v ∈ xs.eraseIdx p ↔ v ∈ xs ∧ v ≠ xs[p] := by
  constructor
  · intro hv
    obtain ⟨j, hj, hjp, hjv⟩ := List.mem_eraseIdx_iff_getElem.mp hv
    refine ⟨List.mem_of_mem_eraseIdx hv, ?_⟩
    intro heq
    exact hjp (hn.eq_of_getElem_eq hj hp (hjv.trans heq))
  · rintro ⟨hv, hne⟩
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hv
    exact List.mem_eraseIdx_iff_getElem.mpr ⟨j, hj, (by intro h; subst j; exact hne hjv.symm), hjv⟩

/-- The splice has precisely the words of the two rows after
removing their selected ends, with only their order changed. -/
theorem gm06SplicedRotation_perm_erase (xs ys : List ℕ) (p q : ℕ) :
    (gm06SplicedRotation xs ys p q).Perm (xs.eraseIdx p ++ ys.eraseIdx q) := by
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ]
  have hmove := (List.perm_append_comm (l₁ := ys.drop (q + 1) ++ ys.take q)
    (l₂ := xs.drop (p + 1))).append_left (xs.take p)
  have hswap := (List.perm_append_comm (l₁ := ys.drop (q + 1))
    (l₂ := ys.take q)).append_left (xs.take p ++ xs.drop (p + 1))
  have hswap' := hswap
  simp only [List.append_assoc] at hswap'
  simpa only [gm06SplicedRotation, List.append_assoc] using hmove.trans hswap'

/-- Membership in a splice removes exactly its two selected words. -/
theorem gm06SplicedRotation_mem_iff {xs ys : List ℕ} (hx : xs.Nodup) (hy : ys.Nodup)
    {p q : ℕ} (hp : p < xs.length) (hq : q < ys.length) (v : ℕ) :
    v ∈ gm06SplicedRotation xs ys p q ↔
      (v ∈ xs ∧ v ≠ xs[p]) ∨ (v ∈ ys ∧ v ≠ ys[q]) := by
  rw [(gm06SplicedRotation_perm_erase xs ys p q).mem_iff, List.mem_append,
    mem_eraseIdx_iff_of_nodup hx hp, mem_eraseIdx_iff_of_nodup hy hq]

/-- Disjoint duplicate-free endpoint rows give a duplicate-free splice. -/
theorem gm06SplicedRotation_nodup {xs ys : List ℕ} (hx : xs.Nodup) (hy : ys.Nodup)
    (hxy : List.Disjoint xs ys) (p q : ℕ) : (gm06SplicedRotation xs ys p q).Nodup := by
  apply (gm06SplicedRotation_perm_erase xs ys p q).nodup_iff.mpr
  apply (hx.eraseIdx p).append (hy.eraseIdx q)
  intro v hv hvs
  exact hxy (List.mem_of_mem_eraseIdx hv) (List.mem_of_mem_eraseIdx hvs)

/-- The two actual row writes of the contraction command. -/
@[expose] def gm06ContractRotationRows (rows : List (List ℕ)) (a b d e : ℕ) : List (List ℕ) :=
  (rows.set a (gm06SplicedRotation (rows[a]?.getD []) (rows[b]?.getD [])
    ((rows[a]?.getD []).idxOf d) ((rows[b]?.getD []).idxOf e))).set b []

/-- The row-label count is unchanged by the contraction. -/
theorem gm06ContractRotationRows_length (rows : List (List ℕ)) (a b d e : ℕ) :
    (gm06ContractRotationRows rows a b d e).length = rows.length := by
  simp only [gm06ContractRotationRows, List.length_set]

/-- A row is empty at the retired vertex, spliced at the retained
vertex and unchanged at every other vertex. -/
theorem gm06ContractRotationRows_getElem (rows : List (List ℕ)) (a b d e : ℕ)
    {j : ℕ} (hj : j < rows.length) :
    (gm06ContractRotationRows rows a b d e)[j]'(by rw [gm06ContractRotationRows_length]; exact hj) =
      if b = j then [] else if a = j then
        gm06SplicedRotation (rows[a]?.getD []) (rows[b]?.getD [])
          ((rows[a]?.getD []).idxOf d) ((rows[b]?.getD []).idxOf e)
      else rows[j] := by
  simp only [gm06ContractRotationRows, List.getElem_set]

/-- The row update preserves both uniqueness within each rotation
and disjointness between different vertex rotations. -/
theorem gm06ContractRotationRows_nodup_disjoint
    (rows : List (List ℕ)) (a b d e : ℕ) (ha : a < rows.length) (hb : b < rows.length) (hab : a ≠ b)
    (hnd : ∀ j : Fin rows.length, rows[j.val].Nodup)
    (hdisj : ∀ j l : Fin rows.length, j ≠ l → List.Disjoint rows[j.val] rows[l.val]) :
    let updated := gm06ContractRotationRows rows a b d e
    (∀ j : Fin updated.length, updated[j.val].Nodup) ∧
      ∀ j l : Fin updated.length, j ≠ l → List.Disjoint updated[j.val] updated[l.val] := by
  let merged := gm06SplicedRotation rows[a] rows[b] (rows[a].idxOf d) (rows[b].idxOf e)
  have hm : merged.Nodup := gm06SplicedRotation_nodup (hnd ⟨a, ha⟩) (hnd ⟨b, hb⟩)
    (hdisj ⟨a, ha⟩ ⟨b, hb⟩ (by intro h; exact hab (congrArg Fin.val h))) _ _
  have hrow : ∀ j : Fin (gm06ContractRotationRows rows a b d e).length,
      (gm06ContractRotationRows rows a b d e)[j.val] =
        if b = j.val then [] else if a = j.val then merged else rows[j.val]'(by
          exact Nat.lt_of_lt_of_eq j.isLt (gm06ContractRotationRows_length rows a b d e)) := by
    intro j
    rw [gm06ContractRotationRows_getElem rows a b d e
      (Nat.lt_of_lt_of_eq j.isLt (gm06ContractRotationRows_length rows a b d e))]
    simp only [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.getD_some, merged]
  have hmem : ∀ v ∈ merged, v ∈ rows[a] ∨ v ∈ rows[b] := fun v hv => gm06SplicedRotation_mem hv
  have hoff : ∀ (j : Fin rows.length), j.val ≠ a → j.val ≠ b → List.Disjoint merged rows[j.val] := by
    intro j hja hjb v hv hjv
    rcases hmem v hv with hva | hvb
    · exact hdisj ⟨a, ha⟩ j (by intro h; exact hja (congrArg Fin.val h).symm) hva hjv
    · exact hdisj ⟨b, hb⟩ j (by intro h; exact hjb (congrArg Fin.val h).symm) hvb hjv
  constructor
  · intro j
    rw [hrow]
    split
    · exact List.nodup_nil
    · split
      · exact hm
      · exact hnd ⟨j.val, Nat.lt_of_lt_of_eq j.isLt (gm06ContractRotationRows_length rows a b d e)⟩
  · intro j l hjl
    have hj : j.val < rows.length := Nat.lt_of_lt_of_eq j.isLt (gm06ContractRotationRows_length rows a b d e)
    have hl : l.val < rows.length := Nat.lt_of_lt_of_eq l.isLt (gm06ContractRotationRows_length rows a b d e)
    rw [hrow, hrow]
    by_cases hbj : b = j.val
    · simp only [hbj, ite_true]; exact fun _ hv => False.elim (List.not_mem_nil hv)
    by_cases hbl : b = l.val
    · simp only [hbl, ite_true]; exact fun _ _ hv => False.elim (List.not_mem_nil hv)
    simp only [hbj, hbl, ite_false]
    by_cases haj : a = j.val
    · have hal : a ≠ l.val := fun h => hjl (Fin.ext (haj.symm.trans h))
      rw [ite_eq_left haj, ite_eq_right hal]
      exact hoff ⟨l.val, hl⟩ (Ne.symm hal) (Ne.symm hbl)
    by_cases hal : a = l.val
    · rw [ite_eq_right haj, ite_eq_left hal]
      exact fun v hv hm => hoff ⟨j.val, hj⟩ (Ne.symm haj) (Ne.symm hbj) hm hv
    rw [ite_eq_right haj, ite_eq_right hal]
    exact hdisj ⟨j.val, hj⟩ ⟨l.val, hl⟩ (by intro h; exact hjl (Fin.ext (congrArg (fun z : Fin rows.length => z.val) h)))

/-- For a retained word, contraction replaces its old source b
by a and preserves every other source. This uses only the supplied
row incidence and the two selected end words. -/
theorem gm06ContractRotationRows_incidence
    (rows : List (List ℕ)) (a b d e w source : ℕ)
    (ha : a < rows.length) (hb : b < rows.length) (hab : a ≠ b)
    (hnd : ∀ j : Fin rows.length, rows[j.val].Nodup)
    (hd : d ∈ rows[a]) (he : e ∈ rows[b]) (hwd : w ≠ d) (hwe : w ≠ e)
    (hsource : ∀ j : Fin rows.length, w ∈ rows[j.val] ↔ source = j.val)
    (j : Fin rows.length) :
    w ∈ (gm06ContractRotationRows rows a b d e)[j.val]'(by rw [gm06ContractRotationRows_length]; exact j.isLt) ↔
      (if source = b then a else source) = j.val := by
  rw [gm06ContractRotationRows_getElem rows a b d e j.isLt]
  have hmerge : w ∈ gm06SplicedRotation (rows[a]?.getD []) (rows[b]?.getD [])
      ((rows[a]?.getD []).idxOf d) ((rows[b]?.getD []).idxOf e) ↔ source = a ∨ source = b := by
    simp only [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.getD_some]
    have hpd : rows[a][rows[a].idxOf d]'(List.idxOf_lt_length_iff.mpr hd) = d :=
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hd)
    have hqe : rows[b][rows[b].idxOf e]'(List.idxOf_lt_length_iff.mpr he) = e :=
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr he)
    rw [gm06SplicedRotation_mem_iff (hnd ⟨a, ha⟩) (hnd ⟨b, hb⟩)
      (List.idxOf_lt_length_iff.mpr hd) (List.idxOf_lt_length_iff.mpr he), hpd, hqe]
    exact (or_congr (and_iff_left hwd) (and_iff_left hwe)).trans
      (or_congr (hsource ⟨a, ha⟩) (hsource ⟨b, hb⟩))
  by_cases hbj : b = j.val
  · rw [ite_eq_left hbj]
    simp only [List.not_mem_nil, false_iff]
    by_cases hsb : source = b <;> simp only [hsb, ite_true, ite_false] <;> omega
  · rw [ite_eq_right hbj]
    by_cases haj : a = j.val
    · rw [ite_eq_left haj, hmerge]
      by_cases hsb : source = b
      · rw [ite_eq_left hsb]
        exact iff_of_true (Or.inr hsb) haj
      · rw [ite_eq_right hsb]
        constructor
        · rintro (hsa | hsb')
          · exact hsa.trans haj
          · exact False.elim (hsb hsb')
        · intro hs
          exact Or.inl (hs.trans haj.symm)
    · rw [ite_eq_right haj, hsource j]
      by_cases hsb : source = b <;> simp only [hsb, ite_true, ite_false] <;> omega

end GraphMinor.Compute
