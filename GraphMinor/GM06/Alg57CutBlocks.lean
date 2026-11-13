module

public import GraphMinor.GM06.Alg57FilterBlock
public import GraphMinor.Compute.GM06CutRotations

/-!
# The blocks kept by the copies of a split vertex

The cut of the Word RAM program (`GraphMinor.Compute.gm06CutRotation`) keeps, at each copy of a
linkage vertex, the darts of a closed cyclic interval `[u, w]` of the old row (Section 9 of our
proof of VI (5.7), outlined in `Alg57Algorithm.lean`). Here we show that a filter given by such an
interval is a block of consecutive darts, so `formPerm_filter_symm_of_block` applies
(`formPerm_filter_symm_of_closed`): in the filtered row a kept dart other than `u` has its old
predecessor, and `u` is preceded by `w`.
-/

public section

namespace GraphMinor.GM06

open Equiv GraphMinor.Compute

/-- Positions of a closed cyclic interval `[i, q]` read from `i`: the position `j` steps after
`i` is in the interval exactly when `j` is at most the distance from `i` to `q`. -/
theorem cyclic_closed_iff {n i q j : ℕ} (hi : i < n) (hq : q < n) (hj : j < n) (hiq : i ≠ q) :
    ((j + i) % n = i ∨ (j + i) % n = q ∨
      GM06DrawingData.cyclicBetween i q ((j + i) % n) = true) ↔ j < (q + n - i) % n + 1 := by
  have ht : (j + i) % n = if j + i < n then j + i else j + i - n := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hK : (q + n - i) % n = if i ≤ q then q - i else q + n - i := by
    split_ifs with h
    · rw [show q + n - i = (q - i) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [ht, hK]
  unfold GM06DrawingData.cyclicBetween
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

/-- The end of the interval, read from its start. -/
theorem cyclic_closed_last {n i q : ℕ} (hi : i < n) (hq : q < n) :
    ((q + n - i) % n + i) % n = q := by
  by_cases h : i ≤ q
  · rw [show q + n - i = (q - i) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show q - i < n by omega), Nat.sub_add_cancel h, Nat.mod_eq_of_lt hq]
  · rw [Nat.mod_eq_of_lt (by omega : q + n - i < n), show q + n - i + i = q + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hq]

/-- In a row without repetitions, the entry at `t` is `u` exactly when `t` is the index of `u`. -/
theorem getElem_eq_iff_eq_idxOf {α : Type*} [DecidableEq α] {row : List α} (hn : row.Nodup)
    {u : α} (hu : u ∈ row) {t : ℕ} (ht : t < row.length) : row[t] = u ↔ t = row.idxOf u := by
  constructor
  · rintro rfl
    exact (hn.idxOf_getElem t ht).symm
  · rintro rfl
    exact List.getElem_idxOf _

/-- **A closed cyclic interval is a block.** If `keep` keeps exactly the darts of the closed
interval from `u` to `w ≠ u` of a row without repetitions, then in the filtered row a kept dart
other than `u` has its old predecessor, and `u` is preceded by `w`. -/
theorem formPerm_filter_symm_of_closed {α : Type*} [DecidableEq α] (row : List α)
    (hn : row.Nodup) (keep : α → Bool) {u w : α} (hu : u ∈ row) (hw : w ∈ row) (huw : u ≠ w)
    (hkeep : ∀ d ∈ row, keep d = true ↔ (d = u ∨ d = w ∨
      GM06DrawingData.cyclicBetween (row.idxOf u) (row.idxOf w) (row.idxOf d) = true)) :
    (∀ x ∈ row, keep x = true → x ≠ u →
      (row.filter keep).formPerm.symm x = row.formPerm.symm x) ∧
    (row.filter keep).formPerm.symm u = w := by
  have hiu := List.idxOf_lt_length_of_mem hu
  have hiw := List.idxOf_lt_length_of_mem hw
  have hne : row.idxOf u ≠ row.idxOf w := fun h =>
    huw (by rw [← List.getElem_idxOf hiu, ← List.getElem_idxOf hiw]; simp only [h])
  set n := row.length with hnlen
  have hK1 : 1 ≤ (row.idxOf w + n - row.idxOf u) % n + 1 := by omega
  have hK : (row.idxOf w + n - row.idxOf u) % n + 1 ≤ n := Nat.mod_lt _ (by omega)
  have hp : ∀ (j : ℕ) (hj : j < row.length),
      keep ((row.rotate (row.idxOf u))[j]'(by simpa using hj)) = true ↔
        j < (row.idxOf w + n - row.idxOf u) % n + 1 := by
    intro j hj
    rw [List.getElem_rotate]
    have htn : (j + row.idxOf u) % row.length < row.length := Nat.mod_lt _ (by omega)
    rw [hkeep _ (List.getElem_mem _), getElem_eq_iff_eq_idxOf hn hu htn,
      getElem_eq_iff_eq_idxOf hn hw htn, hn.idxOf_getElem _ htn]
    exact cyclic_closed_iff hiu hiw hj hne
  obtain ⟨h1, h2⟩ := formPerm_filter_symm_of_block row hn keep (row.idxOf u) hK1 hK hp
  have hfirst : (row.rotate (row.idxOf u))[0]'(by simp; omega) = u := by
    rw [List.getElem_rotate]
    simp only [Nat.zero_add]
    rw [getElem_eq_iff_eq_idxOf hn hu, Nat.mod_eq_of_lt hiu]
  have hlast : (row.rotate (row.idxOf u))[(row.idxOf w + n - row.idxOf u) % n + 1 - 1]'
      (by simp; omega) = w := by
    rw [List.getElem_rotate]
    simp only [Nat.add_sub_cancel]
    rw [getElem_eq_iff_eq_idxOf hn hw]
    exact cyclic_closed_last hiu hiw
  refine ⟨fun x hx hkx hxu => ?_, ?_⟩
  · exact h1 x hx hkx (by rw [hfirst]; exact hxu)
  · rw [← hfirst, h2, hlast]

/-- Reading a `formPerm` through a relabelling: if `l.map f = m` and both lists have no
repetitions, then `f` carries predecessors in `l` to predecessors in `m`. -/
theorem map_formPerm_symm {α β : Type*} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hl : l.Nodup) (hm : (l.map f).Nodup) {x : α} (hx : x ∈ l) :
    f (l.formPerm.symm x) = (l.map f).formPerm.symm (f x) := by
  have hfwd : ∀ y ∈ l, (l.map f).formPerm (f y) = f (l.formPerm y) := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    have h1 := List.formPerm_apply_getElem (l.map f) hm j (by simpa using hj)
    simp only [List.getElem_map, List.length_map] at h1
    rw [h1, List.formPerm_apply_getElem l hl j hj]
  have hy : l.formPerm.symm x ∈ l := by
    by_contra hy
    have h := List.formPerm_apply_of_notMem hy
    rw [Equiv.apply_symm_apply] at h
    rw [← h] at hy
    exact hy hx
  rw [Equiv.eq_symm_apply, hfwd _ hy, Equiv.apply_symm_apply]

/-- The test by which the cut of the program keeps a dart at the copy `left` of a split vertex. -/
@[expose] def cutKeep (p : GM06CutPosition) (row : List ℕ) (left : Bool) (d : ℕ) : Bool :=
  decide (d ∈ p.pathEnds) || (gm06CutDartLeft p row d == left)

/-- A copied row is the filtered old row, relabelled. -/
theorem gm06CutRotation_eq_map_filter (p : GM06CutPosition) (row : List ℕ) (left : Bool) :
    gm06CutRotation p row left = (row.filter (cutKeep p row left)).map (gm06CutRowDart p left) :=
  rfl

/-- **The rotation of a copy of a split vertex.** If the copy keeps the closed interval from `u`
to `w ≠ u` of the old row, then the predecessor of a dart `x` of the copy projects to the old
predecessor of the projection of `x`, except that `u` is preceded by `w`. -/
theorem cutRotation_symm_project (p : GM06CutPosition) (row : List ℕ) (left : Bool)
    (hn : row.Nodup) {u w : ℕ} (hu : u ∈ row) (hw : w ∈ row) (huw : u ≠ w)
    (hkeep : ∀ d ∈ row, cutKeep p row left d = true ↔ (d = u ∨ d = w ∨
      GM06DrawingData.cyclicBetween (row.idxOf u) (row.idxOf w) (row.idxOf d) = true))
    {x : ℕ} (hx : x ∈ gm06CutRotation p row left) :
    gm06UncutDart ((gm06CutRotation p row left).formPerm.symm x) =
      if gm06UncutDart x = u then w else row.formPerm.symm (gm06UncutDart x) := by
  have hproj : (gm06CutRotation p row left).map gm06UncutDart = row.filter (cutKeep p row left) :=
    gm06CutRotation_project p row left
  have hnd := gm06CutRotation_nodup p row left hn
  have hmap := map_formPerm_symm _ gm06UncutDart hnd (by rw [hproj]; exact hn.filter _) hx
  rw [hmap, hproj]
  have hux : gm06UncutDart x ∈ row.filter (cutKeep p row left) := by
    rw [← hproj]; exact List.mem_map_of_mem hx
  rw [List.mem_filter] at hux
  obtain ⟨h1, h2⟩ := formPerm_filter_symm_of_closed row hn (cutKeep p row left) hu hw huw hkeep
  split_ifs with h
  · rw [h]; exact h2
  · exact h1 _ hux.1 hux.2 h

/-- Distinct members of a row have distinct indices. -/
theorem idxOf_ne_of_ne {α : Type*} [DecidableEq α] {row : List α} {x y : α} (hx : x ∈ row)
    (hy : y ∈ row) (hxy : x ≠ y) : row.idxOf x ≠ row.idxOf y := fun h =>
  hxy (by rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hx),
    ← List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)]; simp only [h])

/-- The index after `s < n`. -/
theorem succ_mod_cases {n s : ℕ} (hs : s < n) :
    ((s + 1) % n = s + 1 ∧ s + 1 < n) ∨ ((s + 1) % n = 0 ∧ s + 1 = n) := by
  by_cases h : s + 1 < n
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · exact Or.inr ⟨by rw [show s + 1 = n by omega, Nat.mod_self], by omega⟩

/-- The index after `s` is not strictly between `i` and `s`. -/
theorem cyclicBetween_succ_left {n i s : ℕ} (hi : i < n) (hs : s < n) (his : i ≠ s)
    (hit : i ≠ (s + 1) % n) :
    GM06DrawingData.cyclicBetween i s ((s + 1) % n) = false := by
  obtain ⟨ht, h⟩ | ⟨ht, h⟩ := succ_mod_cases hs <;> rw [ht] at hit ⊢ <;>
    unfold GM06DrawingData.cyclicBetween <;>
    split_ifs <;> simp only [decide_eq_false_iff_not] <;> omega

/-- The index before `t` is not strictly between `t` and `i`. -/
theorem cyclicBetween_succ_right {n i s : ℕ} (hi : i < n) (hs : s < n)
    (hit : i ≠ (s + 1) % n) :
    GM06DrawingData.cyclicBetween ((s + 1) % n) i s = false := by
  obtain ⟨ht, h⟩ | ⟨ht, h⟩ := succ_mod_cases hs <;> rw [ht] at hit ⊢ <;>
    unfold GM06DrawingData.cyclicBetween <;>
    split_ifs <;> simp only [decide_eq_false_iff_not] <;> omega

/-- Moving the end `s` of an open interval to the next index `t`. -/
theorem cyclicBetween_not_left {n i s d : ℕ} (hi : i < n) (hs : s < n) (hd : d < n)
    (his : i ≠ s) (hit : i ≠ (s + 1) % n)
    (hdi : d ≠ i) (hds : d ≠ s) (hdt : d ≠ (s + 1) % n) :
    (!GM06DrawingData.cyclicBetween i s d) = GM06DrawingData.cyclicBetween ((s + 1) % n) i d := by
  obtain ⟨ht, h⟩ | ⟨ht, h⟩ := succ_mod_cases hs <;> rw [ht] at hdt hit ⊢ <;>
    apply Bool.eq_iff_iff.mpr <;>
    unfold GM06DrawingData.cyclicBetween <;>
    split_ifs <;> simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

/-- Moving the start `t` of an open interval back to the previous index `s`. -/
theorem cyclicBetween_not_right {n i s d : ℕ} (hi : i < n) (hs : s < n) (hd : d < n)
    (his : i ≠ s) (hit : i ≠ (s + 1) % n)
    (hdi : d ≠ i) (hds : d ≠ s) (hdt : d ≠ (s + 1) % n) :
    (!GM06DrawingData.cyclicBetween ((s + 1) % n) i d) = GM06DrawingData.cyclicBetween i s d := by
  rw [← cyclicBetween_not_left hi hs hd his hit hdi hds hdt, Bool.not_not]

/-! ### The blocks of the three kinds of split vertex -/

section Blocks

variable {row : List ℕ}

local notation "between" => GM06DrawingData.cyclicBetween

/-- At an interior vertex with path ends `a` (back) and `b` (forward), the left copy keeps the
closed interval from `b` to `a`. -/
theorem cutKeep_interior_left {a b : ℕ} :
    ∀ d ∈ row, cutKeep (.interior a b) row true d = true ↔
      (d = b ∨ d = a ∨ between (row.idxOf b) (row.idxOf a) (row.idxOf d) = true) := by
  intro d _
  simp only [cutKeep, GM06CutPosition.pathEnds, gm06CutDartLeft, gm06CutBetween,
    GM06CutPosition.leftBounds, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  tauto

/-- At an interior vertex the right copy keeps the closed interval from `a` to `b`. -/
theorem cutKeep_interior_right {a b : ℕ} (ha : a ∈ row) (hb : b ∈ row) (hab : a ≠ b) :
    ∀ d ∈ row, cutKeep (.interior a b) row false d = true ↔
      (d = a ∨ d = b ∨ between (row.idxOf a) (row.idxOf b) (row.idxOf d) = true) := by
  intro d hd
  simp only [cutKeep, GM06CutPosition.pathEnds, gm06CutDartLeft, gm06CutBetween,
    GM06CutPosition.leftBounds, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  by_cases hda : d = a
  · simp [hda]
  by_cases hdb : d = b
  · simp [hdb]
  rw [gm06CutBetween_complement (idxOf_ne_of_ne ha hb hab) (idxOf_ne_of_ne hd ha hda)
    (idxOf_ne_of_ne hd hb hdb)]
  simp [hda, hdb]

/-- At a start with path end `b` and cuff ends `cp`, `cn`, where `cn` follows `cp` in the row, the
left copy keeps the closed interval from `b` to `cp`. -/
theorem cutKeep_start_left {b cp cn : ℕ} (hb : b ∈ row) (hcp : cp ∈ row) (hcn : cn ∈ row)
    (hbp : b ≠ cp) (hbn : b ≠ cn) (hpn : cp ≠ cn)
    (hnext : row.idxOf cn = (row.idxOf cp + 1) % row.length) :
    ∀ d ∈ row, cutKeep (.start b cp cn) row true d = true ↔
      (d = b ∨ d = cp ∨ between (row.idxOf b) (row.idxOf cp) (row.idxOf d) = true) := by
  intro d hd
  simp only [cutKeep, GM06CutPosition.pathEnds, gm06CutDartLeft, gm06CutBetween,
    GM06CutPosition.leftBounds, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  by_cases hdb : d = b
  · simp [hdb]
  by_cases hdp : d = cp
  · simp [hdp]
  by_cases hdn : d = cn
  · subst hdn
    rw [hnext, cyclicBetween_succ_left (List.idxOf_lt_length_of_mem hb)
      (List.idxOf_lt_length_of_mem hcp) (idxOf_ne_of_ne hb hcp hbp)
      (hnext ▸ idxOf_ne_of_ne hb hcn hbn)]
    simp [hdb, hdp]
  · simp [hdb, hdp, hdn]

/-- At a start the right copy keeps the closed interval from `cn` to `b`. -/
theorem cutKeep_start_right {b cp cn : ℕ} (hb : b ∈ row) (hcp : cp ∈ row) (hcn : cn ∈ row)
    (hbp : b ≠ cp) (hbn : b ≠ cn) (hpn : cp ≠ cn)
    (hnext : row.idxOf cn = (row.idxOf cp + 1) % row.length) :
    ∀ d ∈ row, cutKeep (.start b cp cn) row false d = true ↔
      (d = cn ∨ d = b ∨ between (row.idxOf cn) (row.idxOf b) (row.idxOf d) = true) := by
  intro d hd
  have hib := List.idxOf_lt_length_of_mem hb
  have hip := List.idxOf_lt_length_of_mem hcp
  have hbn' : row.idxOf b ≠ (row.idxOf cp + 1) % row.length := hnext ▸ idxOf_ne_of_ne hb hcn hbn
  simp only [cutKeep, GM06CutPosition.pathEnds, gm06CutDartLeft, gm06CutBetween,
    GM06CutPosition.leftBounds, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  by_cases hdb : d = b
  · simp [hdb]
  by_cases hdp : d = cp
  · subst hdp
    rw [hnext, cyclicBetween_succ_right hib hip hbn']
    simp [hdb, hpn]
  by_cases hdn : d = cn
  · simp [hdn, Ne.symm hpn]
  · rw [hnext, ← cyclicBetween_not_left hib hip (List.idxOf_lt_length_of_mem hd)
      (idxOf_ne_of_ne hb hcp hbp) hbn' (idxOf_ne_of_ne hd hb hdb) (idxOf_ne_of_ne hd hcp hdp)
      (hnext ▸ idxOf_ne_of_ne hd hcn hdn)]
    simp [hdb, hdp, hdn]

/-- At a terminal with path end `a` and cuff ends `cp`, `cn`, where `cp` follows `cn` in the
row, the left copy keeps the closed interval from `cp` to `a`. -/
theorem cutKeep_terminal_left {a cp cn : ℕ} (ha : a ∈ row) (hcp : cp ∈ row) (hcn : cn ∈ row)
    (hap : a ≠ cp) (han : a ≠ cn) (hpn : cp ≠ cn)
    (hnext : row.idxOf cp = (row.idxOf cn + 1) % row.length) :
    ∀ d ∈ row, cutKeep (.terminal a cp cn) row true d = true ↔
      (d = cp ∨ d = a ∨ between (row.idxOf cp) (row.idxOf a) (row.idxOf d) = true) := by
  intro d hd
  simp only [cutKeep, GM06CutPosition.pathEnds, gm06CutDartLeft, gm06CutBetween,
    GM06CutPosition.leftBounds, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  by_cases hda : d = a
  · simp [hda]
  by_cases hdp : d = cp
  · simp [hdp]
  by_cases hdn : d = cn
  · subst hdn
    rw [hnext, cyclicBetween_succ_right (List.idxOf_lt_length_of_mem ha)
      (List.idxOf_lt_length_of_mem hcn) (hnext ▸ idxOf_ne_of_ne ha hcp hap)]
    simp [hda, hdp]
  · simp [hda, hdp, hdn]

/-- At a terminal the right copy keeps the closed interval from `a` to `cn`. -/
theorem cutKeep_terminal_right {a cp cn : ℕ} (ha : a ∈ row) (hcp : cp ∈ row) (hcn : cn ∈ row)
    (hap : a ≠ cp) (han : a ≠ cn) (hpn : cp ≠ cn)
    (hnext : row.idxOf cp = (row.idxOf cn + 1) % row.length) :
    ∀ d ∈ row, cutKeep (.terminal a cp cn) row false d = true ↔
      (d = a ∨ d = cn ∨ between (row.idxOf a) (row.idxOf cn) (row.idxOf d) = true) := by
  intro d hd
  have hia := List.idxOf_lt_length_of_mem ha
  have hin := List.idxOf_lt_length_of_mem hcn
  have hap' : row.idxOf a ≠ (row.idxOf cn + 1) % row.length := hnext ▸ idxOf_ne_of_ne ha hcp hap
  simp only [cutKeep, GM06CutPosition.pathEnds, gm06CutDartLeft, gm06CutBetween,
    GM06CutPosition.leftBounds, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  by_cases hda : d = a
  · simp [hda]
  by_cases hdp : d = cp
  · subst hdp
    rw [hnext, cyclicBetween_succ_left hia hin (idxOf_ne_of_ne ha hcn han) hap']
    simp [hda, hpn]
  by_cases hdn : d = cn
  · simp [hdn, Ne.symm hpn]
  · rw [hnext, ← cyclicBetween_not_right hia hin (List.idxOf_lt_length_of_mem hd)
      (idxOf_ne_of_ne ha hcn han) hap' (idxOf_ne_of_ne hd ha hda) (idxOf_ne_of_ne hd hcn hdn)
      (hnext ▸ idxOf_ne_of_ne hd hcp hdp)]
    simp [hda, hdp, hdn]

end Blocks

end GraphMinor.GM06
