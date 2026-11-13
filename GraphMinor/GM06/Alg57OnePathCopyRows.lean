module

public import GraphMinor.GM06.Alg57CutBlocks
public import GraphMinor.GM06.Alg57CutFaceLink
public import GraphMinor.GM06.Alg57CutOrbitAvoidLast
import GraphMinor.Compute.GM06FaceRowsProgram
import GraphMinor.Compute.GM06CutRowsFacts
import all GraphMinor.GM06.Alg57CutFaceLink

/-!
# The darts kept by a copy, as rotation iterates

The lifted incidence (`Alg57OnePathFaceForm`) speaks of blocks of darts `b, R.rot b, …` before `a`.
The copies of a split vertex in the cut rows of the program keep a closed cyclic interval `[b, a]`
of the old row (`cutKeep_interior_left` and its relatives). Here we turn intervals into iterates of
the row permutation: a dart is in `[b, a]` but is not `a` exactly when it is `formPerm^[i] b` for
some `i` such that no `formPerm^[j] b` with `j ≤ i` is `a` (`block_iff_iterate`). With the
projection of the copied row (`gm06CutRotation_project`) this reads: the darts of a copy other than
its last dart project onto the iterates from its first dart before its last dart
(`copy_project_iff_iterate`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Equiv GraphMinor.Compute

local notation "between" => GM06DrawingData.cyclicBetween

/-- A number below `2 n` reduced mod `n`. -/
theorem mod_two_cases {m n : ℕ} (h : m < 2 * n) :
    (m % n = m ∧ m < n) ∨ (m % n = m - n ∧ n ≤ m) := by
  by_cases hm : m < n
  · exact Or.inl ⟨Nat.mod_eq_of_lt hm, hm⟩
  · refine Or.inr ⟨?_, by omega⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **A closed cyclic interval without its last end, as iterates.** In a row without repeats, a
dart is `u` or strictly between `u` and `w` exactly when it is `formPerm^[i] u` for an `i` such that
no `formPerm^[j] u` with `j ≤ i` is `w`. -/
theorem block_iff_iterate {row : List ℕ} (hn : row.Nodup) {u w : ℕ} (hu : u ∈ row) (hw : w ∈ row)
    (huw : u ≠ w) (d : ℕ) :
    (d ∈ row ∧ (d = u ∨ between (row.idxOf u) (row.idxOf w) (row.idxOf d) = true)) ↔
      ∃ i, (∀ j ≤ i, row.formPerm^[j] u ≠ w) ∧ row.formPerm^[i] u = d := by
  set n := row.length with hnlen
  have hiu : row.idxOf u < n := List.idxOf_lt_length_of_mem hu
  have hiw : row.idxOf w < n := List.idxOf_lt_length_of_mem hw
  have hne : row.idxOf u ≠ row.idxOf w := idxOf_ne_of_ne hu hw huw
  -- the iterates are the entries after `u`
  have hit : ∀ j, row.formPerm^[j] u = row[(row.idxOf u + j) % n]'(Nat.mod_lt _ (by omega)) := by
    intro j
    rw [← Equiv.Perm.coe_pow]
    conv_lhs => rw [← List.getElem_idxOf hiu]
    exact List.formPerm_pow_apply_getElem row hn j _ hiu
  have heq : ∀ (s : ℕ) (hs : s < n) (x : ℕ), x ∈ row → (row[s] = x ↔ s = row.idxOf x) := by
    intro s hs x hx
    have hx' := List.idxOf_lt_length_of_mem hx
    constructor
    · intro h
      exact hn.getElem_inj_iff.mp (h.trans (List.getElem_idxOf hx').symm)
    · rintro rfl
      exact List.getElem_idxOf hx'
  constructor
  · rintro ⟨hd, rfl | hb⟩
    · exact ⟨0, fun j hj => by
        rw [Nat.le_zero.mp hj]; exact huw, rfl⟩
    · have hid : row.idxOf d < n := List.idxOf_lt_length_of_mem hd
      have hdu : row.idxOf d ≠ row.idxOf u := by
        intro h; rw [h] at hb; unfold GM06DrawingData.cyclicBetween at hb
        split_ifs at hb <;> simp only [decide_eq_true_eq] at hb <;> omega
      refine ⟨if row.idxOf u < row.idxOf d then row.idxOf d - row.idxOf u
        else row.idxOf d + n - row.idxOf u, ?_, ?_⟩
      · intro j hj hjw
        rw [hit, heq _ _ w hw] at hjw
        unfold GM06DrawingData.cyclicBetween at hb
        rcases mod_two_cases (m := row.idxOf u + j) (n := n) (by split_ifs at hj <;> omega)
          with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hjw <;>
          split_ifs at hb hj <;> simp only [decide_eq_true_eq] at hb <;> omega
      · rw [hit, heq _ _ d hd]
        rcases mod_two_cases (m := row.idxOf u + (if row.idxOf u < row.idxOf d then
          row.idxOf d - row.idxOf u else row.idxOf d + n - row.idxOf u)) (n := n)
          (by split_ifs <;> omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> split_ifs at h2 ⊢ <;>
          omega
  · rintro ⟨i, hi, rfl⟩
    -- the first iterate that is `w`
    set j₀ := if row.idxOf u < row.idxOf w then row.idxOf w - row.idxOf u
      else row.idxOf w + n - row.idxOf u with hj₀
    have hj₀w : row.formPerm^[j₀] u = w := by
      rw [hit, heq _ _ w hw]
      rcases mod_two_cases (m := row.idxOf u + j₀) (n := n) (by rw [hj₀]; split_ifs <;> omega)
        with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> rw [hj₀] at h2 ⊢ <;> split_ifs at h2 ⊢ <;> omega
    have hij : i < j₀ := by
      by_contra h
      exact hi j₀ (by omega) hj₀w
    have hmem : row[(row.idxOf u + i) % n]'(Nat.mod_lt _ (by omega)) ∈ row := List.getElem_mem _
    refine ⟨by rw [hit]; exact hmem, ?_⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · left; rfl
    right
    have hidx : row.idxOf (row[(row.idxOf u + i) % n]'(Nat.mod_lt _ (by omega))) =
        (row.idxOf u + i) % n :=
      ((heq _ _ _ hmem).mp rfl).symm
    rw [hit, hidx]
    unfold GM06DrawingData.cyclicBetween
    rcases mod_two_cases (m := row.idxOf u + i) (n := n) (by rw [hj₀] at hij; split_ifs at hij <;> omega)
      with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> rw [hj₀] at hij <;> split_ifs at hij ⊢ <;>
      simp only [decide_eq_true_eq] <;> omega

/-- **The darts of a copy other than its last dart, projected.** If a copy of a split vertex keeps
the closed interval from `u` to `w ≠ u` of the old row, then the old darts under its darts other
than the copy of `w` are the iterates `formPerm^[i] u` taken before `w` is reached. -/
theorem copy_project_iff_iterate (p : GM06CutPosition) {row : List ℕ} (left : Bool)
    (hn : row.Nodup) {u w : ℕ} (hu : u ∈ row) (hw : w ∈ row) (huw : u ≠ w)
    (hkeep : ∀ d ∈ row, cutKeep p row left d = true ↔ (d = u ∨ d = w ∨
      between (row.idxOf u) (row.idxOf w) (row.idxOf d) = true)) (d : ℕ) :
    (∃ q ∈ gm06CutRotation p row left, q ≠ gm06CutRowDart p left w ∧ gm06UncutDart q = d) ↔
      ∃ i, (∀ j ≤ i, row.formPerm^[j] u ≠ w) ∧ row.formPerm^[i] u = d := by
  rw [← block_iff_iterate hn hu hw huw d, gm06CutRotation_eq_map_filter]
  constructor
  · rintro ⟨q, hq, hqw, rfl⟩
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hq
    rw [gm06CutRowDart_project]
    obtain ⟨hd'r, hk⟩ := List.mem_filter.mp hd'
    have hdw : d' ≠ w := fun h => hqw (h ▸ rfl)
    refine ⟨hd'r, ?_⟩
    rcases (hkeep d' hd'r).mp hk with h | h | h
    exacts [Or.inl h, absurd h hdw, Or.inr h]
  · rintro ⟨hd, hb⟩
    have hdw : d ≠ w := by
      rintro rfl
      rcases hb with h | h
      · exact huw h.symm
      · unfold GM06DrawingData.cyclicBetween at h
        split_ifs at h <;> simp only [decide_eq_true_eq] at h <;> omega
    have hk : cutKeep p row left d = true := (hkeep d hd).mpr (by tauto)
    refine ⟨gm06CutRowDart p left d, List.mem_map_of_mem (List.mem_filter.mpr ⟨hd, hk⟩), ?_,
      gm06CutRowDart_project p left d⟩
    intro h
    exact hdw (by simpa only [gm06CutRowDart_project] using congrArg gm06UncutDart h)

/-- The half-open blocks `[first, last)` of the two copies of a split vertex are disjoint. -/
theorem copy_blocks_disjoint {p : GM06CutPosition} {row : List ℕ} (h : CutBlockOK p row)
    {d : ℕ} (hd : d ∈ row)
    (h1 : d = cutFirst p true ∨
      between (row.idxOf (cutFirst p true)) (row.idxOf (cutLast p true)) (row.idxOf d) = true)
    (h2 : d = cutFirst p false ∨
      between (row.idxOf (cutFirst p false)) (row.idxOf (cutLast p false)) (row.idxOf d) = true) :
    False := by
  have e : ∀ y ∈ row, d = y ↔ row.idxOf d = row.idxOf y := fun y hy =>
    ⟨fun h => h ▸ rfl, fun h => (List.idxOf_inj hd).mp h⟩
  have hid := List.idxOf_lt_length_of_mem hd
  cases p with
  | interior a b =>
    obtain ⟨ha, hb, hab⟩ : a ∈ row ∧ b ∈ row ∧ a ≠ b := h
    have hia := List.idxOf_lt_length_of_mem ha
    have hib := List.idxOf_lt_length_of_mem hb
    have hne := idxOf_ne_of_ne ha hb hab
    simp only [cutFirst, cutLast, e _ ha, e _ hb] at h1 h2
    unfold GM06DrawingData.cyclicBetween at h1 h2
    split_ifs at h1 h2 <;> simp only [decide_eq_true_eq] at h1 h2 <;> omega
  | start b cp cn =>
    obtain ⟨hb, hcp, hcn, h1', h2', h3', hadj⟩ : b ∈ row ∧ cp ∈ row ∧ cn ∈ row ∧ b ≠ cp ∧ b ≠ cn ∧
      cp ≠ cn ∧ row.idxOf cn = (row.idxOf cp + 1) % row.length := h
    have hia := List.idxOf_lt_length_of_mem hb
    have hib := List.idxOf_lt_length_of_mem hcp
    have hic := List.idxOf_lt_length_of_mem hcn
    have n1 := idxOf_ne_of_ne hb hcp h1'
    have n2 := idxOf_ne_of_ne hb hcn h2'
    have n3 := idxOf_ne_of_ne hcp hcn h3'
    simp only [cutFirst, cutLast, e _ hb, e _ hcn] at h1 h2
    rcases mod_two_cases (m := row.idxOf cp + 1) (n := row.length) (by omega) with
      ⟨hm, hm2⟩ | ⟨hm, hm2⟩ <;> rw [hm] at hadj <;>
    unfold GM06DrawingData.cyclicBetween at h1 h2 <;>
    split_ifs at h1 h2 <;> simp only [decide_eq_true_eq] at h1 h2 <;> omega
  | terminal a cp cn =>
    obtain ⟨ha, hcp, hcn, h1', h2', h3', hadj⟩ : a ∈ row ∧ cp ∈ row ∧ cn ∈ row ∧ a ≠ cp ∧ a ≠ cn ∧
      cp ≠ cn ∧ row.idxOf cp = (row.idxOf cn + 1) % row.length := h
    have hia := List.idxOf_lt_length_of_mem ha
    have hib := List.idxOf_lt_length_of_mem hcp
    have hic := List.idxOf_lt_length_of_mem hcn
    have n1 := idxOf_ne_of_ne ha hcp h1'
    have n2 := idxOf_ne_of_ne ha hcn h2'
    have n3 := idxOf_ne_of_ne hcp hcn h3'
    simp only [cutFirst, cutLast, e _ ha, e _ hcp] at h1 h2
    rcases mod_two_cases (m := row.idxOf cn + 1) (n := row.length) (by omega) with
      ⟨hm, hm2⟩ | ⟨hm, hm2⟩ <;> rw [hm] at hadj <;>
    unfold GM06DrawingData.cyclicBetween at h1 h2 <;>
    split_ifs at h1 h2 <;> simp only [decide_eq_true_eq] at h1 h2 <;> omega

/-- Two rows without common darts: a dart lies in the row of one index only. -/
theorem rows_index_eq_of_mem {rows : List (List ℕ)} (hn : rows.flatten.Nodup)
    {i j : ℕ} {a b : List ℕ} (hi : rows[i]? = some a) (hj : rows[j]? = some b)
    {d : ℕ} (hda : d ∈ a) (hdb : d ∈ b) : i = j := by
  obtain ⟨hi', hai⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hbj⟩ := List.getElem?_eq_some_iff.mp hj
  have hp := List.pairwise_iff_getElem.mp (List.nodup_flatten.mp hn).2
  have hni : ¬ i < j := fun hij => hp i j hi' hj' hij (hai.symm ▸ hda) (hbj.symm ▸ hdb)
  have hnj : ¬ j < i := fun hji => hp j i hj' hi' hji (hbj.symm ▸ hdb) (hai.symm ▸ hda)
  omega

/-- A dart of a split row projects into the old row. -/
theorem uncut_mem_of_mem_splitVertexRows {pos : Option GM06CutPosition} {row r : List ℕ}
    (hr : r ∈ gm06SplitVertexRows pos row) {q : ℕ} (hq : q ∈ r) : gm06UncutDart q ∈ row := by
  cases pos with
  | none =>
    simp only [gm06SplitVertexRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      rw [gm06UncutDart_cut d 0 (by decide)]
      exact hd
    · exact absurd hq List.not_mem_nil
  | some p =>
    simp only [gm06SplitVertexRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact gm06CutRotation_project_mem p row _ hq

section Orbit

variable (marks : GM06CutTables) (rows : List (List ℕ))

local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (gm06SplitRotationRows marks rows)))
local notation "oldNext" => Equiv.trans dartMatePerm (Equiv.symm (gm06RotationPermutation rows))

/-- The cut face orbit stays among the cut darts. -/
theorem cut_iterate_mem (hn : rows.flatten.Nodup)
    (hmate : ∀ x ∈ (gm06SplitRotationRows marks rows).flatten,
      gm06DartMate x ∈ (gm06SplitRotationRows marks rows).flatten)
    {c : ℕ} (hc : c ∈ (gm06SplitRotationRows marks rows).flatten) (n : ℕ) :
    (cutNext)^[n] c ∈ (gm06SplitRotationRows marks rows).flatten := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact gm06RotationPermutation_symm_mem _ (gm06SplitRotationRows_nodup marks rows hn) _
      (by simpa only [Equiv.trans_apply, dartMatePerm_apply] using hmate _ ih)

/-- **The cut face orbit at one copy of a split vertex.** The cut face orbit of `c` visits the copy
`left` of a split vertex exactly when the old face orbit of the projection of `c` contains a dart
of the half-open block from the first dart of that copy, before its last dart. -/
theorem cut_orbit_mem_copy_iff (hn : rows.flatten.Nodup)
    (hok : ∀ v row p, rows[v]? = some row → gm06CutPositionAt marks v = some p → CutBlockOK p row)
    (hfit : CutFits marks rows)
    (hmate : ∀ x ∈ (gm06SplitRotationRows marks rows).flatten,
      gm06DartMate x ∈ (gm06SplitRotationRows marks rows).flatten)
    {c : ℕ} (hc : c ∈ (gm06SplitRotationRows marks rows).flatten)
    (hcF : gm06DartMate c ∉ cutFirstDarts marks rows)
    {v : ℕ} {row : List ℕ} {p : GM06CutPosition} (hv : rows[v]? = some row)
    (hp : gm06CutPositionAt marks v = some p) (left : Bool) :
    (∃ n, (cutNext)^[n] c ∈ gm06CutRotation p row left) ↔
      ∃ i, (∀ j ≤ i, row.formPerm^[j] (cutFirst p left) ≠ cutLast p left) ∧
        ∃ n, (oldNext)^[n] (gm06UncutDart c) = row.formPerm^[i] (cutFirst p left) := by
  have hrow : row ∈ rows := List.mem_of_getElem? hv
  have hrn : row.Nodup := (List.nodup_flatten.mp hn).1 row hrow
  have hb := hok v row p hv hp
  have hlast : ∀ l n, (cutNext)^[n] c ≠ gm06CutRowDart p l (cutLast p l) := fun l n h =>
    cut_face_iterate_not_last marks rows hn hok hfit hmate hc hcF n ⟨v, row, p, l, hv, hp, h⟩
  have hproj := cut_face_orbit_projection_of_fits marks rows hn hok hfit hmate hc hcF
  constructor
  · rintro ⟨n, hq⟩
    obtain ⟨hu, hw, huw, hkeep⟩ := cutBlock_spec hb left
    obtain ⟨i, hi, hid⟩ := (copy_project_iff_iterate p left hrn hu hw huw hkeep _).mp
      ⟨_, hq, hlast left n, rfl⟩
    exact ⟨i, hi, n, (hproj n).symm.trans hid.symm⟩
  · rintro ⟨i, hi, n, hn'⟩
    refine ⟨n, ?_⟩
    have hd := (hproj n).trans hn'
    obtain ⟨hu, hw, huw, hkeep⟩ := cutBlock_spec hb left
    have hblock := (block_iff_iterate hrn hu hw huw _).mpr ⟨i, hi, rfl⟩
    obtain ⟨v', row', r, hv', hr, hqr⟩ := exists_vertex_of_mem_split
      (cut_iterate_mem marks rows hn hmate hc n)
    have hvv : v' = v := rows_index_eq_of_mem hn hv' hv
      (uncut_mem_of_mem_splitVertexRows hr hqr) (hd ▸ hblock.1)
    subst hvv
    rw [hv] at hv'
    cases hv'
    rw [hp] at hr
    simp only [gm06SplitVertexRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hcase : ∃ l, r = gm06CutRotation p row l := by
      rcases hr with rfl | rfl
      exacts [⟨true, rfl⟩, ⟨false, rfl⟩]
    obtain ⟨l, rfl⟩ := hcase
    by_cases hl : l = left
    · exact hl ▸ hqr
    exfalso
    obtain ⟨hu', hw', huw', hkeep'⟩ := cutBlock_spec hb l
    obtain ⟨i', hi', hid'⟩ := (copy_project_iff_iterate p l hrn hu' hw' huw' hkeep' _).mp
      ⟨_, hqr, hlast l n, rfl⟩
    have hblock' := (block_iff_iterate hrn hu' hw' huw' _).mpr ⟨i', hi', hid'⟩
    rw [hd] at hblock'
    cases left <;> cases l
    · exact hl rfl
    · exact copy_blocks_disjoint hb hblock.1 hblock'.2 hblock.2
    · exact copy_blocks_disjoint hb hblock.1 hblock.2 hblock'.2
    · exact hl rfl

end Orbit

end GraphMinor.GM06
