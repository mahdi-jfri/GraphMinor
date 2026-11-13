module

public import GraphMinor.GM06.Alg57CutBlocks
public import GraphMinor.GM06.Alg57CutOrbit
public import GraphMinor.Compute.GM06CutTables
public import GraphMinor.Compute.GM06RotationPredecessors
import GraphMinor.Compute.GM06CutRowsFacts

/-!
# Face orbits of the cut graph project to face orbits of `G⁺`

The Word RAM program of (5.7) computes the incidence of Lemma 11 from the face orbit of `c̄ᵢ` in the
cut graph `Kᵢ`, whose rotation rows are `gm06SplitRotationRows marks rows`. Here we show that this
orbit projects onto the face orbit of `c̄ᵢ` in the old rotation (`cut_face_orbit_projection`). This
is the combinatorial part of Lemma 10 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`).

At each split vertex each copy keeps a closed cyclic interval of the old row
(`Alg57CutBlocks`). Its first dart is `cutFirst` and its last dart `cutLast`. With these, (C1) and
(C2) of `cut_orbit_projection` hold for every row (`cut_C1`, `cut_C2`). Condition (C3) says that
the reverse of the copy of a last dart is the copy of a first dart. It describes how the blocks fit
together along the linkage and the cuffs, and it is a hypothesis here.
-/

public section

namespace GraphMinor.GM06

open Equiv GraphMinor.Compute

/-- The rotation permutation of a list of rows, read backwards in the row of a dart. -/
theorem rotationPermutation_symm_apply_row {D : Type*} [DecidableEq D] (rows : List (List D))
    (hn : rows.flatten.Nodup) (row : List D) (hr : row ∈ rows) (d : D) (hd : d ∈ row) :
    (gm06RotationPermutation rows).symm d = row.formPerm.symm d := by
  have hmem : row.formPerm.symm d ∈ row := by
    by_contra h
    have h' := List.formPerm_apply_of_notMem h
    rw [Equiv.apply_symm_apply] at h'
    rw [← h'] at h
    exact h hd
  rw [Equiv.symm_apply_eq, gm06RotationPermutation_apply_row rows hn row hr _ hmem,
    Equiv.apply_symm_apply]

/-- The first dart of the block kept by a copy of a split vertex. -/
def cutFirst : GM06CutPosition → Bool → ℕ
  | .interior _ b, true => b
  | .interior a _, false => a
  | .start b _ _, true => b
  | .start _ _ cn, false => cn
  | .terminal _ cp _, true => cp
  | .terminal a _ _, false => a

/-- The last dart of the block kept by a copy of a split vertex. -/
def cutLast : GM06CutPosition → Bool → ℕ
  | .interior a _, true => a
  | .interior _ b, false => b
  | .start _ cp _, true => cp
  | .start b _ _, false => b
  | .terminal a _ _, true => a
  | .terminal _ _ cn, false => cn

/-- The local hypotheses at a split vertex: its path and cuff ends are distinct darts of its row,
and at a start (terminal) the negative (positive) cuff end follows the other one in the row. -/
def CutBlockOK (p : GM06CutPosition) (row : List ℕ) : Prop :=
  match p with
  | .interior a b => a ∈ row ∧ b ∈ row ∧ a ≠ b
  | .start b cp cn => b ∈ row ∧ cp ∈ row ∧ cn ∈ row ∧ b ≠ cp ∧ b ≠ cn ∧ cp ≠ cn ∧
      row.idxOf cn = (row.idxOf cp + 1) % row.length
  | .terminal a cp cn => a ∈ row ∧ cp ∈ row ∧ cn ∈ row ∧ a ≠ cp ∧ a ≠ cn ∧ cp ≠ cn ∧
      row.idxOf cp = (row.idxOf cn + 1) % row.length

/-- Under `CutBlockOK`, each copy keeps the closed interval from `cutFirst` to `cutLast`. -/
theorem cutBlock_spec {p : GM06CutPosition} {row : List ℕ} (h : CutBlockOK p row) (left : Bool) :
    cutFirst p left ∈ row ∧ cutLast p left ∈ row ∧ cutFirst p left ≠ cutLast p left ∧
    ∀ d ∈ row, cutKeep p row left d = true ↔ (d = cutFirst p left ∨ d = cutLast p left ∨
      GM06DrawingData.cyclicBetween (row.idxOf (cutFirst p left)) (row.idxOf (cutLast p left))
        (row.idxOf d) = true) := by
  cases p with
  | interior a b =>
    obtain ⟨ha, hb, hab⟩ := h
    cases left
    · exact ⟨ha, hb, hab, cutKeep_interior_right ha hb hab⟩
    · exact ⟨hb, ha, Ne.symm hab, cutKeep_interior_left⟩
  | start b cp cn =>
    obtain ⟨hb, hcp, hcn, hbp, hbn, hpn, hnext⟩ := h
    cases left
    · exact ⟨hcn, hb, Ne.symm hbn, cutKeep_start_right hb hcp hcn hbp hbn hpn hnext⟩
    · exact ⟨hb, hcp, hbp, cutKeep_start_left hb hcp hcn hbp hbn hpn hnext⟩
  | terminal a cp cn =>
    obtain ⟨ha, hcp, hcn, hap, han, hpn, hnext⟩ := h
    cases left
    · exact ⟨ha, hcn, han, cutKeep_terminal_right ha hcp hcn hap han hpn hnext⟩
    · exact ⟨hcp, ha, Ne.symm hap, cutKeep_terminal_left ha hcp hcn hap han hpn hnext⟩

/-- In a copy, the copy of the first dart is preceded by the copy of the last dart. -/
theorem cutRotation_symm_first {p : GM06CutPosition} {row : List ℕ} (hn : row.Nodup)
    (h : CutBlockOK p row) (left : Bool) :
    (gm06CutRotation p row left).formPerm.symm (gm06CutRowDart p left (cutFirst p left)) =
      gm06CutRowDart p left (cutLast p left) := by
  obtain ⟨hu, hw, huw, hkeep⟩ := cutBlock_spec h left
  have h2 := (formPerm_filter_symm_of_closed row hn (cutKeep p row left) hu hw huw hkeep).2
  have hfirst : cutFirst p left ∈ row.filter (cutKeep p row left) :=
    List.mem_filter.mpr ⟨hu, (hkeep _ hu).mpr (Or.inl rfl)⟩
  have hmap := map_formPerm_symm (row.filter (cutKeep p row left)) (gm06CutRowDart p left)
    (hn.filter _) (gm06CutRotation_eq_map_filter p row left ▸ gm06CutRotation_nodup p row left hn)
    hfirst
  rw [h2, ← gm06CutRotation_eq_map_filter] at hmap
  exact hmap.symm

/-- A dart of a copy is the copy of its projection. -/
theorem eq_cutRowDart_of_mem {p : GM06CutPosition} {row : List ℕ} {left : Bool} {x : ℕ}
    (hx : x ∈ gm06CutRotation p row left) : x = gm06CutRowDart p left (gm06UncutDart x) := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  rw [gm06CutRowDart_project]

/-- Reversal commutes with projection. -/
theorem gm06UncutDart_mate (x : ℕ) : gm06UncutDart (gm06DartMate x) = gm06DartMate (gm06UncutDart x) := by
  unfold gm06UncutDart gm06DartMate
  split_ifs <;> omega

/-- Copies of first darts. -/
def cutFirstDarts (marks : GM06CutTables) (rows : List (List ℕ)) : Set ℕ :=
  {x | ∃ v row p left, rows[v]? = some row ∧ gm06CutPositionAt marks v = some p ∧
    x = gm06CutRowDart p left (cutFirst p left)}

/-- Copies of last darts. -/
def cutLastDarts (marks : GM06CutTables) (rows : List (List ℕ)) : Set ℕ :=
  {x | ∃ v row p left, rows[v]? = some row ∧ gm06CutPositionAt marks v = some p ∧
    x = gm06CutRowDart p left (cutLast p left)}

/-- The cut rows of a vertex lie among all cut rows. -/
theorem mem_splitRotationRows {marks : GM06CutTables} {rows : List (List ℕ)} {v : ℕ}
    {row : List ℕ} (hv : rows[v]? = some row) {r : List ℕ}
    (hr : r ∈ gm06SplitVertexRows (gm06CutPositionAt marks v) row) :
    r ∈ gm06SplitRotationRows marks rows :=
  List.mem_flatMap.mpr ⟨(row, v), List.mem_zipIdx_iff_getElem?.mpr hv, hr⟩

/-- A cut dart lies in a cut row of some vertex. -/
theorem exists_vertex_of_mem_split {marks : GM06CutTables} {rows : List (List ℕ)} {x : ℕ}
    (hx : x ∈ (gm06SplitRotationRows marks rows).flatten) :
    ∃ v row r, rows[v]? = some row ∧ r ∈ gm06SplitVertexRows (gm06CutPositionAt marks v) row ∧
      x ∈ r := by
  obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hx
  obtain ⟨⟨row, v⟩, hp, hr⟩ := List.mem_flatMap.mp hr
  exact ⟨v, row, r, List.mem_zipIdx_iff_getElem?.mp hp, hr, hxr⟩

variable (marks : GM06CutTables) (rows : List (List ℕ))

/-- **(C1)** A cut dart that is not the copy of a first dart has as predecessor the copy of its old
predecessor. -/
theorem cut_C1 (hn : rows.flatten.Nodup)
    (hok : ∀ v row p, rows[v]? = some row → gm06CutPositionAt marks v = some p → CutBlockOK p row)
    {x : ℕ} (hx : x ∈ (gm06SplitRotationRows marks rows).flatten)
    (hxF : x ∉ cutFirstDarts marks rows) :
    gm06UncutDart ((gm06RotationPermutation (gm06SplitRotationRows marks rows)).symm x) =
      (gm06RotationPermutation rows).symm (gm06UncutDart x) := by
  obtain ⟨v, row, r, hv, hr, hxr⟩ := exists_vertex_of_mem_split hx
  have hrow : row ∈ rows := List.mem_of_getElem? hv
  have hrn : row.Nodup := (List.nodup_flatten.mp hn).1 row hrow
  rw [rotationPermutation_symm_apply_row _ (gm06SplitRotationRows_nodup marks rows hn) r
    (mem_splitRotationRows hv hr) x hxr]
  cases hpos : gm06CutPositionAt marks v with
  | none =>
    rw [hpos] at hr
    simp only [gm06SplitVertexRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hmap : (row.map (fun d => gm06CutDart d 0)).map gm06UncutDart = row := by
        rw [List.map_map]
        exact List.map_id'' (fun d => gm06UncutDart_cut d 0 (by decide)) _
      have hnd : (row.map (fun d => gm06CutDart d 0)).Nodup :=
        List.Nodup.of_map gm06UncutDart (by rw [hmap]; exact hrn)
      rw [map_formPerm_symm _ gm06UncutDart hnd (by rw [hmap]; exact hrn) hxr, hmap]
      have hux : gm06UncutDart x ∈ row := by rw [← hmap]; exact List.mem_map_of_mem hxr
      rw [rotationPermutation_symm_apply_row rows hn row hrow _ hux]
    · exact absurd hxr (List.not_mem_nil)
  | some p =>
    rw [hpos] at hr
    simp only [gm06SplitVertexRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hcase : ∃ left, r = gm06CutRotation p row left := by
      rcases hr with rfl | rfl
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    obtain ⟨left, rfl⟩ := hcase
    have hb := hok v row p hv hpos
    obtain ⟨hu, hw, huw, hkeep⟩ := cutBlock_spec hb left
    rw [cutRotation_symm_project p row left hrn hu hw huw hkeep hxr]
    have hne : gm06UncutDart x ≠ cutFirst p left := by
      intro h
      exact hxF ⟨v, row, p, left, hv, hpos, by rw [← h]; exact eq_cutRowDart_of_mem hxr⟩
    have hux : gm06UncutDart x ∈ row := by
      have := gm06CutRotation_project p row left
      have hm : gm06UncutDart x ∈ (gm06CutRotation p row left).map gm06UncutDart :=
        List.mem_map_of_mem hxr
      rw [this] at hm
      exact (List.mem_filter.mp hm).1
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne), rotationPermutation_symm_apply_row rows hn row hrow _ hux]

/-- **(C2)** The predecessor of the copy of a first dart is the copy of a last dart. -/
theorem cut_C2 (hn : rows.flatten.Nodup)
    (hok : ∀ v row p, rows[v]? = some row → gm06CutPositionAt marks v = some p → CutBlockOK p row)
    {x : ℕ} (hxF : x ∈ cutFirstDarts marks rows) :
    (gm06RotationPermutation (gm06SplitRotationRows marks rows)).symm x ∈
      cutLastDarts marks rows := by
  obtain ⟨v, row, p, left, hv, hpos, rfl⟩ := hxF
  have hrow : row ∈ rows := List.mem_of_getElem? hv
  have hrn : row.Nodup := (List.nodup_flatten.mp hn).1 row hrow
  have hb := hok v row p hv hpos
  have hr : gm06CutRotation p row left ∈ gm06SplitVertexRows (gm06CutPositionAt marks v) row := by
    rw [hpos]; cases left <;> simp [gm06SplitVertexRows]
  obtain ⟨hu, -, -, hkeep⟩ := cutBlock_spec hb left
  have hmem : gm06CutRowDart p left (cutFirst p left) ∈ gm06CutRotation p row left :=
    gm06CutRotation_eq_map_filter p row left ▸
      List.mem_map_of_mem (List.mem_filter.mpr ⟨hu, (hkeep _ hu).mpr (Or.inl rfl)⟩)
  rw [rotationPermutation_symm_apply_row _ (gm06SplitRotationRows_nodup marks rows hn) _
    (mem_splitRotationRows hv hr) _ hmem, cutRotation_symm_first hrn hb left]
  exact ⟨v, row, p, left, hv, hpos, rfl⟩

/-- The path end by which the linkage arrives at a split vertex (as an outgoing dart). -/
def cutIncoming : GM06CutPosition → Option ℕ
  | .interior a _ => some a
  | .start _ _ _ => none
  | .terminal a _ _ => some a

/-- The path end by which the linkage leaves a split vertex. -/
def cutOutgoing : GM06CutPosition → Option ℕ
  | .interior _ b => some b
  | .start b _ _ => some b
  | .terminal _ _ _ => none

/-- How the split vertices fit together: the reverse of an arriving path end leaves an earlier split
vertex, the reverse of a leaving path end arrives at a later one, the reverse of the positive cuff
end at a start is the negative cuff end at a start, and the reverse of the negative cuff end at a
terminal is the positive cuff end at a terminal. -/
structure CutFits (marks : GM06CutTables) (rows : List (List ℕ)) : Prop where
  incoming : ∀ v row p a, rows[v]? = some row → gm06CutPositionAt marks v = some p →
    cutIncoming p = some a → ∃ u row' p', rows[u]? = some row' ∧
      gm06CutPositionAt marks u = some p' ∧ cutOutgoing p' = some (gm06DartMate a)
  outgoing : ∀ v row p b, rows[v]? = some row → gm06CutPositionAt marks v = some p →
    cutOutgoing p = some b → ∃ u row' p', rows[u]? = some row' ∧
      gm06CutPositionAt marks u = some p' ∧ cutIncoming p' = some (gm06DartMate b)
  start : ∀ v row b cp cn, rows[v]? = some row →
    gm06CutPositionAt marks v = some (.start b cp cn) → ∃ u row' b' cp', rows[u]? = some row' ∧
      gm06CutPositionAt marks u = some (.start b' cp' (gm06DartMate cp))
  terminal : ∀ v row a cp cn, rows[v]? = some row →
    gm06CutPositionAt marks v = some (.terminal a cp cn) → ∃ u row' a' cn', rows[u]? = some row' ∧
      gm06CutPositionAt marks u = some (.terminal a' (gm06DartMate cn) cn')

/-- **(C3)** If the split vertices fit together, the reverse of the copy of a last dart is the copy
of a first dart. -/
theorem cut_C3 (hok : ∀ v row p, rows[v]? = some row → gm06CutPositionAt marks v = some p →
      CutBlockOK p row)
    (hfit : CutFits marks rows) {y : ℕ} (hy : y ∈ cutLastDarts marks rows) :
    gm06DartMate y ∈ cutFirstDarts marks rows := by
  obtain ⟨v, row, p, left, hv, hpos, rfl⟩ := hy
  have hb := hok v row p hv hpos
  -- arriving at a vertex from the previous one, on the left
  have hleft : ∀ d, (∃ u row' p', rows[u]? = some row' ∧
      gm06CutPositionAt marks u = some p' ∧ cutOutgoing p' = some d) →
      gm06CutDart d 0 ∈ cutFirstDarts marks rows := by
    rintro d ⟨u, row', p', hu, hpu, hout⟩
    refine ⟨u, row', p', true, hu, hpu, ?_⟩
    cases p' <;> simp only [cutOutgoing, reduceCtorEq, Option.some.injEq] at hout <;> subst hout <;>
      simp [gm06CutRowDart, cutFirst, GM06CutPosition.pathEnds]
  have hright : ∀ d, (∃ u row' p', rows[u]? = some row' ∧
      gm06CutPositionAt marks u = some p' ∧ cutIncoming p' = some d) →
      gm06CutDart d 1 ∈ cutFirstDarts marks rows := by
    rintro d ⟨u, row', p', hu, hpu, hin⟩
    refine ⟨u, row', p', false, hu, hpu, ?_⟩
    cases p' <;> simp only [cutIncoming, reduceCtorEq, Option.some.injEq] at hin <;> subst hin <;>
      simp [gm06CutRowDart, cutFirst, GM06CutPosition.pathEnds]
  cases p with
  | interior a b =>
    cases left
    · have := hright _ (hfit.outgoing v row _ b hv hpos rfl)
      simpa [gm06CutRowDart, cutLast, GM06CutPosition.pathEnds, ← gm06CutDart_mate] using this
    · have := hleft _ (hfit.incoming v row _ a hv hpos rfl)
      simpa [gm06CutRowDart, cutLast, GM06CutPosition.pathEnds, ← gm06CutDart_mate] using this
  | start b cp cn =>
    cases left
    · have := hright _ (hfit.outgoing v row _ b hv hpos rfl)
      simpa [gm06CutRowDart, cutLast, GM06CutPosition.pathEnds, ← gm06CutDart_mate] using this
    · obtain ⟨u, row', b', cp', hu, hpu⟩ := hfit.start v row b cp cn hv hpos
      have hb' := hok u row' _ hu hpu
      refine ⟨u, row', _, false, hu, hpu, ?_⟩
      simp only [gm06CutRowDart, cutLast, cutFirst, GM06CutPosition.pathEnds, List.mem_singleton,
        ← gm06CutDart_mate]
      rw [ite_eq_right_iff.mpr (fun h => absurd h (Ne.symm hb.2.2.2.1)),
        ite_eq_right_iff.mpr (fun h => absurd h.symm hb'.2.2.2.2.1)]
  | terminal a cp cn =>
    cases left
    · obtain ⟨u, row', a', cn', hu, hpu⟩ := hfit.terminal v row a cp cn hv hpos
      have hb' := hok u row' _ hu hpu
      refine ⟨u, row', _, true, hu, hpu, ?_⟩
      simp only [gm06CutRowDart, cutLast, cutFirst, GM06CutPosition.pathEnds, List.mem_singleton,
        ← gm06CutDart_mate]
      rw [ite_eq_right_iff.mpr (fun h => absurd h.symm hb.2.2.2.2.1),
        ite_eq_right_iff.mpr (fun h => absurd h.symm hb'.2.2.2.1)]
    · have := hleft _ (hfit.incoming v row _ a hv hpos rfl)
      simpa [gm06CutRowDart, cutLast, GM06CutPosition.pathEnds, ← gm06CutDart_mate] using this

/-- A copy of a dart that is no first dart of any block is not the copy of a first dart. -/
theorem cutDart_not_mem_cutFirstDarts {d : ℕ}
    (h : ∀ v row p left, rows[v]? = some row → gm06CutPositionAt marks v = some p →
      cutFirst p left ≠ d) : gm06CutDart d 0 ∉ cutFirstDarts marks rows := by
  rintro ⟨v, row, p, left, hv, hpos, heq⟩
  have := congrArg gm06UncutDart heq
  rw [gm06UncutDart_cut d 0 (by decide), gm06CutRowDart_project] at this
  exact h v row p left hv hpos this.symm

/-- The reversal of darts as a permutation. -/
def dartMatePerm : Perm ℕ := gm06DartMate_involutive.toPerm _

/-- **Projection of the face orbits of the cut graph.** Assume the old rows have no repeated darts,
the local hypotheses `CutBlockOK` hold at every split vertex, the cut darts are closed under
reversal, and (C3): the reverse of the copy of a last dart is the copy of a first dart. Then for a
cut dart `c` whose reverse is not the copy of a first dart, the face orbit of `c` in the cut rotation
projects step by step onto the face orbit of its projection in the old rotation. -/
theorem cut_face_orbit_projection (hn : rows.flatten.Nodup)
    (hok : ∀ v row p, rows[v]? = some row → gm06CutPositionAt marks v = some p → CutBlockOK p row)
    (hmate : ∀ x ∈ (gm06SplitRotationRows marks rows).flatten,
      gm06DartMate x ∈ (gm06SplitRotationRows marks rows).flatten)
    (C3 : ∀ y ∈ (gm06SplitRotationRows marks rows).flatten, y ∈ cutLastDarts marks rows →
      gm06DartMate y ∈ cutFirstDarts marks rows)
    {c : ℕ} (hc : c ∈ (gm06SplitRotationRows marks rows).flatten)
    (hcF : gm06DartMate c ∉ cutFirstDarts marks rows) (n : ℕ) :
    gm06UncutDart ((dartMatePerm.trans
        (gm06RotationPermutation (gm06SplitRotationRows marks rows)).symm)^[n] c) =
      (dartMatePerm.trans (gm06RotationPermutation rows).symm)^[n] (gm06UncutDart c) := by
  classical
  set σ' := gm06RotationPermutation (gm06SplitRotationRows marks rows)
  have hS : ∀ x ∈ (gm06SplitRotationRows marks rows).flatten.toFinset, σ'.symm x ∈
      (gm06SplitRotationRows marks rows).flatten.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    obtain ⟨v, row, r, hv, hr, hxr⟩ := exists_vertex_of_mem_split hx
    rw [rotationPermutation_symm_apply_row _ (gm06SplitRotationRows_nodup marks rows hn) r
      (mem_splitRotationRows hv hr) x hxr]
    have hmem : r.formPerm.symm x ∈ r := by
      by_contra h
      have h' := List.formPerm_apply_of_notMem h
      rw [Equiv.apply_symm_apply] at h'
      rw [← h'] at h
      exact h hxr
    exact List.mem_flatten.mpr ⟨r, mem_splitRotationRows hv hr, hmem⟩
  exact (cut_orbit_projection σ' dartMatePerm (gm06RotationPermutation rows) dartMatePerm
    gm06UncutDart _ (cutFirstDarts marks rows) (cutLastDarts marks rows) hS
    (fun x hx => List.mem_toFinset.mpr (hmate x (List.mem_toFinset.mp hx)))
    (fun x => gm06UncutDart_mate x)
    (fun x hx hxF => cut_C1 marks rows hn hok (List.mem_toFinset.mp hx) hxF)
    (fun x _ hxF => cut_C2 marks rows hn hok hxF)
    (fun y hy hyΛ => C3 y (List.mem_toFinset.mp hy) hyΛ)
    (List.mem_toFinset.mpr hc) hcF n).2.2

/-- The orbit form: a dart is in the old face orbit of the projection of `c` exactly when it is the
projection of a dart in the cut face orbit of `c`. -/
theorem cut_face_orbit_projection_iff (hn : rows.flatten.Nodup)
    (hok : ∀ v row p, rows[v]? = some row → gm06CutPositionAt marks v = some p → CutBlockOK p row)
    (hfit : CutFits marks rows)
    (hmate : ∀ x ∈ (gm06SplitRotationRows marks rows).flatten,
      gm06DartMate x ∈ (gm06SplitRotationRows marks rows).flatten)
    {c : ℕ} (hc : c ∈ (gm06SplitRotationRows marks rows).flatten)
    (hcF : gm06DartMate c ∉ cutFirstDarts marks rows) (d : ℕ) :
    (∃ n, (dartMatePerm.trans (gm06RotationPermutation rows).symm)^[n] (gm06UncutDart c) = d) ↔
      ∃ n, gm06UncutDart ((dartMatePerm.trans
        (gm06RotationPermutation (gm06SplitRotationRows marks rows)).symm)^[n] c) = d := by
  have h := fun n => cut_face_orbit_projection marks rows hn hok hmate
    (fun _ _ hy => cut_C3 marks rows hok hfit hy) hc hcF n
  exact ⟨fun ⟨n, hn⟩ => ⟨n, (h n).trans hn⟩, fun ⟨n, hn⟩ => ⟨n, (h n).symm.trans hn⟩⟩

/-- `cut_face_orbit_projection` with (C3) discharged by `CutFits`. -/
theorem cut_face_orbit_projection_of_fits (hn : rows.flatten.Nodup)
    (hok : ∀ v row p, rows[v]? = some row → gm06CutPositionAt marks v = some p → CutBlockOK p row)
    (hfit : CutFits marks rows)
    (hmate : ∀ x ∈ (gm06SplitRotationRows marks rows).flatten,
      gm06DartMate x ∈ (gm06SplitRotationRows marks rows).flatten)
    {c : ℕ} (hc : c ∈ (gm06SplitRotationRows marks rows).flatten)
    (hcF : gm06DartMate c ∉ cutFirstDarts marks rows) (n : ℕ) :
    gm06UncutDart ((dartMatePerm.trans
        (gm06RotationPermutation (gm06SplitRotationRows marks rows)).symm)^[n] c) =
      (dartMatePerm.trans (gm06RotationPermutation rows).symm)^[n] (gm06UncutDart c) :=
  cut_face_orbit_projection marks rows hn hok hmate
    (fun _ _ hy => cut_C3 marks rows hok hfit hy) hc hcF n

end GraphMinor.GM06
