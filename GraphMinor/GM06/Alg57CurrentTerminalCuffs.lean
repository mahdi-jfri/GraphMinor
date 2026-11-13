module

public import GraphMinor.GM06.Alg57CurrentTerminalInputs
import GraphMinor.GM06.Section5NextContact

/-!
# The cuff ends of the actual terminal face

In Section 15 of the proof of VI (5.7), page 133, the removed
reverse inner cuff end runs from the next right source to the
chosen left source. Forward inner cuff ends and reverse outer
cuff ends belong to the exterior boundary orbits. The computed
local cuff positions and copied-row origins prove these facts
without a supplied cut representation.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "marks" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff
local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)

private theorem row_lookup (a : Fin x.vertexCount) :
    x.rotations[a.val]? = some (x.rotations.getD a.val []) := by
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  simp only [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]

/-- A dart in a permanent copied slot has exactly that stored origin. -/
theorem cut_origin_of_slot (hG : IsCylinderSection5Drawing k G) (a : Fin x.vertexCount)
    (left : Bool) {q : ℕ}
    (hq : q ∈ (currentCut).rotations.getD (gm06CutVertex a.val left) []) :
    (currentCut).origins[q]?.getD 0 = gm06CutVertex a.val left := by
  have hslot : gm06CutVertex a.val left < (currentCut).rotations.length := by
    simp only [gm06CutDataOfLinkage, gm06SplitRotationRows_length, rep.rows_length]
    have hh := a.isLt
    cases left <;> simp only [gm06CutVertex, Bool.not_true, Bool.not_false,
      Bool.toNat_true, Bool.toNat_false] <;> omega
  rw [List.getD_eq_getElem _ _ hslot] at hq
  have hflat := List.mem_flatten.mpr ⟨_, List.getElem_mem hslot, hq⟩
  obtain ⟨hn, hk, _, _, _⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hb := hk q hflat
  have hbound : q < 4 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length) := by
    rw [rep.cuff_lengths.1, rep.cuff_lengths.2]
    omega
  exact (gm06CutOrigins_row_iff _ hn hflat hbound hslot).mpr hq

/-- A retained nonpath end has the stored origin of its assigned side. -/
theorem cut_nonpath_origin (hG : IsCylinderSection5Drawing k G) (a : Fin x.vertexCount)
    (p : GM06CutPosition) (hp : gm06CutPositionAt marks a.val = some p)
    (d : ℕ) (hd : d ∈ x.rotations.getD a.val []) (hnot : d ∉ p.pathEnds)
    (left : Bool) (hside : gm06CutDartLeft p (x.rotations.getD a.val []) d = left) :
    (currentCut).origins[gm06CutDart d 0]?.getD 0 = gm06CutVertex a.val left := by
  apply rep.cut_origin_of_slot hG a left
  dsimp only [gm06CutDataOfLinkage]
  rw [splitRows_getD_of_position (rep.rows_length.symm ▸ a.isLt) hp left]
  exact (gm06CutRotation_nonpath_mem p _ d hnot left).mpr ⟨hd, hside⟩

/-- At either cuff position its positive marker is at the left
copy and its negative marker is at the right copy. -/
theorem cut_cuff_origin_table (hG : IsCylinderSection5Drawing k G) (a : Fin x.vertexCount)
    (p : GM06CutPosition) (hp : gm06CutPositionAt marks a.val = some p) :
    match p with
    | .interior _ _ => True
    | .start _ cp cn | .terminal _ cp cn =>
        (currentCut).origins[gm06CutDart cp 0]?.getD 0 = gm06CutVertex a.val true ∧
        (currentCut).origins[gm06CutDart cn 0]?.getD 0 = gm06CutVertex a.val false := by
  have hok := rep.cut_block_ok hG _ _ _ (rep.row_lookup a) hp
  cases p with
  | interior => trivial
  | start b cp cn =>
    obtain ⟨_, hcp, hcn, _, _, hpn, _⟩ := (cutBlockOK_start_iff _ _ _ _).mp hok
    obtain ⟨i, _, hcpword, hcnword⟩ := rep.cut_start_markers hG.1 a hp
    have hnp : cp ∉ (GM06CutPosition.start b cp cn).pathEnds := by
      intro h
      have hb := rep.cut_path_end_lt a hp h
      omega
    have hnn : cn ∉ (GM06CutPosition.start b cp cn).pathEnds := by
      intro h
      have hb := rep.cut_path_end_lt a hp h
      omega
    have hs := gm06CutDartLeft_cuffs b cp cn hpn (x.rotations.getD a.val [])
    exact ⟨rep.cut_nonpath_origin hG a _ hp cp hcp hnp true hs.1,
      rep.cut_nonpath_origin hG a _ hp cn hcn hnn false hs.2.1⟩
  | terminal b cp cn =>
    obtain ⟨_, hcp, hcn, _, _, hpn, _⟩ := (cutBlockOK_terminal_iff _ _ _ _).mp hok
    obtain ⟨i, _, hcpword, hcnword⟩ := rep.cut_terminal_markers hG.1 a hp
    have hnp : cp ∉ (GM06CutPosition.terminal b cp cn).pathEnds := by
      intro h
      have hb := rep.cut_path_end_lt a hp h
      omega
    have hnn : cn ∉ (GM06CutPosition.terminal b cp cn).pathEnds := by
      intro h
      have hb := rep.cut_path_end_lt a hp h
      omega
    have hs := gm06CutDartLeft_cuffs b cp cn hpn (x.rotations.getD a.val [])
    exact ⟨rep.cut_nonpath_origin hG a _ hp cp hcp hnp true hs.2.2.1,
      rep.cut_nonpath_origin hG a _ hp cn hcn hnn false hs.2.2.2⟩

/-- The signed inner gap ends have their two prescribed copied origins. -/
theorem inner_copied_origins (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    (currentCut).origins[gm06CutDart (2 * (rep.tagged.length + i.val)) 0]?.getD 0 =
        gm06CutVertex (rep.source i).val true ∧
    (currentCut).origins[gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0]?.getD 0 =
        gm06CutVertex (rep.source (finSuccCycle i)).val false := by
  obtain ⟨b, hp⟩ := rep.cut_source_position hG.1 i
  obtain ⟨b', hp'⟩ := rep.cut_source_position hG.1 (finSuccCycle i)
  have hprev : gm06PreviousCuffIndex k (finSuccCycle i).val = i.val := by
    rw [previousCuffIndex_eq_pred, finPredCycle_finSuccCycle]
  exact ⟨(rep.cut_cuff_origin_table hG _ _ hp).1,
    by simpa only [hprev] using (rep.cut_cuff_origin_table hG _ _ hp').2⟩

/-- Forward inner cuff ends lie in the last-end boundary set. -/
theorem positive_inner_is_last (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    gm06CutDart (2 * (rep.tagged.length + i.val)) 0 ∈ cutLastDarts marks x.rotations := by
  obtain ⟨b, hp⟩ := rep.cut_source_position hG.1 i
  have hnot : 2 * (rep.tagged.length + i.val) ∉
      (GM06CutPosition.start b (2 * (rep.tagged.length + i.val))
        (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1)).pathEnds := by
    intro h
    have hb := rep.cut_path_end_lt (rep.source i) hp h
    omega
  have hh := cutLastDarts_of_position (rep.row_lookup _) hp true
  simpa only [cutLast_eq, gm06CutRowDart, hnot, ite_false] using hh

/-- Reverse outer cuff ends also lie in the last-end boundary set. -/
theorem negative_outer_is_last (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    gm06CutDart (2 * (rep.tagged.length + k + i.val) + 1) 0 ∈ cutLastDarts marks x.rotations := by
  obtain ⟨b, hp⟩ := rep.cut_target_position hG.1 (finSuccCycle i)
  have hprev : gm06PreviousCuffIndex k (finSuccCycle i).val = i.val := by
    rw [previousCuffIndex_eq_pred, finPredCycle_finSuccCycle]
  rw [hprev] at hp
  have hnot : 2 * (rep.tagged.length + k + i.val) + 1 ∉
      (GM06CutPosition.terminal b (2 * (rep.tagged.length + k + (finSuccCycle i).val))
        (2 * (rep.tagged.length + k + i.val) + 1)).pathEnds := by
    intro h
    have hb := rep.cut_path_end_lt (rep.target (finSuccCycle i)) hp h
    omega
  have hh := cutLastDarts_of_position (rep.row_lookup _) hp false
  simpa only [cutLast_eq, gm06CutRowDart, hnot, ite_false] using hh

/-- A nonordinary active end has no linkage copy tag. -/
theorem cut_cuff_tag_zero (hG : IsCylinderSection5Drawing k G) {q : ℕ}
    (hq : q ∈ (currentCut).activeDarts) (hlarge : 2 * rep.tagged.length ≤ gm06UncutDart q) :
    q = gm06CutDart (gm06UncutDart q) 0 := by
  have ht : q / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hreb := gm06CutDart_rebuild q
  have hcopy : gm06CutDart (gm06UncutDart q) (q / 2 % 2) ∈
      (gm06CutAlongLinkageRotations x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff x.rotations).flatten := by
    rw [hreb]
    exact ((gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hq).2
  have hh := ((rep.cut_copies hG _ _ ht).mp hcopy).2
  have htag : q / 2 % 2 = 0 := by
    rcases hh with h | h | h
    · exact h
    · have hb := rep.path_word_lt h
      omega
    · have hb := gm06DartMate_lt (rep.path_word_lt h)
      rw [gm06DartMate_involutive] at hb
      omega
  rw [htag] at hreb
  exact hreb.symm

/-- A forward outer cuff end starts at its prescribed left target copy. -/
theorem positive_outer_origin (hG : IsCylinderSection5Drawing k G) (j : Fin k) :
    (currentCut).origins[gm06CutDart (2 * (rep.tagged.length + k + j.val)) 0]?.getD 0 =
      gm06CutVertex (rep.target j).val true := by
  obtain ⟨a, hp⟩ := rep.cut_target_position hG.1 j
  exact (rep.cut_cuff_origin_table hG _ _ hp).1

local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (GM06CutData.rotations currentCut)))
local notation "gap" i:arg => gm06CutDart (2 * (rep.tagged.length + Fin.val (i : Fin k)) + 1) 0

/-- A selected face contains only its own reverse inner gap. -/
theorem selected_face_inner_gap_unique (hG : IsCylinderSection5Drawing k G)
    (i j : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (hj : (gap j) ∈ row) : j = i := by
  obtain ⟨H, _, _, _, g, _, hface, _, _, hdistinct⟩ := rep.exists_strip_corner_labels hG
  obtain ⟨n, hn⟩ := (horbit _).mp hj
  have hlabel := rep.cut_iterate_corner_label hG g hface i n
  dsimp only at hlabel
  dsimp only [gm06CutDataOfLinkage] at hn
  rw [hn, gm06UncutDart_cut _ 0 (by decide)] at hlabel
  exact hdistinct j i hlabel

/-- The only cuff ends on the selected face are its own reverse
inner gap and forward outer cuff ends. -/
theorem selected_face_cuff_cases (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    {q : ℕ} (hq : q ∈ row) (hlarge : 2 * rep.tagged.length ≤ gm06UncutDart q) :
    q = (gap i) ∨ ∃ j : Fin k, q = gm06CutDart (2 * (rep.tagged.length + k + j.val)) 0 := by
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  have htag := rep.cut_cuff_tag_zero hG hactive hlarge
  have hact := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hactive
  have ho := cutOrigins_project_mem marks x.rotations rep.rows_flatten_nodup hact.2 hact.1
  obtain ⟨a, ha, _, _, _, _⟩ := rep.cut_origin_point (List.range x.vertexCount) hactive
  have hrow : gm06UncutDart q ∈ x.rotations.getD a.val [] := by
    rw [ha]
    exact ho.2
  have hnot : q ∉ cutLastDarts marks x.rotations := by
    obtain ⟨n, rfl⟩ := (horbit q).mp hq
    exact rep.cut_iterate_not_last hG i n
  rcases rep.cuff_word_cases hG a hrow hlarge with ⟨j, b, hw, _⟩ | ⟨j, b, hw, _⟩
  · cases b with
    | false =>
      simp only [Bool.toNat_false, Nat.add_zero] at hw
      have hqj : q = gm06CutDart (2 * (rep.tagged.length + j.val)) 0 :=
        htag.trans (congrArg (fun d => gm06CutDart d 0) hw)
      exact False.elim (hnot (hqj.symm ▸ rep.positive_inner_is_last hG j))
    | true =>
      simp only [Bool.toNat_true] at hw
      have hqj : q = (gap j) := htag.trans (congrArg (fun d => gm06CutDart d 0) hw)
      have hj := rep.selected_face_inner_gap_unique hG i j row horbit (hqj ▸ hq)
      exact Or.inl (hj ▸ hqj)
  · cases b with
    | false =>
      simp only [Bool.toNat_false, Nat.add_zero] at hw
      exact Or.inr ⟨j, htag.trans (congrArg (fun d => gm06CutDart d 0) hw)⟩
    | true =>
      simp only [Bool.toNat_true] at hw
      have hqj : q = gm06CutDart (2 * (rep.tagged.length + k + j.val) + 1) 0 :=
        htag.trans (congrArg (fun d => gm06CutDart d 0) hw)
      exact False.elim (hnot (hqj.symm ▸ rep.negative_outer_is_last hG j))

end GM06CurrentDrawingRep
end GraphMinor.GM06
