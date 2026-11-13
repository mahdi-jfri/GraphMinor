module

public import GraphMinor.GM06.Alg57CurrentPathPositions
public import GraphMinor.GM06.Alg57CurrentBoundaryRotation

/-!
# Corner labels along consecutive linkage words

For Lemma 10 of VI (5.7), page 133, the forward ends of a path have
the comparison-region label of its following strip. Its reversed
ends have the preceding strip label. The first word is read at its
actual source position. At consecutive words the exact interior
position and old face successor carry each side label to the next.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

private theorem row_mem (a : Fin x.vertexCount) : x.rotations.getD a.val [] ∈ x.rotations := by
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem face_label_at_row {β : Type*} (g : ℕ → β)
    (hface : ∀ r ∈ x.rotations.flatten,
      g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm) r) = g r)
    {r : ℕ} (hr : r ∈ x.rotations.flatten) (a : Fin x.vertexCount)
    (hm : gm06DartMate r ∈ x.rotations.getD a.val []) :
    g ((x.rotations.getD a.val []).formPerm.symm (gm06DartMate r)) = g r := by
  have hh := hface r hr
  simpa only [Equiv.trans_apply, dartMatePerm_apply,
    rotationPermutation_symm_apply_row _ rep.rows_flatten_nodup _ (rep.row_mem a) _ hm] using hh

/-- Consecutive current path words carry the same forward-side
label and the same reverse-side label. All positions and row reads
are those computed from the actual linkage arrays. -/
theorem path_corner_step {β : Type*} (hG : IsCylinderSection5Drawing k G) (g : ℕ → β)
    (hskip : ∀ row ∈ x.rotations, ∀ r ∈ row,
      gm06LinkageCuffKeep rep.tagged.length x.linkage r = false → g (row.formPerm.symm r) = g r)
    (hface : ∀ r ∈ x.rotations.flatten,
      g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm) r) = g r)
    {d e : ℕ} (hd : d ∈ x.linkage.flatten) (he : e ∈ x.linkage.flatten)
    (hchain : x.endpoints[gm06DartMate d]?.getD 0 = x.endpoints[e]?.getD 0) :
    g e = g d ∧ g (gm06DartMate e) = g (gm06DartMate d) := by
  let a : Fin x.vertexCount := ⟨x.endpoints[e]?.getD 0, rep.cut_path_origin_lt false he⟩
  have hp := rep.cut_position_of_consecutive hd he hchain
  obtain ⟨hdb, hda⟩ := rep.path_word_active hd
  obtain ⟨heb, hea⟩ := rep.path_word_active he
  have hdmb := gm06DartMate_lt hdb
  have hdma : (rep.tagged[gm06DartMate d / 2]'(by omega)).2 = 1 := by
    simpa only [gm06DartMate_edge] using hda
  have hmd := rep.ordinary_word_mem_row a _ hdmb hdma hchain
  have hme := rep.ordinary_word_mem_row a e heb hea rfl
  have hleft := rep.comparison_corner_prev_last hG a (.interior (gm06DartMate d) e) hp
    g (hskip _ (rep.row_mem a)) true
  have hright := rep.comparison_corner_prev_last hG a (.interior (gm06DartMate d) e) hp
    g (hskip _ (rep.row_mem a)) false
  simp only [cutFirst_eq, cutLast_eq] at hleft hright
  have hfwd := rep.face_label_at_row g hface (rep.path_word_ends_in_rotation hd).1 a hmd
  have hrev := rep.face_label_at_row g hface (rep.path_word_ends_in_rotation he).2 a
    (by simpa only [gm06DartMate_involutive e] using hme)
  simp only [gm06DartMate_involutive e] at hrev
  exact ⟨hleft.symm.trans hfwd, hrev.symm.trans hright⟩

/-- The first forward path end has its following inner-gap label.
The first reverse end has the signed preceding-gap label. -/
theorem path_corner_first {β : Type*} (hG : IsCylinderSection5Drawing k G) (g : ℕ → β)
    (hskip : ∀ row ∈ x.rotations, ∀ r ∈ row,
      gm06LinkageCuffKeep rep.tagged.length x.linkage r = false → g (row.formPerm.symm r) = g r)
    (hface : ∀ r ∈ x.rotations.flatten,
      g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm) r) = g r)
    (i : Fin k) (d : ℕ) (rest : List ℕ)
    (hrow : (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) = d :: rest) :
    g d = g (2 * (rep.tagged.length + i.val) + 1) ∧
      g (gm06DartMate d) = g (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1) := by
  let a := rep.source i
  have hp := rep.cut_source_position_of_first hG.1 i d rest hrow
  have hd : d ∈ x.linkage.flatten := List.mem_flatten.mpr
    ⟨_, List.getElem_mem _, hrow.symm ▸ List.mem_cons_self⟩
  obtain ⟨hdb, hda⟩ := rep.path_word_active hd
  have hmd := rep.ordinary_word_mem_row a d hdb hda (rep.linkage_first_origin i d rest hrow)
  have hleft := rep.comparison_corner_prev_last hG a
    (.start d (2 * (rep.tagged.length + i.val))
      (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1)) hp
    g (hskip _ (rep.row_mem a)) true
  have hright := rep.comparison_corner_prev_last hG a
    (.start d (2 * (rep.tagged.length + i.val))
      (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1)) hp
    g (hskip _ (rep.row_mem a)) false
  simp only [cutFirst_eq, cutLast_eq] at hleft hright
  have hc : 2 * (rep.tagged.length + i.val) + 1 ∈ x.rotations.flatten :=
    List.mem_flatten.mpr ⟨_, rep.row_mem (rep.source (finSuccCycle i)), (rep.inner_markers hG i).2⟩
  have hmate : gm06DartMate (2 * (rep.tagged.length + i.val) + 1) =
      2 * (rep.tagged.length + i.val) := by simp [gm06DartMate]
  have hfwd := rep.face_label_at_row g hface hc a
    (by rw [hmate]; exact (rep.inner_markers hG i).1)
  rw [hmate] at hfwd
  have hrev := rep.face_label_at_row g hface (rep.path_word_ends_in_rotation hd).2 a
    (by simpa only [gm06DartMate_involutive d] using hmd)
  simp only [gm06DartMate_involutive d] at hrev
  exact ⟨hleft.symm.trans hfwd, hrev.symm.trans hright⟩

omit rep in
private theorem label_eq_head_of_chain {β : Type*} (g : ℕ → β) (a : ℕ) (rest : List ℕ)
    (hc : List.IsChain (fun d e => g d = g e) (a :: rest)) :
    ∀ d ∈ a :: rest, g d = g a := by
  induction rest generalizing a with
  | nil => intro d hd; exact congrArg g (List.mem_singleton.mp hd)
  | cons b rest ih =>
    obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp hc
    intro d hd
    rcases List.mem_cons.mp hd with h | h
    · exact congrArg g h
    · exact (ih b htail d h).trans hab.symm

/-- Every forward end in an actual linkage row has the label of
its following inner gap. Every reverse end has the preceding gap
label. This follows the exact finite path chain, including its ends. -/
theorem path_corner_labels {β : Type*} (hG : IsCylinderSection5Drawing k G) (g : ℕ → β)
    (hskip : ∀ row ∈ x.rotations, ∀ r ∈ row,
      gm06LinkageCuffKeep rep.tagged.length x.linkage r = false → g (row.formPerm.symm r) = g r)
    (hface : ∀ r ∈ x.rotations.flatten,
      g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm) r) = g r)
    (i : Fin k) :
    ∀ d ∈ (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)),
      g d = g (2 * (rep.tagged.length + i.val) + 1) ∧
        g (gm06DartMate d) = g (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1) := by
  have hmem (d : ℕ) (hd : d ∈ (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt))) :
      d ∈ x.linkage.flatten := List.mem_flatten.mpr ⟨_, List.getElem_mem _, hd⟩
  have hforward : List.IsChain (fun d e => g d = g e)
      (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) := by
    apply (rep.linkage_origin_chain i).imp_of_mem_imp
    intro d e hd he hc
    exact (rep.path_corner_step hG g hskip hface (hmem d hd) (hmem e he) hc).1.symm
  have hreverse : List.IsChain (fun d e => g (gm06DartMate d) = g (gm06DartMate e))
      (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) := by
    apply (rep.linkage_origin_chain i).imp_of_mem_imp
    intro d e hd he hc
    exact (rep.path_corner_step hG g hskip hface (hmem d hd) (hmem e he) hc).2.symm
  cases hrow : x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt) with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons first rest =>
    obtain ⟨hfirst, hfirstRev⟩ := rep.path_corner_first hG g hskip hface i first rest hrow
    rw [hrow] at hforward hreverse
    intro d hd
    exact ⟨(label_eq_head_of_chain g first rest hforward d hd).trans hfirst,
      (label_eq_head_of_chain (fun q => g (gm06DartMate q)) first rest hreverse d hd).trans hfirstRev⟩

end GM06CurrentDrawingRep
end GraphMinor.GM06
