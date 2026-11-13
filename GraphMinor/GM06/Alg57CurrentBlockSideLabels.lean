module

public import GraphMinor.GM06.Alg57CurrentStripCornerLabels
public import GraphMinor.GM06.Alg57CutBlockCornerLabels
import GraphMinor.GM06.Section4PathTools

/-!
# Strip labels of the first ends of current cut blocks

For Lemma 10 in VI (5.7), page 133, the first end at the left copy
of a linkage vertex has the following strip's label. At the right
copy it has the preceding strip's label. Path ends are read from
the actual path rows. At the inner cuff the signed gap gives the
label directly. At the outer cuff the face predecessor gives it.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- A current path end at a vertex on a specified linkage path
belongs to that path's row, since the linkage paths are disjoint. -/
theorem path_word_mem_of_origin {d : ℕ} (hd : d ∈ x.linkage.flatten)
    (incoming : Bool) (a : Fin x.vertexCount) (j : Fin k)
    (horigin : x.endpoints[if incoming then gm06DartMate d else d]?.getD 0 = a.val)
    (ha : rep.vertex a ∈ (L.pathDrawing j).U) :
    d ∈ (x.linkage[j.val]'(by rw [rep.linkage.1]; exact j.isLt)) := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  let i' : Fin k := ⟨i, rep.linkage.1 ▸ hi⟩
  obtain ⟨v, hv, _, hvP⟩ := rep.path_origin_mem i' incoming hd
  have hva : v = a := Fin.ext (hv.symm.trans horigin)
  have hij : i' = j := by
    by_contra hne
    exact disjoint_left.mp (L.pairwise_disjoint hne)
      ((L.pathDrawing i').V_subset_U (hva ▸ hvP)) ha
  simpa only [← hij] using hd

/-- The first ends of the left and right local blocks carry the
following and preceding strip labels of their actual path. -/
theorem block_first_corner_labels {β : Type*} (hG : IsCylinderSection5Drawing k G)
    (g : ℕ → β)
    (hskip : ∀ row ∈ x.rotations, ∀ r ∈ row,
      gm06LinkageCuffKeep rep.tagged.length x.linkage r = false → g (row.formPerm.symm r) = g r)
    (hface : ∀ r ∈ x.rotations.flatten,
      g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm) r) = g r)
    (a : Fin x.vertexCount) (j : Fin k) (ha : rep.vertex a ∈ (L.pathDrawing j).U)
    (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) :
    g (cutFirst p true) = g (2 * (rep.tagged.length + j.val) + 1) ∧
      g (cutFirst p false) =
        g (2 * (rep.tagged.length + gm06PreviousCuffIndex k j.val) + 1) := by
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  have hrow : x.rotations.getD a.val [] ∈ x.rotations := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hlabels := rep.path_corner_labels hG g hskip hface
  cases p with
  | interior d e =>
    obtain ⟨hin, hout⟩ := (computedCutPosition_interior_iff _ _ _ _).mp hp
    obtain ⟨hd, hdorg⟩ := gm06BuildCutTables_incoming_source x.endpoints x.linkage
      x.innerCuff x.outerCuff a.isLt hin
    obtain ⟨he, heorg⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
      x.innerCuff x.outerCuff a.isLt hout
    have hdj := rep.path_word_mem_of_origin hd true a j
      (by simpa only [Bool.true_eq, ite_true, gm06DartMate_involutive d] using hdorg) ha
    have hej := rep.path_word_mem_of_origin he false a j heorg ha
    simpa only [cutFirst_eq, gm06DartMate_involutive d] using
      And.intro (hlabels j e hej).1 (hlabels j (gm06DartMate d) hdj).2
  | start e cp cn =>
    obtain ⟨_, hout, _, _⟩ := (computedCutPosition_start_iff _ _ _ _ _).mp hp
    obtain ⟨he, heorg⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
      x.innerCuff x.outerCuff a.isLt hout
    have hej := rep.path_word_mem_of_origin he false a j heorg ha
    obtain ⟨i, hia, _, hcn⟩ := rep.cut_start_markers hG.1 a hp
    have hij : i = j := by
      by_contra hne
      apply disjoint_left.mp (L.pairwise_disjoint hne) _ ha
      rw [← hia, rep.source_point]
      exact (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
    subst i
    exact ⟨by simpa only [cutFirst_eq] using (hlabels j e hej).1,
      by simp only [cutFirst_eq, hcn]⟩
  | terminal d cp cn =>
    obtain ⟨hin, _, _, _⟩ := (computedCutPosition_terminal_iff _ _ _ _ _).mp hp
    obtain ⟨hd, hdorg⟩ := gm06BuildCutTables_incoming_source x.endpoints x.linkage
      x.innerCuff x.outerCuff a.isLt hin
    have hdj := rep.path_word_mem_of_origin hd true a j
      (by simpa only [Bool.true_eq, ite_true, gm06DartMate_involutive d] using hdorg) ha
    have hf := hlabels j (gm06DartMate d) hdj
    have hprev := rep.comparison_corner_prev_last hG a (.terminal d cp cn) hp g
      (hskip _ hrow) true
    simp only [cutFirst_eq, cutLast_eq] at hprev
    have hm : d ∈ x.rotations.getD a.val [] := by
      have hh := rep.cut_block_ok hG a.val (x.rotations.getD a.val []) _ (by
        simp only [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]) hp
      exact ((cutBlockOK_terminal_iff _ _ _ _).mp hh).1
    have hfd := hface _ (rep.path_word_ends_in_rotation hd).1
    simp only [Equiv.trans_apply, dartMatePerm_apply, gm06DartMate_involutive d,
      rotationPermutation_symm_apply_row _ rep.rows_flatten_nodup _ hrow _ hm] at hfd
    exact ⟨by simpa only [cutFirst_eq] using hprev.symm.trans (hfd.trans hf.1),
      by simpa only [cutFirst_eq, gm06DartMate_involutive d] using hf.2⟩

end GM06CurrentDrawingRep
end GraphMinor.GM06
