module

public import GraphMinor.GM06.Alg57CurrentBlockSideLabels
public import GraphMinor.GM06.Alg57CopiedCornerLabels
import GraphMinor.Compute.GM06FaceRowsProgram

/-!
# Side labels of the actual selected cut orbit

For Lemma 10 of VI (5.7), page 133, projection preserves the corner
label around the selected cut orbit. That orbit avoids the last
ends of local blocks. Reading a marked copied slot thus gives the
strip label of its left or right boundary, with every premise
derived from the current drawing and its rows.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- No selected current cut-face iterate is a last local block end. -/
theorem cut_iterate_not_last (hG : IsCylinderSection5Drawing k G) (i : Fin k) (n : ℕ) :
    let marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff
    (dartMatePerm.trans (gm06RotationPermutation
      (gm06SplitRotationRows marks x.rotations)).symm)^[n]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) ∉ cutLastDarts marks x.rotations := by
  exact cut_face_iterate_not_last _ _ rep.rows_flatten_nodup (rep.cut_block_ok hG)
    (rep.cut_fits hG.1) (fun _ h => rep.cut_rows_mate hG h)
    (rep.reverse_inner_mem_cut hG i) (rep.reverse_inner_cut_mate_not_first hG.1 i) n

/-- The projected label of every selected cut-face iterate is the
label at its selecting reverse inner gap. -/
theorem cut_iterate_corner_label {β : Type*} (hG : IsCylinderSection5Drawing k G)
    (g : ℕ → β)
    (hface : ∀ r ∈ x.rotations.flatten,
      g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm) r) = g r)
    (i : Fin k) (n : ℕ) :
    let marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff
    g (gm06UncutDart ((dartMatePerm.trans (gm06RotationPermutation
      (gm06SplitRotationRows marks x.rotations)).symm)^[n]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0))) =
        g (2 * (rep.tagged.length + i.val) + 1) := by
  dsimp only
  rw [cut_face_orbit_projection_of_fits _ _ rep.rows_flatten_nodup (rep.cut_block_ok hG)
    (rep.cut_fits hG.1) (fun _ h => rep.cut_rows_mate hG h)
    (rep.reverse_inner_mem_cut hG i) (rep.reverse_inner_cut_mate_not_first hG.1 i) n,
    gm06UncutDart_cut _ 0 (by decide)]
  have hc : 2 * (rep.tagged.length + i.val) + 1 ∈ x.rotations.flatten :=
    ((rep.cut_copies hG _ 0 (by decide)).mp (rep.reverse_inner_mem_cut hG i)).1
  have hall : ∀ j, (dartMatePerm.trans (gm06RotationPermutation x.rotations).symm)^[j]
      (2 * (rep.tagged.length + i.val) + 1) ∈ x.rotations.flatten ∧
      g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm)^[j]
        (2 * (rep.tagged.length + i.val) + 1)) = g (2 * (rep.tagged.length + i.val) + 1) := by
    intro j
    induction j with
    | zero => exact ⟨hc, rfl⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨?_, (hface _ ih.1).trans ih.2⟩
      apply gm06RotationPermutation_symm_mem _ rep.rows_flatten_nodup
      rw [dartMatePerm_apply]
      exact rep.rows_mate ih.1
  exact (hall n).2

/-- Reading a selected face end in either actual marked copied slot
returns precisely the first-end label of that local block. -/
theorem cut_iterate_slot_corner_label {β : Type*} (hG : IsCylinderSection5Drawing k G)
    (g : ℕ → β)
    (hskip : ∀ row ∈ x.rotations, ∀ r ∈ row,
      gm06LinkageCuffKeep rep.tagged.length x.linkage r = false → g (row.formPerm.symm r) = g r)
    (i : Fin k) (n : ℕ) (a : Fin x.vertexCount) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) (left : Bool)
    (hslot : (dartMatePerm.trans (gm06RotationPermutation (gm06SplitRotationRows
      (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff) x.rotations)).symm)^[n]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) ∈
      (gm06SplitRotationRows (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
        x.linkage x.innerCuff x.outerCuff) x.rotations).getD (gm06CutVertex a.val left) []) :
    g (gm06UncutDart ((dartMatePerm.trans (gm06RotationPermutation (gm06SplitRotationRows
      (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff) x.rotations)).symm)^[n]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0))) = g (cutFirst p left) := by
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  have hrow : x.rotations.getD a.val [] ∈ x.rotations := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  apply copied_corner_label hi hp
    ((List.nodup_flatten.mp rep.rows_flatten_nodup).1 _ hrow)
    (rep.cut_block_ok hG _ _ _ (by
      simp only [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]) hp) g _ left hslot
    (rep.cut_iterate_not_last hG i n)
  intro d hd hbd
  apply hskip _ hrow d hd
  cases hk : gm06LinkageCuffKeep rep.tagged.length x.linkage d with
  | false => rfl
  | true => exact False.elim (hbd ((rep.keep_iff_boundaryEnd hG a hd p hp).mp hk))

/-- A selected face end at a left linkage copy belongs to the
selecting path. At a right copy its path has the selecting path as
predecessor. The strip labels are constructed from the drawing. -/
theorem cut_iterate_path_side (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (n : ℕ) (a : Fin x.vertexCount) (j : Fin k)
    (ha : rep.vertex a ∈ (L.pathDrawing j).U) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) (left : Bool)
    (hslot : (dartMatePerm.trans (gm06RotationPermutation (gm06SplitRotationRows
      (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff) x.rotations)).symm)^[n]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) ∈
      (gm06SplitRotationRows (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
        x.linkage x.innerCuff x.outerCuff) x.rotations).getD (gm06CutVertex a.val left) []) :
    (if left then j else finPredCycle j) = i := by
  obtain ⟨H, _, _, _, g, hskip, hface, _, _, hdistinct⟩ := rep.exists_strip_corner_labels hG
  have hlabel := (rep.cut_iterate_slot_corner_label hG g hskip i n a p hp left hslot).symm.trans
    (rep.cut_iterate_corner_label hG g hface i n)
  have hfirst := rep.block_first_corner_labels hG g hskip hface a j ha p hp
  cases left with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    apply hdistinct (finPredCycle j) i
    rw [hfirst.2] at hlabel
    simpa only [previousCuffIndex_eq_pred] using hlabel
  | true =>
    simp only [ite_true]
    exact hdistinct j i (hfirst.1.symm.trans hlabel)

end GM06CurrentDrawingRep
end GraphMinor.GM06
