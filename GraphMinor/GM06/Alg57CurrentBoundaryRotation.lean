module

public import GraphMinor.GM06.Alg57BoundaryRowRotation
public import GraphMinor.GM06.Alg57FilterCornerLabels

/-!
# Comparison predecessors in actual current rows

The exact boundary mask proved for VI (5.7), page 133, lets the local
boundary rotation table be read in the actual filtered arrays. The
corner labels merge across removed ends, so the old predecessor of
a block's last end has the label of the block's first end. These
are the transitions used to follow the two sides of each path row.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The actual comparison row equals the filter to its decoded
path and cuff boundary ends. -/
theorem comparison_row_eq_boundary (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) :
    (x.rotations.getD a.val []).filter (gm06LinkageCuffKeep rep.tagged.length x.linkage) =
      (x.rotations.getD a.val []).filter (fun d => decide (d ∈ cutBoundaryEnds p)) := by
  apply List.filter_congr
  intro d hd
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using rep.keep_iff_boundaryEnd hG a hd p hp

/-- Each local block's boundary predecessor is read correctly in
the actual filtered current row. -/
theorem comparison_row_prev_last (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) (left : Bool) :
    ((x.rotations.getD a.val []).filter
      (gm06LinkageCuffKeep rep.tagged.length x.linkage)).formPerm.symm (cutLast p left) =
        cutFirst p left := by
  rw [rep.comparison_row_eq_boundary hG a p hp]
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  have hrow : x.rotations[a.val]? = some (x.rotations.getD a.val []) := by
    simp only [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
  have hmem : x.rotations.getD a.val [] ∈ x.rotations := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  exact boundaryRow_prev_last ((List.nodup_flatten.mp rep.rows_flatten_nodup).1 _ hmem)
    (rep.cut_block_ok hG _ _ _ hrow hp) left

/-- For corner labels that merge at removed ends, the old predecessor
of the last end has exactly the label of the first boundary end. -/
theorem comparison_corner_prev_last {β : Type*} (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p)
    (g : ℕ → β)
    (hskip : ∀ d ∈ x.rotations.getD a.val [],
      gm06LinkageCuffKeep rep.tagged.length x.linkage d = false →
        g ((x.rotations.getD a.val []).formPerm.symm d) = g d) (left : Bool) :
    g ((x.rotations.getD a.val []).formPerm.symm (cutLast p left)) = g (cutFirst p left) := by
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  have hrow : x.rotations[a.val]? = some (x.rotations.getD a.val []) := by
    simp only [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
  have hok := rep.cut_block_ok hG _ _ _ hrow hp
  obtain ⟨_, hl, _, _⟩ := cutBlock_spec hok left
  have hk : gm06LinkageCuffKeep rep.tagged.length x.linkage (cutLast p left) = true := by
    apply (rep.keep_iff_boundaryEnd hG a hl p hp).mpr
    cases p <;> cases left <;> simp only [cutLast_eq, cutBoundaryEnds, List.mem_cons,
      List.not_mem_nil, or_false, true_or, or_true, eq_self]
  have hn : (x.rotations.getD a.val []).Nodup :=
    (List.nodup_flatten.mp rep.rows_flatten_nodup).1 _ (by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi)
  have hh := formPerm_filter_symm_label _ hn _ g hskip hl hk
  rw [rep.comparison_row_prev_last hG a p hp left] at hh
  exact hh.symm

end GM06CurrentDrawingRep
end GraphMinor.GM06
