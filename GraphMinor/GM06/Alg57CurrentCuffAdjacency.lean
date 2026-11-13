module

public import GraphMinor.GM06.Alg57CurrentCutBlocks
public import GraphMinor.GM06.Alg57PersistentRowRotation
import GraphMinor.GM06.Alg57CurrentRows
import GraphMinor.GM06.Alg57CuffRotation
import GraphMinor.GM06.Alg57RegionIncidence

/-!
# Cuff adjacency in current rows with permanent labels

The two cap arguments for VI (5.7), page 133, determine the cuff
successors without any assumption on ordinary edge labels. We read
the drawing rotation from the positive permanent rows at live slots.
The fixed signed cuff labels then give exactly the cyclic index
conditions in every current cut block, including after deletions
leave gaps in the label space.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

private theorem idxOf_succ_of_formPerm {row : List ℕ} (hn : row.Nodup)
    {a b : ℕ} (ha : a ∈ row) (hb : b ∈ row) (hab : row.formPerm a = b) :
    row.idxOf b = (row.idxOf a + 1) % row.length := by
  have hlen : 0 < row.length := List.length_pos_of_mem ha
  have hi := List.idxOf_lt_length_of_mem ha
  have hh := List.formPerm_apply_getElem row hn (row.idxOf a) hi
  rw [List.getElem_idxOf, hab] at hh
  exact ((getElem_eq_iff_eq_idxOf hn hb (Nat.mod_lt _ hlen)).mp hh.symm).symm

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The two cuff families occupy the consecutive positions needed
by the local cut blocks. This follows from the positive input rows. -/
theorem cuff_row_adjacency (hG : IsCylinderSection5Drawing k G) :
    (∀ i : Fin k,
      (x.rotations.getD (rep.source i).val []).idxOf
        (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1) =
      ((x.rotations.getD (rep.source i).val []).idxOf
        (2 * (rep.tagged.length + i.val)) + 1) %
          (x.rotations.getD (rep.source i).val []).length) ∧
    (∀ i : Fin k,
      (x.rotations.getD (rep.target i).val []).idxOf
        (2 * (rep.tagged.length + k + i.val)) =
      ((x.rotations.getD (rep.target i).val []).idxOf
        (2 * (rep.tagged.length + k + gm06PreviousCuffIndex k i.val) + 1) + 1) %
          (x.rotations.getD (rep.target i).val []).length) := by
  classical
  let A := {a : Fin x.vertexCount // a ∈ rep.live}
  let vertex : A → OnePoint EuclideanPlane := fun a => cylinderToSphere (rep.vertex a.val)
  have hinj : Function.Injective vertex := by
    intro a b hab
    apply Subtype.ext
    exact rep.vertex_inj a.property b.property (injective_cylinderToSphere hab)
  let rows : OnePoint EuclideanPlane → List ℕ :=
    Function.extend vertex (fun a => x.rotations.getD a.val.val []) (fun _ => [])
  have hrows_at (a : Fin x.vertexCount) (ha : a ∈ rep.live) :
      rows (cylinderToSphere (rep.vertex a)) = x.rotations.getD a.val [] :=
    hinj.extend_apply _ _ ⟨a, ha⟩
  have hrowsΓ : ∀ v ∈ (cylinderSphereDrawing rep.cuffed).V,
      GM06PersistentRotationRowRep rep.label rep.par v (rows v) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := rep.sphere_vertex_cover hv
    rw [hrows_at a ha]
    exact rep.rows a ha
  have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ (cylinderSphereDrawing rep.cuffed).V :=
    fun h => infty_notMem_cylinderSphereDrawing_U rep.cuffed
      ((cylinderSphereDrawing rep.cuffed).V_subset_U h)
  obtain ⟨R, hR, hccw, _, hrot⟩ :=
    exists_ccwRotation_of_persistent_rows rep.edgePar hinf rows hrowsΓ
  choose fI hfI hlI using rep.inner_labels
  choose fO hfO hlO using rep.outer_labels
  have hmemI (i : Fin k) : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈
      (cylinderSphereDrawing rep.cuffed).E := by
    rw [← hfI i]
    exact (fI i).property
  have hmemO (i : Fin k) : cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) ∈
      (cylinderSphereDrawing rep.cuffed).E := by
    rw [← hfO i]
    exact (fO i).property
  let DI (i : Fin k) (b : Bool) : DrawingDart (cylinderSphereDrawing rep.cuffed) :=
    ⟨(cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), b), hmemI i⟩
  let DO (i : Fin k) (b : Bool) : DrawingDart (cylinderSphereDrawing rep.cuffed) :=
    ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1), b), hmemO i⟩
  have hlabelI (i : Fin k) (b : Bool) :
      persistentDartLabel rep.label (DI i b) = 2 * (rep.tagged.length + i.val) + b.toNat := by
    have hindex : (⟨(DI i b).val.1, (DI i b).property⟩ : (cylinderSphereDrawing rep.cuffed).E) =
        fI i := Subtype.ext (hfI i).symm
    simp only [persistentDartLabel, hindex, hlI, DI]
  have hlabelO (i : Fin k) (b : Bool) :
      persistentDartLabel rep.label (DO i b) = 2 * (rep.tagged.length + k + i.val) + b.toNat := by
    have hindex : (⟨(DO i b).val.1, (DO i b).property⟩ : (cylinderSphereDrawing rep.cuffed).E) =
        fO i := Subtype.ext (hfO i).symm
    simp only [persistentDartLabel, hindex, hlO, DO]
  constructor
  · intro i
    have hrotEq : R.rot (DI i false) = DI (finPredCycle i) true :=
      Subtype.ext (inner_cuff_rotation hG rep.subdrawing rep.cuffed_U rep.cuffed_V rep.edgePar hR hccw hmemI rep.inner_par i)
    have hv : dartVertex rep.par (DI i false) = cylinderToSphere (rep.vertex (rep.source i)) := by
      simp only [DI, dartVertex, endOf, Bool.false_eq_true, ↓reduceIte, rep.inner_par,
        (initialCuffGapCurve_props hG i).1, rep.source_point]
    have hh := hrot (DI i false)
    rw [hrotEq, hlabelI, hlabelI, hv, hrows_at _ (rep.source_live i)] at hh
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at hh
    have hcn := (rep.inner_markers hG (finPredCycle i)).2
    rw [finSuccCycle_pred_eq] at hcn
    rw [previousCuffIndex_eq_pred]
    exact idxOf_succ_of_formPerm (rep.rows (rep.source i) (rep.source_live i)).1
      (rep.inner_markers hG i).1 hcn hh.symm
  · intro i
    have hrotEq : R.rot (DO (finPredCycle i) true) = DO i false :=
      Subtype.ext (outer_cuff_rotation hG rep.subdrawing rep.cuffed_U rep.cuffed_V rep.edgePar hR hccw hmemO rep.outer_par i)
    have hv : dartVertex rep.par (DO (finPredCycle i) true) = cylinderToSphere (rep.vertex (rep.target i)) := by
      simp only [DO, dartVertex, endOf, ↓reduceIte, rep.outer_par,
        (alg511_outer_gap_ends hG (finPredCycle i)).2, finSuccCycle_pred_eq, rep.target_point]
    have hh := hrot (DO (finPredCycle i) true)
    rw [hrotEq, hlabelO, hlabelO, hv, hrows_at _ (rep.target_live i)] at hh
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at hh
    have hcn := (rep.outer_markers hG (finPredCycle i)).2
    rw [finSuccCycle_pred_eq] at hcn
    have hcp := (rep.outer_markers hG i).1
    rw [previousCuffIndex_eq_pred]
    exact idxOf_succ_of_formPerm (rep.rows (rep.target i) (rep.target_live i)).1 hcn hcp hh.symm

/-- Every split vertex in the actual computed cut satisfies
`CutBlockOK`, including the geometric order of its cuff ends. -/
theorem cut_block_ok (hG : IsCylinderSection5Drawing k G) :
    ∀ v row p, x.rotations[v]? = some row →
      gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
        x.endpoints x.linkage x.innerCuff x.outerCuff) v = some p → CutBlockOK p row := by
  obtain ⟨hinner, houter⟩ := rep.cuff_row_adjacency hG
  have hlen := rep.rows_length
  intro v row p hv hp
  have hvn : v < x.vertexCount := hlen ▸ (List.getElem?_eq_some_iff.mp hv).1
  let a : Fin x.vertexCount := ⟨v, hvn⟩
  have hrow : x.rotations.getD a.val [] = row := by
    rw [List.getD_eq_getElem?_getD, hv]
    rfl
  rw [← hrow]
  cases p with
  | interior c d => exact rep.cut_block_interior a hp
  | start b cp cn =>
    obtain ⟨hb, hcp, hcn, hbp, hbn, hpn⟩ := rep.cut_start_end_data hG a hp
    apply (cutBlockOK_start_iff _ _ _ _).mpr
    refine ⟨hb, hcp, hcn, hbp, hbn, hpn, ?_⟩
    obtain ⟨i, hi, hcpEq, hcnEq⟩ := rep.cut_start_markers hG.1 a hp
    simpa only [← hi, hcpEq, hcnEq] using hinner i
  | terminal c cp cn =>
    obtain ⟨hc, hcp, hcn, hcp', hcn', hpn⟩ := rep.cut_terminal_end_data hG a hp
    apply (cutBlockOK_terminal_iff _ _ _ _).mpr
    refine ⟨hc, hcp, hcn, hcp', hcn', hpn, ?_⟩
    obtain ⟨i, hi, hcpEq, hcnEq⟩ := rep.cut_terminal_markers hG.1 a hp
    simpa only [← hi, hcpEq, hcnEq] using houter i

end GM06CurrentDrawingRep
end GraphMinor.GM06
