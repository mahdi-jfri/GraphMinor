module

public import GraphMinor.GM06.Alg57InputCutBlocks
import GraphMinor.GM06.Alg57CuffRotation
import GraphMinor.GM06.Alg57RowRotation
import GraphMinor.GM06.Alg57RegionIncidence

/-!
# Cuff adjacency in the actual input rows

For the cut in VI (5.7), page 133, the two inner cuff ends are
consecutive with the positive end first. The two outer ends are
consecutive with the negative end first. The positive row charts
give a counterclockwise drawing rotation. The cap argument fixes
its successor at each cuff vertex, and the row interpretation turns
that successor into the required cyclic index equation.
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

namespace GM06SuccessorInputRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
include rep

/-- The two cuff families occupy the consecutive positions needed
by the local cut blocks. This follows from the positive input rows. -/
theorem cuff_row_adjacency (hG : IsCylinderSection5Drawing k G) :
    (∀ i : Fin k,
      (x.rotations.getD (rep.source i).val []).idxOf
        (2 * (rep.graph.pairs.length + gm06PreviousCuffIndex k i.val) + 1) =
      ((x.rotations.getD (rep.source i).val []).idxOf
        (2 * (rep.graph.pairs.length + i.val)) + 1) %
          (x.rotations.getD (rep.source i).val []).length) ∧
    (∀ i : Fin k,
      (x.rotations.getD (rep.target i).val []).idxOf
        (2 * (rep.graph.pairs.length + k + i.val)) =
      ((x.rotations.getD (rep.target i).val []).idxOf
        (2 * (rep.graph.pairs.length + k + gm06PreviousCuffIndex k i.val) + 1) + 1) %
          (x.rotations.getD (rep.target i).val []).length) := by
  classical
  obtain ⟨F, e, γ, hGF, hFU, hFV, hγ, he, heI, heO, hends, hγI, hγO, hlen, hrows⟩ :=
    rep.rotations
  let vertex : Fin x.vertexCount → OnePoint EuclideanPlane :=
    fun a => cylinderToSphere (rep.graph.vertex a).val
  have hinj : Function.Injective vertex :=
    injective_cylinderToSphere.comp rep.graph.vertexLabels.injective
  let rows : OnePoint EuclideanPlane → List ℕ :=
    Function.extend vertex (fun a => x.rotations.getD a.val []) (fun _ => [])
  have hrows_at (a : Fin x.vertexCount) : rows (vertex a) = x.rotations.getD a.val [] :=
    hinj.extend_apply _ _ a
  have hrowsΓ : ∀ v ∈ (cylinderSphereDrawing F).V,
      GM06SuccessorRotationRowRep e γ v (rows v) := by
    intro v hv
    rw [cylinderSphereDrawing_V, hFV] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    obtain ⟨a, ha⟩ := rep.graph.vertex.surjective ⟨p, hp⟩
    have hpa : (rep.graph.vertex a).val = p := congrArg Subtype.val ha
    rw [← hpa]
    change GM06SuccessorRotationRowRep e γ (vertex a) (rows (vertex a))
    rw [hrows_at]
    exact hrows a
  have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ (cylinderSphereDrawing F).V :=
    fun h => infty_notMem_cylinderSphereDrawing_U F ((cylinderSphereDrawing F).V_subset_U h)
  obtain ⟨R, hR, hccw, _, hrot⟩ := exists_ccwRotation_of_rows hγ hinf rows hrowsΓ
  have hmemI (i : Fin k) : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈
      (cylinderSphereDrawing F).E := by
    rw [← heI i]
    exact (e ((i.castAdd k).natAdd rep.graph.pairs.length)).property
  have hmemO (i : Fin k) : cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) ∈
      (cylinderSphereDrawing F).E := by
    rw [← heO i]
    exact (e ((i.natAdd k).natAdd rep.graph.pairs.length)).property
  let DI (i : Fin k) (b : Bool) : DrawingDart (cylinderSphereDrawing F) :=
    ⟨(cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), b), hmemI i⟩
  let DO (i : Fin k) (b : Bool) : DrawingDart (cylinderSphereDrawing F) :=
    ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1), b), hmemO i⟩
  have hlabelI (i : Fin k) (b : Bool) :
      dartLabel e (DI i b) = 2 * (rep.graph.pairs.length + i.val) + b.toNat := by
    have hindex : (⟨(DI i b).val.1, (DI i b).property⟩ : (cylinderSphereDrawing F).E) =
        e ((i.castAdd k).natAdd rep.graph.pairs.length) := Subtype.ext (heI i).symm
    simp only [dartLabel, hindex, Equiv.symm_apply_apply, Fin.val_natAdd, Fin.val_castAdd, DI]
  have hlabelO (i : Fin k) (b : Bool) :
      dartLabel e (DO i b) = 2 * (rep.graph.pairs.length + k + i.val) + b.toNat := by
    have hindex : (⟨(DO i b).val.1, (DO i b).property⟩ : (cylinderSphereDrawing F).E) =
        e ((i.natAdd k).natAdd rep.graph.pairs.length) := Subtype.ext (heO i).symm
    simp only [dartLabel, hindex, Equiv.symm_apply_apply, Fin.val_natAdd, DO]
    omega
  constructor
  · intro i
    have hrotEq : R.rot (DI i false) = DI (finPredCycle i) true :=
      Subtype.ext (inner_cuff_rotation hG hGF hFU hFV hγ hR hccw hmemI hγI i)
    have hv : dartVertex γ (DI i false) = vertex (rep.source i) := by
      simp only [DI, dartVertex, endOf, Bool.false_eq_true, ↓reduceIte, hγI,
        (initialCuffGapCurve_props hG i).1, vertex, rep.source_point]
    have hh := hrot (DI i false)
    rw [hrotEq, hlabelI, hlabelI, hv, hrows_at] at hh
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at hh
    have hcn := (rep.inner_markers hG (finPredCycle i)).2
    rw [finSuccCycle_pred_eq] at hcn
    rw [previousCuffIndex_eq_pred]
    exact idxOf_succ_of_formPerm (hrows (rep.source i)).1
      (rep.inner_markers hG i).1 hcn hh.symm
  · intro i
    have hrotEq : R.rot (DO (finPredCycle i) true) = DO i false :=
      Subtype.ext (outer_cuff_rotation hG hGF hFU hFV hγ hR hccw hmemO hγO i)
    have hv : dartVertex γ (DO (finPredCycle i) true) = vertex (rep.target i) := by
      simp only [DO, dartVertex, endOf, ↓reduceIte, hγO,
        (alg511_outer_gap_ends hG (finPredCycle i)).2, finSuccCycle_pred_eq, vertex, rep.target_point]
    have hh := hrot (DO (finPredCycle i) true)
    rw [hrotEq, hlabelO, hlabelO, hv, hrows_at] at hh
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at hh
    have hcn := (rep.outer_markers hG (finPredCycle i)).2
    rw [finSuccCycle_pred_eq] at hcn
    have hcp := (rep.outer_markers hG i).1
    simp only [← Nat.add_assoc] at hcp hcn
    rw [previousCuffIndex_eq_pred]
    exact idxOf_succ_of_formPerm (hrows (rep.target i)).1 hcn hcp hh.symm

/-- Every split vertex in the actual computed cut satisfies
`CutBlockOK`, including the geometric order of its cuff ends. -/
theorem cut_block_ok (hG : IsCylinderSection5Drawing k G) :
    ∀ v row p, x.rotations[v]? = some row →
      gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.graph.pairs.length
        x.endpoints x.linkage x.innerCuff x.outerCuff) v = some p → CutBlockOK p row := by
  obtain ⟨hinner, houter⟩ := rep.cuff_row_adjacency hG
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _⟩ := rep.rotations
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

end GM06SuccessorInputRep
end GraphMinor.GM06
