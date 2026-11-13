module

public import GraphMinor.GM06.Alg57CurrentLinkageCuffRows
public import GraphMinor.GM06.Alg57IndexedRowRotation
import GraphMinor.GM06.Alg57RegionIncidence
import GraphMinor.GM11.NiceStatements
import Mathlib.Data.List.GetD

/-!
# The numeric rotation of the linkage and cuff comparison

For Lemma 10 in the proof of VI (5.7), page 133, the filtered current
rows give the actual counterclockwise rotation of the linkage and cuff
subdrawing. The live original labels still cover all its vertices.
Its point set is connected because every linkage path meets the inner
cuff and at least one of them joins the two cuffs.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- The linkage and both cuffs form a connected point set. This is
the boundary comparison for the local side proof of VI (5.7). -/
theorem isConnected_linkage_union_boundary {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) :
    IsConnected ((⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder) := by
  let i : Fin k := ⟨0, hk⟩
  let a := cylinderM1Point k i
  have ha : a ∈ cylinderCuff1 := rfl
  have hC := isConnected_of_isOArc isOArc_cylinderCuff1
  have hP (j : Fin k) : IsConnected (L.pathDrawing j).U := by
    rw [← (L.curve_parametrizes j).2.1]
    exact isConnected_range (L.curve j).continuous
  have hjoin (j : Fin k) : (cylinderCuff1 ∩ (L.pathDrawing j).U).Nonempty := by
    refine ⟨cylinderM1Point k j, rfl, ?_⟩
    rw [← (L.curve_parametrizes j).2.1]
    exact ⟨0, (L.curve_parametrizes j).2.2.1⟩
  have hinner : IsConnected (cylinderCuff1 ∪ ⋃ j : Fin k, (L.pathDrawing j).U) := by
    refine ⟨⟨a, Or.inl ha⟩, isPreconnected_of_forall a (fun x hx => ?_)⟩
    rcases hx with hx | hx
    · exact ⟨cylinderCuff1, subset_union_left, ha, hx, hC.isPreconnected⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact ⟨cylinderCuff1 ∪ (L.pathDrawing j).U,
        union_subset_union_right _ (subset_iUnion (fun a : Fin k => (L.pathDrawing a).U) j), Or.inl ha, Or.inr hj,
        (hC.union (hjoin j) (hP j)).isPreconnected⟩
  have htarget : L.curve i 1 ∈ cylinderCuff2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [← hj]
    rfl
  have htP : L.curve i 1 ∈ ⋃ j : Fin k, (L.pathDrawing j).U := by
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← (L.curve_parametrizes i).2.1]
    exact mem_range_self 1
  have hboth := hinner.union ⟨L.curve i 1, Or.inr htP, htarget⟩
    (isConnected_of_isOArc isOArc_cylinderCuff2)
  simpa only [bd_closedCylinder, union_assoc, union_comm cylinderCuff1] using hboth

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The actual linkage and cuff comparison has the counterclockwise
rotation computed by filtering the permanent current rows. Its point
set is connected. All geometric and row premises are constructed. -/
theorem exists_linkage_cuff_rotation (hG : IsCylinderSection5Drawing k G) :
    ∃ (H : Drawing ClosedCylinder) (hHF : H.IsSubdrawing rep.cuffed)
      (R : DartRotation (DrawingDart (cylinderSphereDrawing H))),
      H.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder ∧
      H.V = ⋃ j : Fin k, (L.pathDrawing j).V ∧
      (∀ j : Fin k, (L.pathDrawing j).IsSubdrawing H) ∧
      (∀ e, e ∈ H.E ↔ e ∈ rep.cuffed.E ∧
        ((∃ j : Fin k, e ∈ (L.pathDrawing j).E) ∨ e ⊆ bd ClosedCylinder)) ∧
      IsConnected H.U ∧
      IsDrawingRotation (cylinderSphereDrawing H) rep.par R ∧
      IsCcwRotation (cylinderSphereDrawing H) rep.par R ∧
      R.rev = dartFlip (cylinderSphereDrawing H) ∧
      ∀ d, persistentDartLabel
        (gm06RestrictEdgeLabels (cylinderSphereDrawing_isSubdrawing hHF) rep.label) (R.rot d) =
        gm06RotationPermutation
          (x.rotations.map (List.filter (gm06LinkageCuffKeep rep.tagged.length x.linkage)))
          (persistentDartLabel
            (gm06RestrictEdgeLabels (cylinderSphereDrawing_isSubdrawing hHF) rep.label) d) := by
  classical
  obtain ⟨H, hHF, hHU, hHV, hPH, hHE, hrows⟩ := rep.exists_linkage_cuff_rows hG
  have hS := cylinderSphereDrawing_isSubdrawing hHF
  let label := gm06RestrictEdgeLabels hS rep.label
  let vertex := fun a : Fin x.vertexCount => cylinderToSphere (rep.vertex a)
  let keep := gm06LinkageCuffKeep rep.tagged.length x.linkage
  let rows := x.rotations.map (List.filter keep)
  have hγ := edgePar_of_subdrawing hS rep.edgePar
  have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ (cylinderSphereDrawing H).V := by
    intro h
    exact infty_notMem_cylinderSphereDrawing_U rep.cuffed
      ((cylinderSphereDrawing rep.cuffed).V_subset_U (hS.1 h))
  have hinj : InjOn vertex (↑rep.live : Set (Fin x.vertexCount)) := by
    intro a ha b hb hab
    exact rep.vertex_inj ha hb (injective_cylinderToSphere hab)
  have hcover : ∀ v ∈ (cylinderSphereDrawing H).V, ∃ a ∈ rep.live, vertex a = v := by
    intro v hv
    exact rep.sphere_vertex_cover (hS.1 hv)
  have hlen : rows.length = x.vertexCount := by simp only [rows, List.length_map, rep.rows_length]
  have hnd : rows.flatten.Nodup := by
    rw [show rows.flatten = x.rotations.flatten.filter keep from (List.filter_flatten).symm]
    exact rep.rows_flatten_nodup.filter keep
  have hindexed : ∀ a ∈ rep.live,
      GM06PersistentRotationRowRep label rep.par (vertex a) (rows.getD a.val []) := by
    intro a ha
    change GM06PersistentRotationRowRep label rep.par (vertex a)
      ((x.rotations.map (List.filter keep)).getD a.val (List.filter keep []))
    rw [List.getD_map]
    exact hrows a ha
  obtain ⟨R, hR, hccw, hrev, hrot⟩ := exists_ccwRotation_of_indexed_rows label hγ hinf
    vertex rep.live hinj hcover rows hlen hnd hindexed
  exact ⟨H, hHF, R, hHU, hHV, hPH, hHE, hHU.symm ▸ isConnected_linkage_union_boundary hG.1 L,
    hR, hccw, hrev, hrot⟩

end GM06CurrentDrawingRep
end GraphMinor.GM06
