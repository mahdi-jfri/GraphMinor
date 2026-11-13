module

public import GraphMinor.GM06.Alg57ComputedPathRows
import GraphMinor.Compute.GM06CutOriginFacts
import GraphMinor.Compute.GM06CutPathMembership
import GraphMinor.Compute.GM06FaceRowsProgram

/-!
# Ordinary and path edge ends in the current cut

VI (5.7), page 133, keeps each ordinary edge's geometric meaning
when its endpoints are split. Projecting the computed origin gives
the original endpoint. The endpoint array therefore supplies the
actual link between the two projected copied vertices. On a
linkage edge the copy tag also determines each endpoint's side.
These facts follow from the row scatter and the actual path marks.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)

/-- The origin of an active ordinary copied end projects to the
endpoint recorded by its original word. -/
theorem cut_ordinary_origin (hG : IsCylinderSection5Drawing k G) {q : ℕ}
    (hq : q ∈ (currentCut).activeDarts) (hd : gm06UncutDart q < 2 * rep.tagged.length) :
    (currentCut).origins[q]?.getD 0 / 2 = x.endpoints[gm06UncutDart q]?.getD 0 := by
  have hact := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hq
  have ho := cutOrigins_project_mem _ x.rotations rep.rows_flatten_nodup hact.2 hact.1
  have hv : (currentCut).origins[q]?.getD 0 / 2 < x.vertexCount := by
    have hh := (rep.cut_origins_valid q hq).1
    omega
  let a : Fin x.vertexCount := ⟨_, hv⟩
  have hm : gm06UncutDart q ∈ x.rotations.getD a.val [] := ho.2
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  have hz : (x.rotations.getD a.val [], a.val) ∈ x.rotations.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simp only [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
  exact (rep.ordinary_origin_row hG _ hz _ hm hd).symm

/-- Every active ordinary copied edge is the actual graph edge
joining its two projected copied origins. -/
theorem cut_ordinary_isLink (hG : IsCylinderSection5Drawing k G) {q : ℕ}
    (hq : q ∈ (currentCut).activeDarts) (hd : gm06UncutDart q < 2 * rep.tagged.length) :
    ∃ u w : Fin (2 * x.vertexCount),
      (currentCut).origins[q]?.getD 0 = u.val ∧
      (currentCut).origins[gm06DartMate q]?.getD 0 = w.val ∧
      G.toGraph.IsLink (rep.cutEdgePoint (q / 2)) (rep.cutVertexPoint u) (rep.cutVertexPoint w) := by
  obtain ⟨_, _, _, _, hmate⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hmq := hmate q hq
  let u : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[q]?.getD 0, (rep.cut_origins_valid q hq).1⟩
  let w : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[gm06DartMate q]?.getD 0,
    (rep.cut_origins_valid _ hmq).1⟩
  let d : Fin (2 * rep.tagged.length) := ⟨gm06UncutDart q, hd⟩
  have horg := rep.cut_ordinary_origin hG hq hd
  have hmd : gm06UncutDart (gm06DartMate q) < 2 * rep.tagged.length := by
    rw [gm06UncutDart_mate]
    exact gm06DartMate_lt hd
  have hmorg := rep.cut_ordinary_origin hG hmq hmd
  rw [gm06UncutDart_mate] at hmorg
  have hread := gm06Dart_endpoint_words rep.tagged d
  rw [← rep.endpoints] at hread
  have htail : rep.cutVertexPoint u = rep.vertex (gm06DartTail rep.tagged d) :=
    congrArg rep.vertex (Fin.ext (horg.trans hread.1))
  have hhead : rep.cutVertexPoint w = rep.vertex (gm06DartHead rep.tagged d) :=
    congrArg rep.vertex (Fin.ext (hmorg.trans hread.2))
  have hact := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hq
  have ho := cutOrigins_project_mem _ x.rotations rep.rows_flatten_nodup hact.2 hact.1
  have hv : u.val / 2 < x.vertexCount := by have hh := u.isLt; omega
  have ha := rep.row_ordinary_active hG ⟨u.val / 2, hv⟩ ho.2 hd
  have hlink := gm06Dart_isLink G.toGraph rep.tagged rep.vertex rep.edge rep.links d ha
  have he : rep.cutEdgePoint (q / 2) = rep.edge ⟨d.val / 2, by have hh := d.isLt; omega⟩ := by
    have hindex : q / 2 / 2 = d.val / 2 := by
      dsimp only [d]
      unfold gm06UncutDart
      omega
    simp only [cutEdgePoint, hindex, show d.val / 2 < rep.tagged.length by have hh := d.isLt; omega,
      dite_true]
  exact ⟨u, w, rfl, rfl, by rw [he, htail, hhead]; exact hlink⟩

/-- Each copied linkage end is at the copy prescribed by its edge
tag. This includes a reversed arriving word at a terminal vertex. -/
theorem cut_path_copy_origin {d : ℕ}
    (hdpath : d ∈ x.linkage.flatten ∨ gm06DartMate d ∈ x.linkage.flatten) (left : Bool) :
    (currentCut).origins[gm06CutDart d (!left).toNat]?.getD 0 =
      gm06CutVertex (x.endpoints[d]?.getD 0) left := by
  have hd : d < 2 * rep.tagged.length := by
    rcases hdpath with h | h
    · exact rep.path_word_lt h
    · simpa only [gm06DartMate_involutive d] using gm06DartMate_lt (rep.path_word_lt h)
  have ha : (rep.tagged[d / 2]'(by omega)).2 = 1 := by
    rcases hdpath with h | h
    · exact (rep.path_word_active h).2
    · simpa only [gm06DartMate_edge] using (rep.path_word_active h).2
  have hv := rep.ordinary_origin_lt hd
  let a : Fin x.vertexCount := ⟨x.endpoints[d]?.getD 0, hv⟩
  have hrow := rep.ordinary_word_mem_row a d hd ha rfl
  obtain ⟨p, hp, hend⟩ := (gm06BuildCutTables_pathEnds_iff (m := rep.tagged.length)
    x.endpoints x.linkage x.innerCuff x.outerCuff hv
    (rep.cut_path_keys_nodup true) (rep.cut_path_keys_nodup false)).mpr hdpath
  have hcopy : gm06CutDart d (!left).toNat ∈ gm06CutRotation p (x.rotations.getD a.val []) left := by
    cases left with
    | false => exact (gm06CutRotation_path_mem p _ d hrow hend).2
    | true => exact (gm06CutRotation_path_mem p _ d hrow hend).1
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  have hslot : gm06CutDart d (!left).toNat ∈
      (currentCut).rotations.getD (gm06CutVertex a.val left) [] := by
    dsimp only [gm06CutDataOfLinkage]
    rw [splitRows_getD_of_position hi hp left]
    exact hcopy
  have hslotBound : gm06CutVertex a.val left < (currentCut).rotations.length := by
    simp only [gm06CutDataOfLinkage, gm06SplitRotationRows_length, rep.rows_length]
    have hh := a.isLt
    cases left <;> simp only [gm06CutVertex, Bool.not_true, Bool.not_false,
      Bool.toNat_false, Bool.toNat_true] <;> omega
  have hflat : gm06CutDart d (!left).toNat ∈ (currentCut).rotations.flatten := by
    rw [List.getD_eq_getElem _ _ hslotBound] at hslot
    exact List.mem_flatten.mpr ⟨_, List.getElem_mem hslotBound, hslot⟩
  have hbound : gm06CutDart d (!left).toNat <
      4 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length) := by
    have hm := Nat.mod_lt d (by decide : 0 < 2)
    cases left <;> simp only [gm06CutDart, Bool.not_true, Bool.not_false,
      Bool.toNat_false, Bool.toNat_true] <;> omega
  apply (gm06CutOrigins_row_iff _ (gm06SplitRotationRows_nodup _ _ rep.rows_flatten_nodup)
    hflat hbound hslotBound).mpr
  rw [List.getD_eq_getElem _ _ hslotBound] at hslot
  exact hslot

end GM06CurrentDrawingRep
end GraphMinor.GM06
