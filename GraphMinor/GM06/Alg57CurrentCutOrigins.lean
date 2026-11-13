module

public import GraphMinor.GM06.Alg57CurrentFaceRow
public import GraphMinor.GM06.Alg57CutOriginProjection

/-!
# Interpreting copied origins in the current drawing

For VI (5.7), page 133, a computed copied origin projects to a live
original vertex and to the vertex of the corresponding drawing dart.
The numeric split face successor preserves active ends. These facts
let incidence bits be read as actual vertices rather than only darts.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- Every iterate of the numeric face successor stays among active
ends when the rows cover them and reversal preserves them. -/
theorem numeric_face_iterate_active (data : GM06CutData)
    (hn : data.rotations.flatten.Nodup)
    (hc : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hm : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    {c : ℕ} (hstart : c ∈ data.activeDarts) (n : ℕ) :
    (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm)^[n] c ∈ data.activeDarts := by
  induction n with
  | zero => exact hstart
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    apply (hc _).mpr
    apply gm06RotationPermutation_symm_mem _ hn
    rw [dartMatePerm_apply]
    exact (hc _).mp (hm _ ih)

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- A copied active end has a live original origin and names an
actual dart at precisely that vertex. -/
theorem cut_origin_point (live : List ℕ) {q : ℕ}
    (hq : q ∈ (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations live).activeDarts) :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations live
    ∃ a : Fin x.vertexCount, a.val = (data.origins[q]?.getD 0) / 2 ∧ a ∈ rep.live ∧
      ∃ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
        dartVertex rep.par d = cylinderToSphere (rep.vertex a) ∧
          persistentDartLabel rep.label d = gm06UncutDart q := by
  have hh := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hq
  have ho := cutOrigins_project_mem _ x.rotations rep.rows_flatten_nodup hh.2 hh.1
  dsimp only at ho ⊢
  have hb : ((gm06CutOrigins (rep.tagged.length + x.innerCuff.length + x.outerCuff.length)
      (gm06SplitRotationRows (gm06BuildCutTables x.vertexCount rep.tagged.length
        x.endpoints x.linkage x.innerCuff x.outerCuff) x.rotations))[q]?.getD 0) / 2 < x.vertexCount := by
    rw [rep.rows_length] at ho
    omega
  let a : Fin x.vertexCount := ⟨_, hb⟩
  have hmem : gm06UncutDart q ∈ x.rotations.getD a.val [] := ho.2
  have ha := rep.live_of_mem_row hmem
  obtain ⟨d, hd, hl⟩ := exists_persistentDart_of_mem_row (rep.rows a ha) hmem
  exact ⟨a, rfl, ha, d, hd, hl⟩

/-- The selected computed face row contains only active copied ends. -/
theorem cut_face_row_active (hG : IsCylinderSection5Drawing k G) (live : List ℕ) (i : Fin k)
    {row : List ℕ}
    (horbit : ∀ d : ℕ, d ∈ row ↔ ∃ j : ℕ,
      (dartMatePerm.trans (gm06RotationPermutation
        (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
          x.innerCuff x.outerCuff x.rotations live).rotations).symm)^[j]
        (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) = d) :
    ∀ q ∈ row, q ∈ (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations live).activeDarts := by
  obtain ⟨hn, _, _, hc, hm⟩ := rep.cut_data_face_encoding hG live
  have hstart := (hc _).mpr (rep.reverse_inner_mem_cut hG i)
  intro q hq
  obtain ⟨j, rfl⟩ := (horbit q).mp hq
  exact numeric_face_iterate_active _ hn hc hm hstart j

end GM06CurrentDrawingRep
end GraphMinor.GM06
