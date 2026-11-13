module

public import GraphMinor.GM06.Alg57CurrentPathChains
public import GraphMinor.GM06.Alg57CurrentCutOrbit

/-!
# Exact cut positions along current path rows

For Lemma 10 in VI (5.7), page 133, the first word of a linkage row
is its source's outgoing mark. Consecutive words give the incoming
reverse and outgoing marks of their common vertex. The scatter-key
uniqueness already proved for the actual linkage therefore gives
these exact decoded cut positions, with no supplied position table.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- Every active ordinary end occurs in the actual current rotation
table at its stored origin. -/
theorem active_word_in_rotation {d : ℕ} (hd : d < 2 * rep.tagged.length)
    (ha : (rep.tagged[d / 2]'(by omega)).2 = 1) : d ∈ x.rotations.flatten := by
  let a : Fin x.vertexCount := ⟨x.endpoints[d]?.getD 0, rep.ordinary_origin_lt hd⟩
  have hm := rep.ordinary_word_mem_row a d hd ha rfl
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  rw [List.getD_eq_getElem _ _ hi] at hm
  exact List.mem_flatten.mpr ⟨_, List.getElem_mem hi, hm⟩

/-- Both orientations of every actual linkage edge occur in the
current rotation table, with permanent labels unchanged. -/
theorem path_word_ends_in_rotation {d : ℕ} (hd : d ∈ x.linkage.flatten) :
    d ∈ x.rotations.flatten ∧ gm06DartMate d ∈ x.rotations.flatten := by
  obtain ⟨hb, ha⟩ := rep.path_word_active hd
  have hm := gm06DartMate_lt hb
  exact ⟨rep.active_word_in_rotation hb ha, rep.active_word_in_rotation hm
    (by simpa only [gm06DartMate_edge] using ha)⟩

/-- The computed source position has the actual first path word
and the two prescribed signed inner cuff ends. -/
theorem cut_source_position_of_first (hk : 0 < k) (i : Fin k) (d : ℕ) (rest : List ℕ)
    (hrow : (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) = d :: rest) :
    gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff) (rep.source i).val =
        some (.start d (2 * (rep.tagged.length + i.val))
          (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1)) := by
  have hd : d ∈ x.linkage.flatten := List.mem_flatten.mpr
    ⟨_, List.getElem_mem _, hrow.symm ▸ List.mem_cons_self⟩
  have ho := rep.linkage_first_origin i d rest hrow
  have hh := gm06BuildCutTables_outgoing_at (m := rep.tagged.length) x.endpoints x.linkage
    x.innerCuff x.outerCuff hd (by rw [ho]; exact (rep.source i).isLt) (rep.cut_path_keys_nodup false)
  rw [ho] at hh
  apply (computedCutPosition_start_iff _ _ _ _ _).mpr
  exact ⟨rep.source_incoming_zero i, congrArg (fun q => q.getD 0) hh, rep.cut_source_cuff_marks hk i⟩

/-- The common vertex of two consecutive actual path words has
exactly their arriving reverse and leaving word as its cut position. -/
theorem cut_position_of_consecutive {d e : ℕ} (hd : d ∈ x.linkage.flatten)
    (he : e ∈ x.linkage.flatten)
    (hchain : x.endpoints[gm06DartMate d]?.getD 0 = x.endpoints[e]?.getD 0) :
    gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff) (x.endpoints[e]?.getD 0) =
        some (.interior (gm06DartMate d) e) := by
  have hi := gm06BuildCutTables_incoming_at (m := rep.tagged.length) x.endpoints x.linkage
    x.innerCuff x.outerCuff hd (rep.cut_path_origin_lt true hd) (rep.cut_path_keys_nodup true)
  have ho := gm06BuildCutTables_outgoing_at (m := rep.tagged.length) x.endpoints x.linkage
    x.innerCuff x.outerCuff he (rep.cut_path_origin_lt false he) (rep.cut_path_keys_nodup false)
  rw [hchain] at hi
  exact gm06CutPositionAt_interior _ _ _ _ hi ho

end GM06CurrentDrawingRep
end GraphMinor.GM06
