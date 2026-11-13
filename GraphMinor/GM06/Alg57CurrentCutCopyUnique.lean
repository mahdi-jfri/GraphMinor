module

public import GraphMinor.GM06.Alg57CurrentCutSideLabels
public import GraphMinor.GM06.Alg57CutOriginProjection
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Alg57CuffRotation

/-!
# Distinct vertex copies in the selected face

For the injectivity needed in Lemma 10 of VI (5.7), page 133,
the two copies of a linkage vertex lie on different selected
faces when there are at least two paths. Their strip labels
would otherwise identify a path with its cyclic predecessor.
Unmarked vertices have only a left copy.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- A decoded split position is at a vertex of an actual linkage
path. This follows directly from its incoming or outgoing write. -/
theorem exists_path_of_cut_position (a : Fin x.vertexCount) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) :
    ∃ j : Fin k, rep.vertex a ∈ (L.pathDrawing j).V := by
  have hword : ∃ (incoming : Bool) (d : ℕ), d ∈ x.linkage.flatten ∧
      x.endpoints[if incoming then gm06DartMate d else d]?.getD 0 = a.val := by
    cases p with
    | interior d e =>
      have hout := ((computedCutPosition_interior_iff _ _ _ _).mp hp).2
      obtain ⟨he, horg⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
        x.innerCuff x.outerCuff a.isLt hout
      exact ⟨false, e, he, horg⟩
    | start e cp cn =>
      have hout := ((computedCutPosition_start_iff _ _ _ _ _).mp hp).2.1
      obtain ⟨he, horg⟩ := gm06BuildCutTables_outgoing_source x.endpoints x.linkage
        x.innerCuff x.outerCuff a.isLt hout
      exact ⟨false, e, he, horg⟩
    | terminal d cp cn =>
      have hin := ((computedCutPosition_terminal_iff _ _ _ _ _).mp hp).1
      obtain ⟨hd, horg⟩ := gm06BuildCutTables_incoming_source x.endpoints x.linkage
        x.innerCuff x.outerCuff a.isLt hin
      exact ⟨true, gm06DartMate d, hd, by simpa only [ite_true, gm06DartMate_involutive d] using horg⟩
  obtain ⟨incoming, d, hd, horg⟩ := hword
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
  let j' : Fin k := ⟨j, rep.linkage.1 ▸ hj⟩
  obtain ⟨v, hv, _, hvP⟩ := rep.path_origin_mem j' incoming hd
  have hva : v = a := Fin.ext (hv.symm.trans horg)
  exact ⟨j', hva ▸ hvP⟩

/-- The selected cut orbit cannot visit both copies of any old
vertex when at least two linkage paths are present. -/
theorem cut_iterates_not_both_copies (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (n₁ n₂ : ℕ) (a : Fin x.vertexCount)
    (hleft : (dartMatePerm.trans (gm06RotationPermutation (gm06SplitRotationRows
      (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff) x.rotations)).symm)^[n₁]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) ∈
      (gm06SplitRotationRows (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
        x.linkage x.innerCuff x.outerCuff) x.rotations).getD (gm06CutVertex a.val true) [])
    (hright : (dartMatePerm.trans (gm06RotationPermutation (gm06SplitRotationRows
      (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff) x.rotations)).symm)^[n₂]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) ∈
      (gm06SplitRotationRows (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
        x.linkage x.innerCuff x.outerCuff) x.rotations).getD (gm06CutVertex a.val false) []) : False := by
  let marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
    x.innerCuff x.outerCuff
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  cases hp : gm06CutPositionAt marks a.val with
  | none =>
    rw [splitRows_getD marks x.rotations a.val hi false, hp] at hright
    change _ ∈ ((x.rotations.getD a.val []).filter (fun _ => false)).map
      (fun d => gm06CutDart d 0) at hright
    simp only [List.filter_false, List.map_nil] at hright
    exact List.not_mem_nil hright
  | some p =>
    obtain ⟨j, hj⟩ := rep.exists_path_of_cut_position a p hp
    have hjU := (L.pathDrawing j).V_subset_U hj
    have hji := rep.cut_iterate_path_side hG i n₁ a j hjU p hp true hleft
    have hpred := rep.cut_iterate_path_side hG i n₂ a j hjU p hp false hright
    simp only [ite_true] at hji
    simp only [Bool.false_eq_true, ite_false] at hpred
    have hfixed : finPredCycle j = j := hpred.trans hji.symm
    exact finSuccCycle_ne_of_one_lt hk j
      ((congrArg finSuccCycle hfixed).symm.trans (finSuccCycle_pred_eq j))

end GM06CurrentDrawingRep
end GraphMinor.GM06
