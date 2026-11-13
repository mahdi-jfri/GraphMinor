module

public import GraphMinor.GM06.Alg57CurrentCuffWords
public import GraphMinor.GM06.Alg57CurrentLinkageEdges

/-!
# The exact retained ends of a linkage row

In the comparison drawing for Lemma 10 of VI (5.7), page 133, an
interior linkage row retains its two path ends. A start or terminal
also retains its two marked cuff ends. The actual path-key and cuff
word interpretations prove that these are precisely the ends selected
by the numeric linkage-and-cuff mask.
-/

@[expose] public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- The path and cuff ends retained at a decoded linkage vertex in
the linkage-and-cuff comparison of Lemma 10. -/
def cutBoundaryEnds : GM06CutPosition → List ℕ
  | .interior a b => [a, b]
  | .start b cp cn => [b, cp, cn]
  | .terminal a cp cn => [a, cp, cn]

/-- An undirected index occurs exactly when one of its two signed
ends occurs in the original list. -/
theorem edge_index_mem_iff (words : List ℕ) (d : ℕ) :
    d / 2 ∈ words.map (fun a => a / 2) ↔ d ∈ words ∨ gm06DartMate d ∈ words := by
  constructor
  · intro h
    obtain ⟨a, ha, had⟩ := List.mem_map.mp h
    have hm := Nat.mod_lt a (by decide : 0 < 2)
    have hd := Nat.mod_lt d (by decide : 0 < 2)
    have he : a = d ∨ a = gm06DartMate d := by
      unfold gm06DartMate
      split_ifs <;> omega
    exact he.elim (fun h => Or.inl (h ▸ ha)) (fun h => Or.inr (h ▸ ha))
  · intro h
    rcases h with h | h
    · exact List.mem_map.mpr ⟨d, h, rfl⟩
    · exact List.mem_map.mpr ⟨_, h, gm06DartMate_edge d⟩

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- For an ordinary word in a decoded linkage row, the comparison
mask keeps exactly its actual marked path ends. -/
theorem ordinary_keep_iff_pathEnd (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) {d : ℕ} (hd : d ∈ x.rotations.getD a.val [])
    (hb : d < 2 * rep.tagged.length) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) :
    gm06LinkageCuffKeep rep.tagged.length x.linkage d = true ↔ d ∈ p.pathEnds := by
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  have hz : (x.rotations.getD a.val [], a.val) ∈ x.rotations.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simp only [List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
  have ho := rep.ordinary_origin_row hG _ hz d hd hb
  have hlocal := gm06BuildCutTables_pathEnds_iff (m := rep.tagged.length) x.endpoints
    x.linkage x.innerCuff x.outerCuff (by rw [ho]; exact a.isLt)
      (rep.cut_path_keys_nodup true) (rep.cut_path_keys_nodup false)
  rw [ho, hp] at hlocal
  have hmarked : (∃ q, some p = some q ∧ d ∈ q.pathEnds) ↔ d ∈ p.pathEnds := by simp
  rw [hmarked] at hlocal
  simp only [gm06LinkageCuffKeep, decide_eq_true_eq, edge_index_mem_iff]
  have hnot : ¬ rep.tagged.length ≤ d / 2 := by omega
  simp only [hnot, false_or]
  exact hlocal.symm

/-- At every decoded linkage vertex, the computed comparison mask
retains exactly the path and cuff ends in its position data. -/
theorem keep_iff_boundaryEnd (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) {d : ℕ} (hd : d ∈ x.rotations.getD a.val [])
    (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) a.val = some p) :
    gm06LinkageCuffKeep rep.tagged.length x.linkage d = true ↔ d ∈ cutBoundaryEnds p := by
  by_cases hb : d < 2 * rep.tagged.length
  · rw [rep.ordinary_keep_iff_pathEnd hG a hd hb p hp]
    cases p with
    | interior c e => rfl
    | start b cp cn =>
      obtain ⟨i, _, hcp, hcn⟩ := rep.cut_start_markers hG.1 a hp
      have hnep : d ≠ cp := by omega
      have hnen : d ≠ cn := by omega
      simp only [GM06CutPosition.pathEnds, cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false,
        hnep, hnen]
    | terminal c cp cn =>
      obtain ⟨i, _, hcp, hcn⟩ := rep.cut_terminal_markers hG.1 a hp
      have hnep : d ≠ cp := by omega
      have hnen : d ≠ cn := by omega
      simp only [GM06CutPosition.pathEnds, cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false,
        hnep, hnen]
  · have hkeep : gm06LinkageCuffKeep rep.tagged.length x.linkage d = true := by
      simp only [gm06LinkageCuffKeep, decide_eq_true_eq]
      exact Or.inl (by omega)
    apply iff_of_true hkeep
    have hc := rep.cuff_word_at_position hG a hd (Nat.le_of_not_gt hb) p hp
    cases p with
    | interior c e => exact hc.elim
    | start b cp cn =>
      simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr hc
    | terminal c cp cn =>
      simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr hc

end GM06CurrentDrawingRep
end GraphMinor.GM06
