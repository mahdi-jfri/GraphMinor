module

public import GraphMinor.GM06.Alg57InputCutFits
import GraphMinor.GM06.Section5Red
import GraphMinor.Compute.GM06Alg511DartKeys

/-!
# The distinguished inner cuff dart and the computed cut ends

The selected face in VI (5.7), page 133, starts at the reverse inner
cuff dart. Its reverse must not be a first dart of a retained block.
Path ends have ordinary labels, negative cuff ends have odd labels,
and positive terminal ends have outer cuff labels. These three facts
exclude the selected positive inner end from every first position.
We also read ordinary dart membership directly in the geometric input
rows, using the supplied endpoint orientation.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06SuccessorInputRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
include rep

/-- Each linkage word lies in the original ordinary dart space. -/
theorem path_word_lt {d : ℕ} (hd : d ∈ x.linkage.flatten) : d < 2 * rep.graph.pairs.length := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨_, _, henc, _⟩ := rep.linkage.path ⟨i, rep.linkage.1 ▸ hi⟩
  have hh := (henc.active_words d hd).1
  simpa only [GM06SuccessorGraphRep.initialTagged, List.length_map] using hh

/-- Every decoded path end has an ordinary dart label. -/
theorem cut_path_end_lt (v : Fin x.vertexCount) {p : GM06CutPosition}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.graph.pairs.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some p)
    {d : ℕ} (hd : d ∈ p.pathEnds) : d < 2 * rep.graph.pairs.length := by
  have hh := (gm06CutPositionAt_pathEnds_iff _ v.val d).mp ⟨p, hp, hd⟩
  rcases hh with hh | hh
  · have h := rep.path_word_lt (gm06BuildCutTables_incoming_source x.endpoints x.linkage
      x.innerCuff x.outerCuff v.isLt hh).1
    simpa only [gm06DartMate_involutive d] using gm06DartMate_lt h
  · exact rep.path_word_lt (gm06BuildCutTables_outgoing_source x.endpoints x.linkage
      x.innerCuff x.outerCuff v.isLt hh).1

/-- A decoded start has the signed markers of its actual inner
cuff vertex. -/
theorem cut_start_markers (hk : 0 < k) (v : Fin x.vertexCount) {b cp cn : ℕ}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.graph.pairs.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some (.start b cp cn)) :
    ∃ i : Fin k, rep.source i = v ∧ cp = 2 * (rep.graph.pairs.length + i.val) ∧
      cn = 2 * (rep.graph.pairs.length + gm06PreviousCuffIndex k i.val) + 1 := by
  obtain ⟨hin, hout, hcp, hcn⟩ := (computedCutPosition_start_iff _ _ _ _ _).mp hp
  obtain ⟨i, hi⟩ := rep.source_of_marks v hin (by rw [hout]; omega)
  refine ⟨i, hi, ?_, ?_⟩
  · rw [← hi] at hcp
    exact hcp.symm.trans (rep.cut_source_cuff_marks hk i).1
  · rw [← hi] at hcn
    exact hcn.symm.trans (rep.cut_source_cuff_marks hk i).2

/-- A decoded terminal has the signed markers of its actual outer
cuff vertex. -/
theorem cut_terminal_markers (hk : 0 < k) (v : Fin x.vertexCount) {a cp cn : ℕ}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.graph.pairs.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some (.terminal a cp cn)) :
    ∃ i : Fin k, rep.target i = v ∧ cp = 2 * (rep.graph.pairs.length + k + i.val) ∧
      cn = 2 * (rep.graph.pairs.length + k + gm06PreviousCuffIndex k i.val) + 1 := by
  obtain ⟨hin, hout, hcp, hcn⟩ := (computedCutPosition_terminal_iff _ _ _ _ _).mp hp
  obtain ⟨i, hi⟩ := rep.target_of_marks v (by rw [hin]; omega) hout
  refine ⟨i, hi, ?_, ?_⟩
  · rw [← hi] at hcp
    exact hcp.symm.trans (rep.cut_target_cuff_marks hk i).1
  · rw [← hi] at hcn
    exact hcn.symm.trans (rep.cut_target_cuff_marks hk i).2

/-- The positive inner cuff end is never first in a split block. -/
theorem cutFirst_ne_positive_inner (hk : 0 < k) (i : Fin k) (v : Fin x.vertexCount)
    {p : GM06CutPosition}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.graph.pairs.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some p) (left : Bool) :
    cutFirst p left ≠ 2 * (rep.graph.pairs.length + i.val) := by
  cases p with
  | interior a b =>
    have ha := rep.cut_path_end_lt v hp (d := a) (by simp [GM06CutPosition.pathEnds])
    have hb := rep.cut_path_end_lt v hp (d := b) (by simp [GM06CutPosition.pathEnds])
    cases left <;> simp only [cutFirst_eq] <;> omega
  | start b cp cn =>
    have hb := rep.cut_path_end_lt v hp (d := b) (by simp [GM06CutPosition.pathEnds])
    obtain ⟨j, _, _, hcn⟩ := rep.cut_start_markers hk v hp
    cases left <;> simp only [cutFirst_eq] <;> omega
  | terminal a cp cn =>
    have ha := rep.cut_path_end_lt v hp (d := a) (by simp [GM06CutPosition.pathEnds])
    obtain ⟨j, _, hcp, _⟩ := rep.cut_terminal_markers hk v hp
    cases left <;> simp only [cutFirst_eq] <;> omega

/-- The hypothesis excluding a first dart applies to the reverse
of the selected reverse inner cuff dart, as required by the cut
face-orbit projection theorem. -/
theorem reverse_inner_cut_mate_not_first (hk : 0 < k) (i : Fin k) :
    gm06DartMate (gm06CutDart (2 * (rep.graph.pairs.length + i.val) + 1) 0) ∉
      cutFirstDarts (gm06BuildCutTables x.vertexCount rep.graph.pairs.length
        x.endpoints x.linkage x.innerCuff x.outerCuff) x.rotations := by
  have hm : gm06DartMate (2 * (rep.graph.pairs.length + i.val) + 1) =
      2 * (rep.graph.pairs.length + i.val) := by simp [gm06DartMate]
  rw [← gm06CutDart_mate, hm]
  apply cutDart_not_mem_cutFirstDarts
  intro v row p left hv hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _⟩ := rep.rotations
  have hvn : v < x.vertexCount := hlen ▸ (List.getElem?_eq_some_iff.mp hv).1
  exact rep.cutFirst_ne_positive_inner hk i ⟨v, hvn⟩ hp left

/-- An ordinary directed word whose endpoint is `v` occurs in the
actual counterclockwise row at `v`, with the supplied orientation. -/
theorem ordinary_word_mem_row (v : Fin x.vertexCount) (d : ℕ)
    (hd : d < 2 * rep.graph.pairs.length) (hv : x.endpoints[d]?.getD 0 = v.val) :
    d ∈ x.rotations.getD v.val [] := by
  obtain ⟨F, e, γ, _, _, _, _, he, _, _, hends, _, _, _, hrows⟩ := rep.rotations
  let j : Fin rep.graph.pairs.length := ⟨d / 2, by omega⟩
  obtain ⟨hzero, hone⟩ := gm06Alg511EndpointWords_getD
    (rep.graph.pairs.map fun p => (p.1.val, p.2.val)) j.val (by simpa only [List.length_map] using j.isLt)
  simp only [List.getElem_map] at hzero hone
  rw [← rep.graph.endpoints] at hzero hone
  simp only [List.getD_eq_getElem?_getD] at hzero hone
  by_cases hpar : d % 2 = 0
  · have hcode : d = 2 * j.val := by dsimp only [j]; omega
    have hvertex : rep.graph.pairs[j.val].1 = v := Fin.ext
      (hzero.symm.trans (by simpa only [← hcode] using hv))
    have hm := marker_mem (hrows v).to_cuffRotation (j.castAdd (k + k)) false (by
      change γ (e (j.castAdd (k + k))).val 0 = _
      rw [he, (hends j).1, hvertex])
    simpa only [Fin.val_castAdd, Bool.toNat_false, Nat.add_zero, ← hcode] using hm
  · have hcode : d = 2 * j.val + 1 := by dsimp only [j]; omega
    have hvertex : rep.graph.pairs[j.val].2 = v := Fin.ext
      (hone.symm.trans (by simpa only [← hcode] using hv))
    have hm := marker_mem (hrows v).to_cuffRotation (j.castAdd (k + k)) true (by
      change γ (e (j.castAdd (k + k))).val 1 = _
      rw [he, (hends j).2, hvertex])
    simpa only [Fin.val_castAdd, Bool.toNat_true, ← hcode] using hm

end GM06SuccessorInputRep
end GraphMinor.GM06
