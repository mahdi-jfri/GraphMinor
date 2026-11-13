module

public import GraphMinor.GM06.Alg57CurrentCutFits
public import GraphMinor.GM06.Alg57InputCutEnds
import GraphMinor.GM06.Section5Red

/-!
# The actual ends of current split blocks

The current cut in VI (5.7), page 133, uses permanent ordinary
labels and the fixed cuff bases. Each decoded path end is active,
and its endpoint word selects a live vertex. The positive inner
cuff word is excluded from every first position by the same label
bounds as initially. Marker membership is read from the positive
permanent rows at the live cuff vertices.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- A current geometric row contains each labelled end at its vertex. -/
theorem GM06PersistentRotationRowRep.marker_mem
    {Γ : Drawing (OnePoint EuclideanPlane)} {label : Γ.E ↪ ℕ}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {v : OnePoint EuclideanPlane} {row : List ℕ}
    (hrow : GM06PersistentRotationRowRep label γ v row) (f : Γ.E) (b : Bool)
    (hend : γ f.val (endOf b) = v) : 2 * label f + b.toNat ∈ row := by
  let a : halfEdges Γ γ v := ⟨(f.val, b), f.property, hend⟩
  exact (hrow.2.1 _).mpr ⟨a, rfl⟩

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- Each current path word names an active ordinary edge slot. -/
theorem path_word_active {d : ℕ} (hd : d ∈ x.linkage.flatten) :
    ∃ h : d < 2 * rep.tagged.length, (rep.tagged[d / 2]'(by omega)).2 = 1 := by
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨_, _, henc, _⟩ := rep.linkage.path ⟨i, rep.linkage.1 ▸ hi⟩
  exact henc.active_words d hd

/-- Every decoded path end has an ordinary dart label. -/
theorem cut_path_end_lt (v : Fin x.vertexCount) {p : GM06CutPosition}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some p)
    {d : ℕ} (hd : d ∈ p.pathEnds) : d < 2 * rep.tagged.length := by
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
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some (.start b cp cn)) :
    ∃ i : Fin k, rep.source i = v ∧ cp = 2 * (rep.tagged.length + i.val) ∧
      cn = 2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1 := by
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
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some (.terminal a cp cn)) :
    ∃ i : Fin k, rep.target i = v ∧ cp = 2 * (rep.tagged.length + k + i.val) ∧
      cn = 2 * (rep.tagged.length + k + gm06PreviousCuffIndex k i.val) + 1 := by
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
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some p) (left : Bool) :
    cutFirst p left ≠ 2 * (rep.tagged.length + i.val) := by
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
    gm06DartMate (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) ∉
      cutFirstDarts (gm06BuildCutTables x.vertexCount rep.tagged.length
        x.endpoints x.linkage x.innerCuff x.outerCuff) x.rotations := by
  have hm : gm06DartMate (2 * (rep.tagged.length + i.val) + 1) =
      2 * (rep.tagged.length + i.val) := by simp [gm06DartMate]
  rw [← gm06CutDart_mate, hm]
  apply cutDart_not_mem_cutFirstDarts
  intro v row p left hv hp
  have hlen := rep.rows_length
  have hvn : v < x.vertexCount := hlen ▸ (List.getElem?_eq_some_iff.mp hv).1
  exact rep.cutFirst_ne_positive_inner hk i ⟨v, hvn⟩ hp left

/-- A decoded current path end names an active edge, also when it
is the reverse of the listed arriving word. -/
theorem cut_path_end_active (v : Fin x.vertexCount) {p : GM06CutPosition}
    (hp : gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) v.val = some p)
    {d : ℕ} (hd : d ∈ p.pathEnds) :
    (rep.tagged[d / 2]'(by have h := rep.cut_path_end_lt v hp hd; omega)).2 = 1 := by
  have hh := (gm06CutPositionAt_pathEnds_iff _ v.val d).mp ⟨p, hp, hd⟩
  rcases hh with hh | hh
  · obtain ⟨_, hactive⟩ := rep.path_word_active
      (gm06BuildCutTables_incoming_source x.endpoints x.linkage
        x.innerCuff x.outerCuff v.isLt hh).1
    simpa only [gm06DartMate_edge] using hactive
  · exact (rep.path_word_active (gm06BuildCutTables_outgoing_source x.endpoints x.linkage
      x.innerCuff x.outerCuff v.isLt hh).1).2

/-- A current active ordinary word occurs in the row selected by
its endpoint array, whose vertex slot is necessarily live. -/
theorem ordinary_word_mem_row (v : Fin x.vertexCount) (d : ℕ)
    (hd : d < 2 * rep.tagged.length)
    (hactive : (rep.tagged[d / 2]'(by omega)).2 = 1)
    (hv : x.endpoints[d]?.getD 0 = v.val) : d ∈ x.rotations.getD v.val [] := by
  let j : Fin rep.tagged.length := ⟨d / 2, by omega⟩
  obtain ⟨f, hf, hlabel⟩ := rep.ordinary_labels j hactive
  have hread := (gm06Dart_endpoint_words rep.tagged ⟨d, hd⟩).1
  rw [← rep.endpoints] at hread
  by_cases hpar : d % 2 = 0
  · have htail : rep.tagged[j.val].1.1 = v := Fin.ext (by
      simpa only [gm06DartTail, hpar, ↓reduceIte] using hread.symm.trans hv)
    have hvLive : v ∈ rep.live := htail ▸ (rep.ends_live j hactive).1
    have hm := (rep.rows v hvLive).marker_mem f false (by
      change rep.par f.val 0 = _
      rw [hf, (rep.ordinary_ends j hactive).1]
      simp only [Fin.getElem_fin, htail])
    rw [hlabel] at hm
    have hcode : 2 * j.val + false.toNat = d := by simp only [Bool.toNat_false]; dsimp [j]; omega
    exact hcode ▸ hm
  · have htail : rep.tagged[j.val].1.2 = v := Fin.ext (by
      simpa only [gm06DartTail, hpar, ↓reduceIte] using hread.symm.trans hv)
    have hvLive : v ∈ rep.live := htail ▸ (rep.ends_live j hactive).2
    have hm := (rep.rows v hvLive).marker_mem f true (by
      change rep.par f.val 1 = _
      rw [hf, (rep.ordinary_ends j hactive).2]
      simp only [Fin.getElem_fin, htail])
    rw [hlabel] at hm
    have hcode : 2 * j.val + true.toNat = d := by simp only [Bool.toNat_true]; dsimp [j]; omega
    exact hcode ▸ hm

/-- The current inner cuff ends occur at their fixed live sources. -/
theorem inner_markers (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    2 * (rep.tagged.length + i.val) ∈ x.rotations.getD (rep.source i).val [] ∧
    2 * (rep.tagged.length + i.val) + 1 ∈
      x.rotations.getD (rep.source (finSuccCycle i)).val [] := by
  obtain ⟨f, hf, hlabel⟩ := rep.inner_labels i
  constructor
  · have hm := (rep.rows (rep.source i) (rep.source_live i)).marker_mem f false (by
      change rep.par f.val 0 = _
      rw [hf, rep.inner_par, (initialCuffGapCurve_props hG i).1, rep.source_point])
    simpa only [hlabel, Bool.toNat_false, Nat.add_zero] using hm
  · have hm := (rep.rows (rep.source (finSuccCycle i)) (rep.source_live _)).marker_mem f true (by
      change rep.par f.val 1 = _
      rw [hf, rep.inner_par, (initialCuffGapCurve_props hG i).2.1, rep.source_point])
    simpa only [hlabel, Bool.toNat_true] using hm

/-- The current outer cuff ends occur at their fixed live targets. -/
theorem outer_markers (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    2 * (rep.tagged.length + k + i.val) ∈ x.rotations.getD (rep.target i).val [] ∧
    2 * (rep.tagged.length + k + i.val) + 1 ∈
      x.rotations.getD (rep.target (finSuccCycle i)).val [] := by
  obtain ⟨f, hf, hlabel⟩ := rep.outer_labels i
  constructor
  · have hm := (rep.rows (rep.target i) (rep.target_live i)).marker_mem f false (by
      change rep.par f.val 0 = _
      rw [hf, rep.outer_par, (alg511_outer_gap_ends hG i).1, rep.target_point])
    simpa only [hlabel, Bool.toNat_false, Nat.add_zero] using hm
  · have hm := (rep.rows (rep.target (finSuccCycle i)) (rep.target_live _)).marker_mem f true (by
      change rep.par f.val 1 = _
      rw [hf, rep.outer_par, (alg511_outer_gap_ends hG i).2, rep.target_point])
    simpa only [hlabel, Bool.toNat_true] using hm

end GM06CurrentDrawingRep
end GraphMinor.GM06
