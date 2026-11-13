module

public import GraphMinor.GM06.Alg57CurrentCutMarks
public import GraphMinor.GM06.Alg57InputCutFits
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section5Red

/-!
# The current computed cut fits the permanent linkage and cuffs

The source and target marks are read from the current encoded walks.
The two fixed cuff lists still use their original edge base after
ordinary edge deletion. Their distinct keys and cyclic predecessor
indices pair the signed ends. These facts give `CutFits` for the
actual current tables of VI (5.7), page 133, with retired slots kept.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

private theorem cutCuffPairs_mem (base : ℕ) (cuff : List ℕ) (positive : Bool)
    (i : Fin cuff.length) :
    (cuff[i.val], if positive then 2 * (base + i.val)
      else 2 * (base + gm06PreviousCuffIndex cuff.length i.val) + 1) ∈
        gm06CutCuffPairs base cuff positive := by
  apply List.mem_map.mpr
  refine ⟨(cuff[i.val], i.val), ?_, rfl⟩
  apply List.mem_iff_getElem.mpr
  exact ⟨i.val, by simp, by simp only [List.getElem_zipIdx, Nat.zero_add]⟩

private theorem mate_even (a : ℕ) : gm06DartMate (2 * a) = 2 * a + 1 := by
  simp [gm06DartMate]

private theorem mate_odd (a : ℕ) : gm06DartMate (2 * a + 1) = 2 * a := by
  simp [gm06DartMate]

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- Both current cuff orders retain exactly one label per path. -/
theorem cuff_lengths : x.innerCuff.length = k ∧ x.outerCuff.length = k := by
  rw [rep.inner, rep.outer]
  exact ⟨List.length_ofFn, List.length_ofFn⟩

/-- The supplied source and target cuff words are all distinct. -/
theorem cut_cuff_keys_nodup (hk : 0 < k) : (x.innerCuff ++ x.outerCuff).Nodup := by
  have hs : Function.Injective (fun i : Fin k => (rep.source i).val) := by
    intro i j hij
    apply cylinderM1Point_injective hk
    exact (rep.source_point i).symm.trans
      ((congrArg rep.vertex (Fin.ext hij)).trans (rep.source_point j))
  have ht : Function.Injective (fun i : Fin k => (rep.target i).val) := by
    intro i j hij
    apply cylinderM1Point_injective hk
    have hp : cylinderM2Point k i = cylinderM2Point k j :=
      (rep.target_point i).symm.trans
        ((congrArg rep.vertex (Fin.ext hij)).trans (rep.target_point j))
    apply Subtype.ext
    have hh := congrArg (fun p : ClosedCylinder => p.val.2) hp
    simpa only [cylinderM1Point, cylinderM2Point, cylinderPoint] using
      congrArg (fun z => ((1 : ℝ), z)) hh
  rw [rep.inner, rep.outer, List.nodup_append]
  refine ⟨List.nodup_ofFn_ofInjective hs, List.nodup_ofFn_ofInjective ht, ?_⟩
  intro a ha b hb hab
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hb
  have heq : rep.source i = rep.target j := Fin.ext (hi.trans (hab.trans hj.symm))
  have hp := (rep.source_point i).symm.trans
    ((congrArg rep.vertex heq).trans (rep.target_point j))
  exact disjoint_cylinderCuffs.ne_of_mem (cylinderM1Point_mem_cylinderCuff1 k i)
    (cylinderM2Point_mem_cylinderCuff2 k j) hp

/-- Both signs of a source cuff mark are computed at their actual
source label, retaining the original ordinary edge base. -/
theorem cut_source_cuff_marks (hk : 0 < k) (i : Fin k) :
    let marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff
    marks.cuffPositive[(rep.source i).val]?.getD 0 = 2 * (rep.tagged.length + i.val) ∧
      marks.cuffNegative[(rep.source i).val]?.getD 0 =
        2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1 := by
  have hn (positive : Bool) : ((gm06CutCuffPairs rep.tagged.length x.innerCuff positive ++
      gm06CutCuffPairs (rep.tagged.length + x.innerCuff.length) x.outerCuff positive).map
        Prod.fst).Nodup := by
    rw [List.map_append, gm06CutCuffPairs_keys, gm06CutCuffPairs_keys]
    exact rep.cut_cuff_keys_nodup hk
  have hm (positive : Bool) :
      ((rep.source i).val, if positive then 2 * (rep.tagged.length + i.val)
        else 2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1) ∈
      gm06CutCuffPairs rep.tagged.length x.innerCuff positive ++
        gm06CutCuffPairs (rep.tagged.length + x.innerCuff.length) x.outerCuff positive := by
    apply List.mem_append_left
    have hi : i.val < x.innerCuff.length := by rw [rep.cuff_lengths.1]; exact i.isLt
    have hh := cutCuffPairs_mem rep.tagged.length x.innerCuff positive ⟨i.val, hi⟩
    simpa only [rep.inner, List.getElem_ofFn, List.length_ofFn] using hh
  constructor
  · have hh := gm06Scatter_getElem?_of_mem _ (List.replicate x.vertexCount 0)
      (hn true) _ (hm true) (by simp)
    exact congrArg (fun q => q.getD 0) hh
  · have hh := gm06Scatter_getElem?_of_mem _ (List.replicate x.vertexCount 0)
      (hn false) _ (hm false) (by simp)
    exact congrArg (fun q => q.getD 0) hh

/-- Both signs of a target cuff mark use the permanent outer base. -/
theorem cut_target_cuff_marks (hk : 0 < k) (i : Fin k) :
    let marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff
    marks.cuffPositive[(rep.target i).val]?.getD 0 = 2 * (rep.tagged.length + k + i.val) ∧
      marks.cuffNegative[(rep.target i).val]?.getD 0 =
        2 * (rep.tagged.length + k + gm06PreviousCuffIndex k i.val) + 1 := by
  have hn (positive : Bool) : ((gm06CutCuffPairs rep.tagged.length x.innerCuff positive ++
      gm06CutCuffPairs (rep.tagged.length + x.innerCuff.length) x.outerCuff positive).map
        Prod.fst).Nodup := by
    rw [List.map_append, gm06CutCuffPairs_keys, gm06CutCuffPairs_keys]
    exact rep.cut_cuff_keys_nodup hk
  have hm (positive : Bool) :
      ((rep.target i).val, if positive then 2 * (rep.tagged.length + k + i.val)
        else 2 * (rep.tagged.length + k + gm06PreviousCuffIndex k i.val) + 1) ∈
      gm06CutCuffPairs rep.tagged.length x.innerCuff positive ++
        gm06CutCuffPairs (rep.tagged.length + x.innerCuff.length) x.outerCuff positive := by
    apply List.mem_append_right
    have hi : i.val < x.outerCuff.length := by rw [rep.cuff_lengths.2]; exact i.isLt
    have hh := cutCuffPairs_mem (rep.tagged.length + x.innerCuff.length)
      x.outerCuff positive ⟨i.val, hi⟩
    simpa only [rep.outer, List.getElem_ofFn, List.length_ofFn, rep.cuff_lengths.1] using hh
  constructor
  · have hh := gm06Scatter_getElem?_of_mem _ (List.replicate x.vertexCount 0)
      (hn true) _ (hm true) (by simp)
    exact congrArg (fun q => q.getD 0) hh
  · have hh := gm06Scatter_getElem?_of_mem _ (List.replicate x.vertexCount 0)
      (hn false) _ (hm false) (by simp)
    exact congrArg (fun q => q.getD 0) hh

/-- Every source has the computed start position with its two
actual inner cuff markers. -/
theorem cut_source_position (hk : 0 < k) (i : Fin k) :
    ∃ b, gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) (rep.source i).val =
        some (.start b (2 * (rep.tagged.length + i.val))
          (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1)) := by
  have hout := rep.source_outgoing_pos i
  set marks := gm06BuildCutTables x.vertexCount rep.tagged.length
    x.endpoints x.linkage x.innerCuff x.outerCuff
  have hb : marks.outgoing[(rep.source i).val]?.getD 0 =
      (marks.outgoing[(rep.source i).val]?.getD 0 - 1) + 1 := by
    change marks.outgoing[(rep.source i).val]?.getD 0 ≠ 0 at hout
    omega
  exact ⟨_, (computedCutPosition_start_iff _ _ _ _ _).mpr
    ⟨rep.source_incoming_zero i, hb, rep.cut_source_cuff_marks hk i⟩⟩

/-- Every target has the computed terminal position with its two
actual outer cuff markers. -/
theorem cut_target_position (hk : 0 < k) (i : Fin k) :
    ∃ a, gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.tagged.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) (rep.target i).val =
        some (.terminal a (2 * (rep.tagged.length + k + i.val))
          (2 * (rep.tagged.length + k + gm06PreviousCuffIndex k i.val) + 1)) := by
  obtain ⟨j, hj⟩ := L.curve_one_surjective (mem_range_self i : cylinderM2Point k i ∈ cylinderM2 k)
  have hpoint : rep.vertex (rep.target i) = L.curve j 1 :=
    (rep.target_point i).trans hj.symm
  have hin := rep.terminal_incoming_pos j (rep.target i) hpoint (rep.target_live i)
  set marks := gm06BuildCutTables x.vertexCount rep.tagged.length
    x.endpoints x.linkage x.innerCuff x.outerCuff
  have ha : marks.incoming[(rep.target i).val]?.getD 0 =
      (marks.incoming[(rep.target i).val]?.getD 0 - 1) + 1 := by
    change marks.incoming[(rep.target i).val]?.getD 0 ≠ 0 at hin
    omega
  exact ⟨_, (computedCutPosition_terminal_iff _ _ _ _ _).mpr
    ⟨ha, rep.terminal_outgoing_zero j (rep.target i) hpoint (rep.target_live i), rep.cut_target_cuff_marks hk i⟩⟩

/-- All four fit conditions of the computed cut follow from the
actual input linkage and the two fixed cuff lists. -/
theorem cut_fits (hk : 0 < k) :
    CutFits (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
      x.linkage x.innerCuff x.outerCuff) x.rotations := by
  have hrows := rep.rows_length
  set marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
    x.linkage x.innerCuff x.outerCuff
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v row p a hv hp ha
    exact computed_cut_incoming_chains x.endpoints x.linkage x.innerCuff x.outerCuff
      x.rotations hrows (fun d hd => rep.cut_path_origin_lt false hd)
      (rep.cut_path_keys_nodup false) hv hp ha
  · intro v row p b hv hp hb
    exact computed_cut_outgoing_chains x.endpoints x.linkage x.innerCuff x.outerCuff
      x.rotations hrows (fun d hd => rep.cut_path_origin_lt true hd)
      (rep.cut_path_keys_nodup true) hv hp hb
  · intro v row b cp cn hv hp
    have hvn : v < x.vertexCount := hrows ▸ (List.getElem?_eq_some_iff.mp hv).1
    obtain ⟨hin, hout, hcp, hcn⟩ := (computedCutPosition_start_iff _ _ _ _ _).mp hp
    obtain ⟨i, hi⟩ := rep.source_of_marks ⟨v, hvn⟩ hin (by rw [hout]; omega)
    have hvi : (rep.source i).val = v := congrArg Fin.val hi
    obtain ⟨b', hb'⟩ := rep.cut_source_position hk (finSuccCycle i)
    have hcp' : cp = 2 * (rep.tagged.length + i.val) := by
      rw [← hvi] at hcp
      exact hcp.symm.trans (rep.cut_source_cuff_marks hk i).1
    refine ⟨(rep.source (finSuccCycle i)).val,
      x.rotations.getD (rep.source (finSuccCycle i)).val [], b',
      2 * (rep.tagged.length + (finSuccCycle i).val), ?_, ?_⟩
    · have hlen : (rep.source (finSuccCycle i)).val < x.rotations.length := by
        rw [hrows]; exact (rep.source _).isLt
      simp only [List.getElem?_eq_getElem hlen, List.getD_eq_getElem _ _ hlen]
    · simpa only [hcp', mate_even, previousCuffIndex_succ] using hb'
  · intro v row a cp cn hv hp
    have hvn : v < x.vertexCount := hrows ▸ (List.getElem?_eq_some_iff.mp hv).1
    obtain ⟨hin, hout, hcp, hcn⟩ := (computedCutPosition_terminal_iff _ _ _ _ _).mp hp
    obtain ⟨i, hi⟩ := rep.target_of_marks ⟨v, hvn⟩ (by rw [hin]; omega) hout
    have hvi : (rep.target i).val = v := congrArg Fin.val hi
    obtain ⟨a', ha'⟩ := rep.cut_target_position hk (finPredCycle i)
    have hcn' : cn = 2 * (rep.tagged.length + k + (finPredCycle i).val) + 1 := by
      rw [← hvi] at hcn
      exact hcn.symm.trans (by simpa only [previousCuffIndex_eq_pred] using
        (rep.cut_target_cuff_marks hk i).2)
    refine ⟨(rep.target (finPredCycle i)).val,
      x.rotations.getD (rep.target (finPredCycle i)).val [], a',
      2 * (rep.tagged.length + k + gm06PreviousCuffIndex k (finPredCycle i).val) + 1,
      ?_, ?_⟩
    · have hlen : (rep.target (finPredCycle i)).val < x.rotations.length := by
        rw [hrows]; exact (rep.target _).isLt
      simp only [List.getElem?_eq_getElem hlen, List.getD_eq_getElem _ _ hlen]
    · simpa only [hcn', mate_odd] using ha'

end GM06CurrentDrawingRep
end GraphMinor.GM06
