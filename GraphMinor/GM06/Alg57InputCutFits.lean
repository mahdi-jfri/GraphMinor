module

public import GraphMinor.GM06.Alg57InputCutMarks
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5LinkageEnds

/-!
# The computed cut fits the input linkage and cuffs

In Section 9 of the implementation of VI (5.7), page 133, every
arriving path end is paired with a leaving end of the same word.
The two cuff orders pair each positive end with the negative end
at the next cuff vertex. The source and terminal mark classification
therefore supplies all four fields of `CutFits`. No geometric
rotation or face condition is assumed here.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- The complete numeric meaning of the decoded start case. -/
theorem computedCutPosition_start_iff (marks : GM06CutTables) (v b cp cn : ℕ) :
    gm06CutPositionAt marks v = some (.start b cp cn) ↔
      marks.incoming[v]?.getD 0 = 0 ∧ marks.outgoing[v]?.getD 0 = b + 1 ∧
        marks.cuffPositive[v]?.getD 0 = cp ∧ marks.cuffNegative[v]?.getD 0 = cn := by
  unfold gm06CutPositionAt
  dsimp only
  split_ifs <;> simp_all
  all_goals omega

/-- The complete numeric meaning of the decoded terminal case. -/
theorem computedCutPosition_terminal_iff (marks : GM06CutTables) (v a cp cn : ℕ) :
    gm06CutPositionAt marks v = some (.terminal a cp cn) ↔
      marks.incoming[v]?.getD 0 = a + 1 ∧ marks.outgoing[v]?.getD 0 = 0 ∧
        marks.cuffPositive[v]?.getD 0 = cp ∧ marks.cuffNegative[v]?.getD 0 = cn := by
  unfold gm06CutPositionAt
  dsimp only
  split_ifs <;> simp_all
  all_goals omega

/-- The previous gap at the next cuff vertex is the current gap. -/
theorem previousCuffIndex_succ {k : ℕ} (i : Fin k) :
    gm06PreviousCuffIndex k (finSuccCycle i).val = i.val := by
  unfold gm06PreviousCuffIndex finSuccCycle
  split_ifs <;> simp_all
  all_goals omega

/-- The numeric previous-gap index agrees with the cyclic predecessor. -/
theorem previousCuffIndex_eq_pred {k : ℕ} (i : Fin k) :
    gm06PreviousCuffIndex k i.val = (finPredCycle i).val := by
  unfold gm06PreviousCuffIndex finPredCycle
  split_ifs <;> rfl

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

namespace GM06SuccessorInputRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
include rep

/-- The supplied source and target cuff words are all distinct. -/
theorem cut_cuff_keys_nodup (hk : 0 < k) : (x.innerCuff ++ x.outerCuff).Nodup := by
  have hs : Function.Injective (fun i : Fin k => (rep.source i).val) := by
    intro i j hij
    apply cylinderM1Point_injective hk
    exact (rep.source_point i).symm.trans
      ((congrArg rep.graph.vertexLabels (Fin.ext hij)).trans (rep.source_point j))
  have ht : Function.Injective (fun i : Fin k => (rep.target i).val) := by
    intro i j hij
    apply cylinderM1Point_injective hk
    have hp : cylinderM2Point k i = cylinderM2Point k j :=
      (rep.target_point i).symm.trans
        ((congrArg rep.graph.vertexLabels (Fin.ext hij)).trans (rep.target_point j))
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
    ((congrArg rep.graph.vertexLabels heq).trans (rep.target_point j))
  exact disjoint_cylinderCuffs.ne_of_mem (cylinderM1Point_mem_cylinderCuff1 k i)
    (cylinderM2Point_mem_cylinderCuff2 k j) hp

/-- Both signs of a source cuff mark are computed at their actual
source label, retaining the original ordinary edge base. -/
theorem cut_source_cuff_marks (hk : 0 < k) (i : Fin k) :
    let marks := gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
      x.linkage x.innerCuff x.outerCuff
    marks.cuffPositive[(rep.source i).val]?.getD 0 = 2 * (rep.graph.pairs.length + i.val) ∧
      marks.cuffNegative[(rep.source i).val]?.getD 0 =
        2 * (rep.graph.pairs.length + gm06PreviousCuffIndex k i.val) + 1 := by
  have hn (positive : Bool) : ((gm06CutCuffPairs rep.graph.pairs.length x.innerCuff positive ++
      gm06CutCuffPairs (rep.graph.pairs.length + x.innerCuff.length) x.outerCuff positive).map
        Prod.fst).Nodup := by
    rw [List.map_append, gm06CutCuffPairs_keys, gm06CutCuffPairs_keys]
    exact rep.cut_cuff_keys_nodup hk
  have hm (positive : Bool) :
      ((rep.source i).val, if positive then 2 * (rep.graph.pairs.length + i.val)
        else 2 * (rep.graph.pairs.length + gm06PreviousCuffIndex k i.val) + 1) ∈
      gm06CutCuffPairs rep.graph.pairs.length x.innerCuff positive ++
        gm06CutCuffPairs (rep.graph.pairs.length + x.innerCuff.length) x.outerCuff positive := by
    apply List.mem_append_left
    have hi : i.val < x.innerCuff.length := by rw [rep.cuff_lengths.1]; exact i.isLt
    have hh := cutCuffPairs_mem rep.graph.pairs.length x.innerCuff positive ⟨i.val, hi⟩
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
    let marks := gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
      x.linkage x.innerCuff x.outerCuff
    marks.cuffPositive[(rep.target i).val]?.getD 0 = 2 * (rep.graph.pairs.length + k + i.val) ∧
      marks.cuffNegative[(rep.target i).val]?.getD 0 =
        2 * (rep.graph.pairs.length + k + gm06PreviousCuffIndex k i.val) + 1 := by
  have hn (positive : Bool) : ((gm06CutCuffPairs rep.graph.pairs.length x.innerCuff positive ++
      gm06CutCuffPairs (rep.graph.pairs.length + x.innerCuff.length) x.outerCuff positive).map
        Prod.fst).Nodup := by
    rw [List.map_append, gm06CutCuffPairs_keys, gm06CutCuffPairs_keys]
    exact rep.cut_cuff_keys_nodup hk
  have hm (positive : Bool) :
      ((rep.target i).val, if positive then 2 * (rep.graph.pairs.length + k + i.val)
        else 2 * (rep.graph.pairs.length + k + gm06PreviousCuffIndex k i.val) + 1) ∈
      gm06CutCuffPairs rep.graph.pairs.length x.innerCuff positive ++
        gm06CutCuffPairs (rep.graph.pairs.length + x.innerCuff.length) x.outerCuff positive := by
    apply List.mem_append_right
    have hi : i.val < x.outerCuff.length := by rw [rep.cuff_lengths.2]; exact i.isLt
    have hh := cutCuffPairs_mem (rep.graph.pairs.length + x.innerCuff.length)
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
    ∃ b, gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.graph.pairs.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) (rep.source i).val =
        some (.start b (2 * (rep.graph.pairs.length + i.val))
          (2 * (rep.graph.pairs.length + gm06PreviousCuffIndex k i.val) + 1)) := by
  have hout := rep.source_outgoing_pos i
  set marks := gm06BuildCutTables x.vertexCount rep.graph.pairs.length
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
    ∃ a, gm06CutPositionAt (gm06BuildCutTables x.vertexCount rep.graph.pairs.length
      x.endpoints x.linkage x.innerCuff x.outerCuff) (rep.target i).val =
        some (.terminal a (2 * (rep.graph.pairs.length + k + i.val))
          (2 * (rep.graph.pairs.length + k + gm06PreviousCuffIndex k i.val) + 1)) := by
  obtain ⟨j, hj⟩ := L.curve_one_surjective (mem_range_self i : cylinderM2Point k i ∈ cylinderM2 k)
  have hpoint : rep.graph.vertexLabels (rep.target i) = L.curve j 1 :=
    (rep.target_point i).trans hj.symm
  have hin := rep.terminal_incoming_pos j (rep.target i) hpoint
  set marks := gm06BuildCutTables x.vertexCount rep.graph.pairs.length
    x.endpoints x.linkage x.innerCuff x.outerCuff
  have ha : marks.incoming[(rep.target i).val]?.getD 0 =
      (marks.incoming[(rep.target i).val]?.getD 0 - 1) + 1 := by
    change marks.incoming[(rep.target i).val]?.getD 0 ≠ 0 at hin
    omega
  exact ⟨_, (computedCutPosition_terminal_iff _ _ _ _ _).mpr
    ⟨ha, rep.terminal_outgoing_zero j (rep.target i) hpoint, rep.cut_target_cuff_marks hk i⟩⟩

/-- All four fit conditions of the computed cut follow from the
actual input linkage and the two fixed cuff lists. -/
theorem cut_fits (hk : 0 < k) :
    CutFits (gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
      x.linkage x.innerCuff x.outerCuff) x.rotations := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrows, _⟩ := rep.rotations
  set marks := gm06BuildCutTables x.vertexCount rep.graph.pairs.length x.endpoints
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
    have hcp' : cp = 2 * (rep.graph.pairs.length + i.val) := by
      rw [← hvi] at hcp
      exact hcp.symm.trans (rep.cut_source_cuff_marks hk i).1
    refine ⟨(rep.source (finSuccCycle i)).val,
      x.rotations.getD (rep.source (finSuccCycle i)).val [], b',
      2 * (rep.graph.pairs.length + (finSuccCycle i).val), ?_, ?_⟩
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
    have hcn' : cn = 2 * (rep.graph.pairs.length + k + (finPredCycle i).val) + 1 := by
      rw [← hvi] at hcn
      exact hcn.symm.trans (by simpa only [previousCuffIndex_eq_pred] using
        (rep.cut_target_cuff_marks hk i).2)
    refine ⟨(rep.target (finPredCycle i)).val,
      x.rotations.getD (rep.target (finPredCycle i)).val [], a',
      2 * (rep.graph.pairs.length + k + gm06PreviousCuffIndex k (finPredCycle i).val) + 1,
      ?_, ?_⟩
    · have hlen : (rep.target (finPredCycle i)).val < x.rotations.length := by
        rw [hrows]; exact (rep.target _).isLt
      simp only [List.getElem?_eq_getElem hlen, List.getD_eq_getElem _ _ hlen]
    · simpa only [hcn', mate_odd] using ha'

end GM06SuccessorInputRep
end GraphMinor.GM06
