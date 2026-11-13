module

public import GraphMinor.Compute.GM06Alg34DualGapRelation
public import GraphMinor.Compute.GM06Alg34TagPartition

/-!
# Testing dual gap relations using supplied block tags

Equal positive tags identify exactly the pairs in a division block.
Scan the two primal cuff positions and test each such pair against the
two fixed gaps. The absence of a successful pair is exactly the finite
dual relation. This replaces repeated block-list scans by direct reads
of the already computed tag table.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set GM06 GM06DrawingData

/-- One pair of primal cuff positions witnesses a gap separation when
its labels have a common positive block tag and cross the gap pair. -/
def gm06GapPairTest (x : GM06DrawingData) (L : List (Fin x.n))
    (i j a b : Fin L.length) : Bool :=
  decide (gm06BlockTag x.division (L.get a) = gm06BlockTag x.division (L.get b) ∧
    gm06BlockTag x.division (L.get a) ≠ 0) &&
      pairCrossesGaps L (L.get a) (L.get b) i j

/-- Test every pair of supplied primal cuff positions against two fixed gaps. -/
def gm06GapPairScan (x : GM06DrawingData) (L : List (Fin x.n))
    (i j : Fin L.length) : Bool :=
  (List.finRange L.length).any fun a => (List.finRange L.length).any fun b => gm06GapPairTest x L i j a b

private theorem crossing_gap_pair_mem {n : ℕ} (L : List (Fin n)) (a b : Fin n)
    (i j : Fin L.length) (hc : pairCrossesGaps L a b i j = true) :
    a ∈ L ∧ b ∈ L ∧ a ≠ b := by
  by_contra hn
  simp [pairCrossesGaps, gapSide, hn] at hc

/-- The tag-based pair scan finds exactly a block pair crossing the two gaps. -/
theorem gm06GapPairScan_iff (x : GM06DrawingData) (L : List (Fin x.n))
    (hD : IsDivision x.divisionSet) (i j : Fin L.length) :
    gm06GapPairScan x L i j = true ↔
      ∃ B ∈ x.division, ∃ a ∈ B, ∃ b ∈ B, pairCrossesGaps L a b i j = true := by
  simp only [gm06GapPairScan, List.any_eq_true, List.mem_finRange, true_and,
    gm06GapPairTest, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, ⟨heq, hpos⟩, hc⟩
    obtain ⟨B, hB, ha, hb⟩ := gm06BlockTag_common_block x.division (L.get a) (L.get b) heq hpos
    exact ⟨B, hB, L.get a, ha, L.get b, hb, hc⟩
  · rintro ⟨B, hB, a, ha, b, hb, hc⟩
    obtain ⟨haL, hbL, _⟩ := crossing_gap_pair_mem L a b i j hc
    obtain ⟨ia, hia⟩ := List.mem_iff_get.mp haL
    obtain ⟨ib, hib⟩ := List.mem_iff_get.mp hbL
    have ht := (gm06BlockTag_eq_pos_iff (show IsDivision (gm06BlockSets x.division) from hD) a b).mpr
      ⟨B, hB, ha, hb⟩
    refine ⟨ia, ib, ?_, ?_⟩
    · simpa only [hia, hib] using ht
    · simpa only [hia, hib] using hc

/-- For a supplied division, the dual relation is exactly the complement
of the tag-based pair scan, so the RAM can use the existing tag table. -/
theorem gm06GapPairScan_eq_not_related (x : GM06DrawingData) (L : List (Fin x.n))
    (hD : IsDivision x.divisionSet) (i j : Fin L.length) :
    gm06GapPairScan x L i j = !x.dualGapRelated L i j := by
  apply Bool.eq_iff_iff.mpr
  rw [gm06GapPairScan_iff x L hD i j]
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  change _ ↔ ¬ (x.dualGapRelated L i j = true)
  rw [x.dualGapRelated_iff_no_crossing]
  exact not_not.symm

end GraphMinor.Compute
