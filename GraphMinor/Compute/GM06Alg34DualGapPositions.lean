module

public import GraphMinor.Compute.GM06Alg34DualGapPairScan

/-!
# The dual-gap test at numeric alternating positions

The cuff list gives the primal order. Doubling its indices leaves odd
positions for the intervening gaps. For distinct primal positions the
computed interval-side comparison is exactly the finite crossing test.
Equal positions contribute no crossing. This is the numeric test used
by the RAM dual-relation scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test two primal positions and their block tags against two gap positions. -/
def gm06GapPairPattern (i j a b ca cb : ℕ) : Bool :=
  decide (ca = cb ∧ ca ≠ 0) && (decide (a ≠ b) &&
    (GM06DrawingData.cyclicBetween (2 * a) (2 * b) (2 * i + 1) !=
      GM06DrawingData.cyclicBetween (2 * a) (2 * b) (2 * j + 1)))

/-- The numeric comparison of supplied primal cuff labels with two fixed gaps. -/
def gm06GapQuadTest (x : GM06DrawingData) (L : List (Fin x.n))
    (i j a b : Fin L.length) : Bool :=
  gm06GapPairPattern i.val j.val a.val b.val
    (gm06BlockTag x.division (L.get a)) (gm06BlockTag x.division (L.get b))

private theorem idxOf_get {n : ℕ} {L : List (Fin n)} (hL : L.Nodup) (i : Fin L.length) :
    L.idxOf (L.get i) = i.val := by
  have hb := List.idxOf_lt_length_iff.mpr (L.get_mem i)
  have hg := List.idxOf_get (a := L.get i) hb
  have hi : (⟨L.idxOf (L.get i), hb⟩ : Fin L.length) = i := hL.get_inj_iff.mp hg
  exact congrArg Fin.val hi

/-- The numeric alternating-position pattern is exactly the supplied
block-pair crossing test when the cuff has no repeated vertex labels. -/
theorem gm06GapPairPattern_eq (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : L.Nodup) (i j a b : Fin L.length) :
    gm06GapPairPattern i.val j.val a.val b.val
      (gm06BlockTag x.division (L.get a)) (gm06BlockTag x.division (L.get b)) =
        gm06GapPairTest x L i j a b := by
  by_cases hab : a = b
  · subst b
    simp [gm06GapPairPattern, gm06GapPairTest, GM06DrawingData.pairCrossesGaps, GM06DrawingData.gapSide]
  · have hvals : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
    have hgets : L.get a ≠ L.get b := fun hh => hab (hL.get_inj_iff.mp hh)
    have hda : decide (a.val ≠ b.val) = true := decide_eq_true hvals
    have hdg : decide (L.get a ≠ L.get b) = true := decide_eq_true hgets
    simp only [gm06GapPairPattern, gm06GapPairTest, GM06DrawingData.pairCrossesGaps,
      GM06DrawingData.gapSide, List.get_mem, true_and, hda, hdg,
      Bool.true_and, idxOf_get hL]

end GraphMinor.Compute
