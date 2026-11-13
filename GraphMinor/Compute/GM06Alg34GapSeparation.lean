module

public import GraphMinor.Compute.GM06Alg34GapListPositions

/-!
# Distinguishing two cuff gaps by their starting vertices

For two distinct gap positions, take the primal vertices at those same
two indices. The first gap lies strictly on the positive side of that
pair and the second does not. Their finite crossing test therefore
succeeds. This will prove that retained gap points lie in distinct
segments after vertex deletion.
-/

public section
namespace GraphMinor.Compute

open GM06DrawingData

/-- Distinct gap indices are separated by the primal pair at their starting positions. -/
theorem gm06GapSeparatedByStarts {n : ℕ} (i j : Fin n) (hne : i ≠ j) :
    pairCrossesGaps (List.finRange n) i j
      (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) = true := by
  have hvals : i.val ≠ j.val := fun he => hne (Fin.ext he)
  have hi : cyclicBetween (2 * i.val) (2 * j.val) (2 * i.val + 1) = true := by
    unfold cyclicBetween
    split_ifs <;> apply decide_eq_true <;> omega
  have hj : cyclicBetween (2 * i.val) (2 * j.val) (2 * j.val + 1) = false := by
    unfold cyclicBetween
    split_ifs <;> apply decide_eq_false <;> omega
  have hd : decide (i ≠ j) = true := decide_eq_true hne
  simp only [pairCrossesGaps, gapSide, List.mem_finRange, true_and, List.idxOf_finRange]
  simp only [hd, Bool.true_and, Fin.val_cast, hi, hj]
  rfl

/-- The same separating pair works on every cuff list without repeated labels. -/
theorem gm06GapSeparatedByListedStarts {n : ℕ} {L : List (Fin n)} (hL : L.Nodup)
    (i j : Fin L.length) (hne : i ≠ j) :
    pairCrossesGaps L (L.get i) (L.get j) i j = true := by
  rw [gm06PairCrossesGaps_get hL]
  exact gm06GapSeparatedByStarts i j hne

end GraphMinor.Compute
