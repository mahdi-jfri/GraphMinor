module

public import GraphMinor.Compute.GM06Alg34CyclicShift
import GraphMinor.Compute.GM06Alg34FiniteCrossingComm

/-!
# The alternating gap order after taking a dual

Advance the alternating circle by one slot, then interchange the two
crossing pairs. The new primal slots are the old gap slots, and the
new gap slots are the next old primal vertices. This determines the
finite gap metadata of the dual array without choosing points.
-/

public section
namespace GraphMinor.Compute

open GM06DrawingData

/-- Dual primal-versus-gap crossing is the old comparison with the next
primal vertices, with the two pairs interchanged. -/
theorem gm06PairCrossesGaps_dual_shift {n : ℕ} (a b i j : Fin n) :
    pairCrossesGaps (List.finRange n) a b
      (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) =
    pairCrossesGaps (List.finRange n) (gm06CycleSucc i) (gm06CycleSucc j)
      (Fin.cast List.length_finRange.symm a) (Fin.cast List.length_finRange.symm b) := by
  calc
    _ = crossesOnList (List.finRange (2 * n)) (gm06OddIndex a) (gm06OddIndex b)
        (gm06EvenIndex (gm06CycleSucc i)) (gm06EvenIndex (gm06CycleSucc j)) :=
      (gm06OddEvenSucc_crosses a b i j).symm
    _ = crossesOnList (List.finRange (2 * n)) (gm06EvenIndex (gm06CycleSucc i))
        (gm06EvenIndex (gm06CycleSucc j)) (gm06OddIndex a) (gm06OddIndex b) :=
      gm06CrossesFinRange_comm _ _ _ _
    _ = _ := gm06EvenOdd_crosses _ _ _ _

end GraphMinor.Compute
