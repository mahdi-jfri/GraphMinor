module

public import GraphMinor.Compute.GM06Alg34GapPositionOrder

/-!
# Shifting the origin of a finite cyclic order

Advancing every position once preserves the open cyclic interval test
and hence the crossing test. On alternating primal and gap positions,
this shift sends a primal vertex to its following gap and that gap to
the next primal vertex. These identities describe the gap labels of the
dual using only finite input positions.
-/

@[expose] public section
namespace GraphMinor.Compute

open GM06DrawingData

/-- The next cyclic position, returning to zero after the last slot. -/
def gm06CycleSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨if i.val + 1 < n then i.val + 1 else 0, by split_ifs <;> omega⟩

/-- Cyclic successor is injective, including for an empty position type. -/
theorem gm06CycleSucc_injective {n : ℕ} : Function.Injective (@gm06CycleSucc n) := by
  intro a b he
  apply Fin.ext
  have hv := congrArg Fin.val he
  change (if a.val + 1 < n then a.val + 1 else 0) =
    (if b.val + 1 < n then b.val + 1 else 0) at hv
  by_cases ha : a.val + 1 < n <;> by_cases hb : b.val + 1 < n <;>
    simp only [ha, hb, ↓reduceIte] at hv <;> omega

/-- Changing the origin by one cyclic slot preserves the interval test. -/
theorem gm06CyclicBetween_succ {n : ℕ} (a b i : Fin n) :
    cyclicBetween (gm06CycleSucc a).val (gm06CycleSucc b).val (gm06CycleSucc i).val =
      cyclicBetween a.val b.val i.val := by
  change cyclicBetween (if a.val + 1 < n then a.val + 1 else 0)
    (if b.val + 1 < n then b.val + 1 else 0)
    (if i.val + 1 < n then i.val + 1 else 0) = _
  have ha := a.isLt
  have hb := b.isLt
  have hi := i.isLt
  by_cases hA : a.val + 1 < n <;> by_cases hB : b.val + 1 < n <;>
    by_cases hI : i.val + 1 < n <;>
    simp only [hA, hB, hI, ↓reduceIte, cyclicBetween] <;>
    split_ifs <;> simp only [decide_eq_decide] <;> omega

/-- Moving all four finite positions once preserves their crossing test. -/
theorem gm06CrossesFinRange_succ {n : ℕ} (a b i j : Fin n) :
    crossesOnList (List.finRange n) (gm06CycleSucc a) (gm06CycleSucc b)
      (gm06CycleSucc i) (gm06CycleSucc j) =
        crossesOnList (List.finRange n) a b i j := by
  simp only [crossesOnList, List.mem_finRange, true_and, List.idxOf_finRange,
    ne_eq, gm06CycleSucc_injective.eq_iff, gm06CyclicBetween_succ]

/-- The next alternating position after a primal vertex is its gap. -/
theorem gm06CycleSucc_even {n : ℕ} (i : Fin n) :
    gm06CycleSucc (gm06EvenIndex i) = gm06OddIndex i := by
  apply Fin.ext
  change (if 2 * i.val + 1 < 2 * n then 2 * i.val + 1 else 0) = 2 * i.val + 1
  rw [ite_eq_left (by omega)]

/-- The next alternating position after a gap is the next primal vertex. -/
theorem gm06CycleSucc_odd {n : ℕ} (i : Fin n) :
    gm06CycleSucc (gm06OddIndex i) = gm06EvenIndex (gm06CycleSucc i) := by
  apply Fin.ext
  change (if 2 * i.val + 1 + 1 < 2 * n then 2 * i.val + 1 + 1 else 0) =
    2 * (if i.val + 1 < n then i.val + 1 else 0)
  by_cases hi : i.val + 1 < n
  · rw [ite_eq_left hi, ite_eq_left (by omega)] <;> omega
  · rw [ite_eq_right hi, ite_eq_right (by omega)]

/-- Interchanging primal and gap positions advances the new gap to the
next old primal vertex. -/
theorem gm06OddEvenSucc_crosses {n : ℕ} (a b i j : Fin n) :
    crossesOnList (List.finRange (2 * n)) (gm06OddIndex a) (gm06OddIndex b)
      (gm06EvenIndex (gm06CycleSucc i)) (gm06EvenIndex (gm06CycleSucc j)) =
        pairCrossesGaps (List.finRange n) a b
          (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) := by
  have hh := gm06CrossesFinRange_succ (gm06EvenIndex a) (gm06EvenIndex b)
    (gm06OddIndex i) (gm06OddIndex j)
  rw [gm06CycleSucc_even, gm06CycleSucc_even, gm06CycleSucc_odd, gm06CycleSucc_odd] at hh
  exact hh.trans (gm06EvenOdd_crosses a b i j)

end GraphMinor.Compute
