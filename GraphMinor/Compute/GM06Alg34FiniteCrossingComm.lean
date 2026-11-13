module

public import GraphMinor.Compute.GM06Alg34Input

/-!
# Interchanging finite crossing pairs

The alternating-order test is symmetric in the two pairs. Reduce the
Boolean comparison to the two strict cyclic interval tests. The four
linear orders of the two endpoint pairs then give the same condition
on both sides. This is used when reading dual gap order from primal
crossing order.
-/

public section
namespace GraphMinor.Compute

open GM06DrawingData

private theorem bne_true (a b : Bool) :
    (a != b) = true ↔ ((a = true) ↔ ¬ b = true) := by
  cases a <;> cases b <;> decide

/-- Interchanging the two pairs preserves the finite cyclic crossing test. -/
theorem gm06CrossesFinRange_comm {n : ℕ} (a b i j : Fin n) :
    crossesOnList (List.finRange n) a b i j =
      crossesOnList (List.finRange n) i j a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [crossesOnList, List.mem_finRange, true_and, List.idxOf_finRange,
    Bool.and_eq_true, decide_eq_true_eq, bne_true, cyclicBetween]
  split_ifs <;> simp only [decide_eq_true_eq, ne_eq, Fin.ext_iff] <;> omega

end GraphMinor.Compute
