module

public import GraphMinor.Compute.GM06Alg34GapListPositions

/-!
# Gap comparisons through an injective position labelling

Writing an injective label function as a list does not change the gap
comparison at the original positions. The casts only account for the
length of the generated list. This allows the computed dual cuff to
use its supplied region labels directly.
-/

public section
namespace GraphMinor.Compute

open GM06DrawingData

/-- The gap comparison of an injectively generated list is the comparison
of its original positions. -/
theorem gm06PairCrossesGaps_ofFn {n k : ℕ} (f : Fin k → Fin n)
    (hf : Function.Injective f) (a b i j : Fin k) :
    pairCrossesGaps (List.ofFn f) (f a) (f b)
      (Fin.cast (List.length_ofFn (f := f)).symm i) (Fin.cast (List.length_ofFn (f := f)).symm j) =
    pairCrossesGaps (List.finRange k) a b
      (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) := by
  have hmem (u : Fin k) : f u ∈ List.ofFn f := List.mem_ofFn.mpr ⟨u, rfl⟩
  have hidx (u : Fin k) : (List.ofFn f).idxOf (f u) = u.val := by
    rw [List.ofFn_eq_map, gm06_idxOf_map f hf, List.idxOf_finRange]
  simp only [pairCrossesGaps, gapSide, hmem, List.mem_finRange, true_and,
    ne_eq, hf.eq_iff, hidx, List.idxOf_finRange, Fin.val_cast]

end GraphMinor.Compute
