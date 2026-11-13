module

public import GraphMinor.Compute.GM06Alg34DualGapRelation

/-!
# Finite cyclic order at alternating positions

Embedding an increasing sequence of positions preserves its crossing
test. In particular the odd positions have the same crossing order as
the gap indices. A comparison between two even vertex positions and two
odd gap positions is exactly the finite gap-crossing test.
-/

@[expose] public section
namespace GraphMinor.Compute

open GM06DrawingData

/-- The even position of a vertex in an alternating cuff sequence. -/
def gm06EvenIndex {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val, by omega⟩

/-- The odd position of its following gap. -/
def gm06OddIndex {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val + 1, by omega⟩

/-- Increasing finite-position embeddings preserve open cyclic intervals. -/
theorem gm06CyclicBetween_fin_map {n m : ℕ} (f : Fin n → Fin m)
    (hf : StrictMono f) (a b c : Fin n) :
    cyclicBetween (f a).val (f b).val (f c).val = cyclicBetween a.val b.val c.val := by
  have hcmp (i j : Fin n) : (f i).val < (f j).val ↔ i.val < j.val := hf.lt_iff_lt
  simp only [cyclicBetween, hcmp]

/-- Increasing finite-position embeddings preserve cyclic crossings. -/
theorem gm06CrossesFinRange_map {n m : ℕ} (f : Fin n → Fin m)
    (hf : StrictMono f) (a c b d : Fin n) :
    crossesOnList (List.finRange m) (f a) (f c) (f b) (f d) =
      crossesOnList (List.finRange n) a c b d := by
  simp only [crossesOnList, List.mem_finRange, true_and, List.idxOf_finRange,
    ne_eq, hf.injective.eq_iff, gm06CyclicBetween_fin_map f hf]

/-- The odd gap positions retain the crossing order of their gap indices. -/
theorem gm06OddIndex_crosses {n : ℕ} (a c b d : Fin n) :
    crossesOnList (List.finRange (2 * n)) (gm06OddIndex a) (gm06OddIndex c)
      (gm06OddIndex b) (gm06OddIndex d) = crossesOnList (List.finRange n) a c b d := by
  apply gm06CrossesFinRange_map
  intro i j hij
  change 2 * i.val + 1 < 2 * j.val + 1
  change i.val < j.val at hij
  omega

private theorem even_ne_odd {n : ℕ} (a b : Fin n) : gm06EvenIndex a ≠ gm06OddIndex b := by
  intro he
  have hv := congrArg Fin.val he
  change 2 * a.val = 2 * b.val + 1 at hv
  omega

/-- Comparing a primal pair with two gaps is exactly the alternating-position crossing test. -/
theorem gm06EvenOdd_crosses {n : ℕ} (a b i j : Fin n) :
    crossesOnList (List.finRange (2 * n)) (gm06EvenIndex a) (gm06EvenIndex b)
      (gm06OddIndex i) (gm06OddIndex j) = pairCrossesGaps (List.finRange n) a b
        (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) := by
  by_cases hab : a = b
  · subst b
    simp [crossesOnList, pairCrossesGaps, gapSide]
  by_cases hij : i = j
  · subst j
    simp [crossesOnList, pairCrossesGaps]
  have heven : gm06EvenIndex a ≠ gm06EvenIndex b := by
    intro he
    apply hab
    apply Fin.ext
    have hv := congrArg Fin.val he
    change 2 * a.val = 2 * b.val at hv
    omega
  have hodd : gm06OddIndex i ≠ gm06OddIndex j := by
    intro he
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val he
    change 2 * i.val + 1 = 2 * j.val + 1 at hv
    omega
  have hflag : decide (gm06EvenIndex a ≠ gm06EvenIndex b ∧
      gm06OddIndex i ≠ gm06OddIndex j ∧ gm06EvenIndex a ≠ gm06OddIndex i ∧
      gm06EvenIndex a ≠ gm06OddIndex j ∧ gm06EvenIndex b ≠ gm06OddIndex i ∧
      gm06EvenIndex b ≠ gm06OddIndex j) = true := by
    simp [heven, hodd, even_ne_odd]
  simp only [crossesOnList, List.mem_finRange, true_and, List.idxOf_finRange,
    hflag, Bool.true_and]
  simp only [pairCrossesGaps, gapSide, List.mem_finRange, true_and, hab,
    decide_true, Bool.true_and, List.idxOf_finRange]
  have hd : decide (a ≠ b) = true := decide_eq_true hab
  simp only [hd, Bool.true_and]
  rfl

end GraphMinor.Compute
