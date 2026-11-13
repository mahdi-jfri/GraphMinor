module

public import GraphMinor.Compute.GM06Alg34GapSingletonExhaust
import GraphMinor.Compute.GM06Alg34SingletonComplexity
import Mathlib.Tactic.Ring

/-!
# Original-size bounds for augmented singleton exhaustion

The augmented phase uses the same finite base-drawing recursion and
reservation as the base phase. Reuse its logarithmic word-size bound.
The additional gap work fits twice the original time estimate, yielding
a polynomial bound in the original base input size for both output arrays.
-/

public section
namespace GraphMinor.Compute

private theorem double_budget (a b : ℕ) :
    (a + 1) * (1500 * b + 10) + 1 ≤
      2 * ((a + 1) * (1300 * b + 10) + 1) := by
  ring_nf
  omega

/-- The augmented reservation-bound time is polynomial in the original base size. -/
theorem gm06GapSingletonExhaust_time_le (x : GM06DrawingData) :
    (x.n + 1) * (1500 * (10 * (x.size + 2) ^ 3 + 2) ^ 3 + 10) + 1 ≤
      4000 * (x.size + 2) ^ 22 := by
  calc
    _ ≤ 2 * ((x.n + 1) * (1300 * (10 * (x.size + 2) ^ 3 + 2) ^ 3 + 10) + 1) :=
      double_budget _ _
    _ ≤ 2 * (2000 * (x.size + 2) ^ 22) :=
      Nat.mul_le_mul_left 2 (gm06SingletonExhaust_time_le x)
    _ = _ := by omega

/-- The complete augmented singleton program has polynomial time and
logarithmic words in its original base input size and returns both exact
finite-data arrays, starting from arbitrary scratch contents. -/
theorem gm06GapSingletonExhaustProg_exec_poly (X : GM06GapInput)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length)
    {s : State} (hinput : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    ∃ s' t, Exec (wordSize 21 X.drawing.size) gm06GapSingletonExhaustProg s s' t ∧
      t ≤ 4000 * (X.drawing.size + 2) ^ 22 ∧
      s'.arrs 0 = (gm06GapReduceSingletons X).drawing.words ∧
      s'.arrs 47 = (gm06GapReduceSingletons X).discGapWords ∧ s'.regs 113 = 0 ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  have hr := gm06SingletonExhaust_reservation X.drawing
  obtain ⟨s', t, hex, ht, hin, hgap', hz, harr⟩ :=
    gm06GapSingletonExhaustProg_exec X (gm06SingletonExhaust_wordSize_le X.drawing.size)
      hr.2 hr.1 hshape hinput hgap
  exact ⟨s', t, hex, ht.trans (gm06GapSingletonExhaust_time_le X.drawing), hin, hgap', hz, harr⟩

end GraphMinor.Compute
