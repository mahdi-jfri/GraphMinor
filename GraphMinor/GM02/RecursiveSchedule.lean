module

public import Mathlib.Data.Int.Basic

/-!
# The alternating call schedule and the final width parameter

A2 may call A1 at the same vertex bound, while A1 calls A2 only at a
smaller bound. Weight the vertex bound by two and add one for the A2
phase to make every call decrease. For (3.2), choose a positive fixed
integer width parameter larger than the requested width and one third
of the index bound, as in the paper's final reduction on page 318.
-/

@[expose] public section
namespace GraphMinor.GM02

/-- The two routines in Graph Minors II's alternating recursion, pages 316–317. -/
inductive RecursivePhase where
  | A1
  | A2
  deriving DecidableEq, Repr

/-- A decreasing natural measure for the alternating calls. -/
def RecursivePhase.measure (phase : RecursivePhase) (n : ℕ) : ℕ :=
  2 * n + match phase with | .A1 => 0 | .A2 => 1

/-- A1 calls A2 only at a strictly smaller vertex bound. -/
theorem recursive_measure_A1 {n m : ℕ} (h : m < n) :
    RecursivePhase.A2.measure m < RecursivePhase.A1.measure n := by
  simp only [RecursivePhase.measure]
  omega

/-- A2 calls A1 at a vertex bound no greater than its own. -/
theorem recursive_measure_A2 {n m : ℕ} (h : m ≤ n) :
    RecursivePhase.A1.measure m < RecursivePhase.A2.measure n := by
  simp only [RecursivePhase.measure]
  omega

/-- A positive fixed parameter for the final reduction of II (3.2), page 318.
Natural parts handle negative integer parameters without changing the
required strict width and index inequalities. -/
def recursiveWidthParameter (w k : ℤ) : ℕ := 1 + max w.toNat (k.toNat / 3)

/-- The chosen parameter makes A2 applicable and its width report strictly
stronger than the requested width bound in II (3.2). -/
theorem recursiveWidthParameter_bounds (w k : ℤ) :
    1 ≤ recursiveWidthParameter w k ∧ w < (recursiveWidthParameter w k : ℤ) ∧
      k < (3 * recursiveWidthParameter w k : ℕ) := by
  have hwN : w.toNat < recursiveWidthParameter w k := by unfold recursiveWidthParameter; omega
  have hkN : k.toNat < 3 * recursiveWidthParameter w k := by unfold recursiveWidthParameter; omega
  have hwZ : (w.toNat : ℤ) < recursiveWidthParameter w k := by exact_mod_cast hwN
  have hkZ : (k.toNat : ℤ) < (3 * recursiveWidthParameter w k : ℕ) := by exact_mod_cast hkN
  constructor
  · unfold recursiveWidthParameter
    omega
  · constructor <;> omega

end GraphMinor.GM02
