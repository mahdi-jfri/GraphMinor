module

public import GraphMinor.Compute.GM02RecursiveChildIndex
public import GraphMinor.Compute.GM02RecursiveChildMeasure
public import GraphMinor.Compute.GM02RecursiveTime

/-!
# Common bounds for the two encoded recursive phases

The machine encodes A1 by zero and A2 by one. Express the paper's child
size and index bounds using this phase bit, so the same loop induction
handles both routines. Its supplied vertex bound decreases in A1 and
its phase bit decreases in A2, exactly as in the numerical time budget.
-/

public section
namespace GraphMinor.Compute

/-- Both phase-bit cases give the size and index promises required by the opposite routine. -/
theorem gm02RecursivePhase_child_bounds (phase right : Bool) (q n : ℕ)
    (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
    (C : (gm02CompressedBoundaryInput x L R).schemes)
    (hx : x.n ≤ n) (hlarge : 4 * q < x.n)
    (hindex : if phase then x.A.index ≤ 3 * q else 2 * x.A.index ≤ 5 * q)
    (hvalid : (gm02RecursiveSeparatorInput (!phase) x).validSides (q : ℤ)
      (gm02VertexBits L) (gm02VertexBits R)) :
    (gm02RecursiveChosenInput right x L R C).n ≤ (if phase then n else 3 * n / 4) ∧
      (if !phase then (gm02RecursiveChosenInput right x L R C).A.index ≤ 3 * q
        else 2 * (gm02RecursiveChosenInput right x L R C).A.index ≤ 5 * q) := by
  cases phase with
  | false =>
    exact ⟨gm02RecursiveChosenInput_A1_bound right x q n L R C hx hlarge hvalid,
      gm02RecursiveChosenInput_A1_index right x q L R C hindex hvalid⟩
  | true =>
    exact ⟨(gm02RecursiveChosenInput_size_le right false x q L R C hvalid).trans hx,
      gm02RecursiveChosenInput_A2_index right x q L R C hindex hvalid⟩

/-- The supplied call bound and phase bit strictly decrease on every non-base call. -/
theorem gm02RecursivePhase_measure_lt (phase : Bool) (n : ℕ) (hn : 0 < n) :
    2 * (if phase then n else 3 * n / 4) + (if !phase then 1 else 0) <
      2 * n + (if phase then 1 else 0) := by
  cases phase <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The numerical budget has exactly the child bound selected by the machine phase. -/
theorem gm02RecursiveTime_phase (phase : Bool) (q C d n : ℕ) (hn : 4 * q < n) :
    gm02RecursiveTime q C d (2 * n + if phase then 1 else 0) =
      C * (n + 1) ^ d + 2 * gm02RecursiveCodeBound q *
        gm02RecursiveTime q C d
          (2 * (if phase then n else 3 * n / 4) + if !phase then 1 else 0) := by
  cases phase with
  | false => simpa only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using gm02RecursiveTime_A1 q C d n hn
  | true => simpa only [Bool.not_true, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] using gm02RecursiveTime_A2 q C d n hn

end GraphMinor.Compute
