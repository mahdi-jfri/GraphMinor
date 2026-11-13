module

public import GraphMinor.GM02.RecursiveSchedule
public import Mathlib.Data.List.Chain

/-!
# Depth of the alternating recursive call stack

Every A1/A2 call decreases the natural measure proved for the paper's
schedule. A strictly decreasing list of natural measures has no more
entries below its root than the root value. Hence a root graph on `n`
vertices requires at most `2*n+1` saved parent frames.
-/

public section
namespace GraphMinor.GM02

private theorem descending_length_le (root : ℕ) (tail : List ℕ)
    (h : (root :: tail).IsChain (fun a b => b < a)) : tail.length ≤ root := by
  induction tail generalizing root with
  | nil => simp
  | cons x xs ih =>
    have hh := List.isChain_cons_cons.mp h
    have ht := ih x hh.2
    simp only [List.length_cons]
    omega

/-- A decreasing alternating call chain has depth bounded by its root measure. -/
theorem recursive_stack_depth_le_measure (phase : RecursivePhase) (n : ℕ)
    (calls : List (RecursivePhase × ℕ))
    (h : ((phase.measure n) :: calls.map (fun c => c.1.measure c.2)).IsChain
      (fun a b => b < a)) : calls.length ≤ phase.measure n := by
  simpa only [List.length_map] using
    descending_length_le (phase.measure n) (calls.map (fun c => c.1.measure c.2)) h

/-- The frame depth in II's alternating recursion is at most twice root size plus one. -/
theorem recursive_stack_depth_le (phase : RecursivePhase) (n : ℕ)
    (calls : List (RecursivePhase × ℕ))
    (h : ((phase.measure n) :: calls.map (fun c => c.1.measure c.2)).IsChain
      (fun a b => b < a)) : calls.length ≤ 2 * n + 1 := by
  have hd := recursive_stack_depth_le_measure phase n calls h
  cases phase <;> simp only [RecursivePhase.measure] at hd <;> omega

end GraphMinor.GM02
