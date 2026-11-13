module

public import GraphMinor.Compute.GM02PatternLoopSearch

/-!
# Result of a descending pattern-loop scan

Scan pattern edge positions from last to first, replacing the answer
whenever a matching loop is found. After `j` iterations, the answer is
the first match in the last `j` positions, or the edge count if there is
none. This gives a fixed-length loop with the same result as the finite
search used by the loop-deletion proof.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- The answer after scanning the last `j` supplied pattern edge positions. -/
def gm02PatternLoopScanResult (x : GM02TopologicalInput) (flags : List ℕ) (v j : ℕ) : ℕ :=
  ((((List.finRange x.edges.length).drop (x.edges.length - j)).find?
    (gm02PatternLoopTest x flags v)).map Fin.val).getD x.edges.length

/-- Before any position is scanned, the edge-count sentinel means there is no match yet. -/
theorem gm02PatternLoopScanResult_zero (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ) :
    gm02PatternLoopScanResult x flags v 0 = x.edges.length := by
  rw [gm02PatternLoopScanResult, Nat.sub_zero, List.drop_eq_nil_of_le (by simp)]
  rfl

/-- The full descending scan gives the first matching edge, with the edge count as the failure sentinel. -/
theorem gm02PatternLoopScanResult_full (x : GM02TopologicalInput) (flags : List ℕ) (v : ℕ) :
    gm02PatternLoopScanResult x flags v x.edges.length =
      ((gm02FindPatternLoop x flags v).map Fin.val).getD x.edges.length := by
  simp [gm02PatternLoopScanResult, gm02FindPatternLoop]

/-- Every intermediate answer is either a genuine pattern edge position or the failure sentinel. -/
theorem gm02PatternLoopScanResult_le (x : GM02TopologicalInput) (flags : List ℕ) (v j : ℕ) :
    gm02PatternLoopScanResult x flags v j ≤ x.edges.length := by
  unfold gm02PatternLoopScanResult
  cases h : ((List.finRange x.edges.length).drop (x.edges.length - j)).find? (gm02PatternLoopTest x flags v) with
  | none => simp
  | some f => exact f.isLt.le

/-- The next descending position replaces the answer exactly when its explicit loop test succeeds. -/
theorem gm02PatternLoopScanResult_succ (x : GM02TopologicalInput) (flags : List ℕ) (v j : ℕ)
    (hj : j < x.edges.length) :
    gm02PatternLoopScanResult x flags v (j + 1) =
      if gm02PatternLoopTest x flags v ⟨x.edges.length - (j + 1), by omega⟩ then
        x.edges.length - (j + 1) else gm02PatternLoopScanResult x flags v j := by
  have hidx : x.edges.length - (j + 1) < (List.finRange x.edges.length).length := by simp; omega
  have ht : x.edges.length - (j + 1) + 1 = x.edges.length - j := by omega
  unfold gm02PatternLoopScanResult
  rw [List.drop_eq_getElem_cons hidx, List.getElem_finRange, ht, List.find?_cons]
  split <;> simp_all

end GraphMinor.Compute
