module

public import GraphMinor.Compute.Case3StepsBranchRecordBounds

/-!
# Expanding a directed parallel class into record triples

A multiplicity `q` represents copies numbered from zero to `q - 1`.
The record stores one endpoint triple for each copy. The prefix identities
below justify the scan that expands these copies without changing their
order, as required when the leaf list of a branch code is retained.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Flat record words for the first `q` copies of one directed pair. -/
def case3ParallelCopies (u v q : ℕ) : List ℕ :=
  encEdgeTriples ((List.range q).map (fun j => (u, v, j)))

/-- Each copy occupies exactly three record words. -/
theorem case3ParallelCopies_length (u v q : ℕ) :
    (case3ParallelCopies u v q).length = 3 * q := by
  rw [case3ParallelCopies, case3Length_encEdgeTriples, List.length_map, List.length_range]

private theorem encEdgeTriples_append (a b : List (ℕ × ℕ × ℕ)) :
    encEdgeTriples (a ++ b) = encEdgeTriples a ++ encEdgeTriples b := by
  induction a with
  | nil => rfl
  | cons e a ih => rcases e with ⟨u, v, j⟩; simp only [List.cons_append, encEdgeTriples, ih]

/-- Advancing the copy count appends the next triple with its copy number. -/
theorem case3ParallelCopies_succ (u v q : ℕ) :
    case3ParallelCopies u v (q + 1) = case3ParallelCopies u v q ++ [u, v, q] := by
  rw [case3ParallelCopies, List.range_succ, List.map_append, encEdgeTriples_append]
  rfl

/-- Writing three adjacent zero slots fills precisely one triple and
preserves all surrounding words. -/
theorem case3TripleBuffer_set (pre suf : List ℕ) (u v j : ℕ) :
    (((pre ++ [0, 0, 0] ++ suf).set pre.length u).set (pre.length + 1) v).set
      (pre.length + 2) j = pre ++ [u, v, j] ++ suf := by
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    simpa only [List.cons_append, List.length_cons, Nat.add_right_comm pre.length 1,
      List.set_cons_succ] using congrArg (List.cons a) ih

/-- Filling the next three slots extends the completed parallel-copy
prefix, leaving the unfilled suffix zero. -/
theorem case3ParallelCopies_buffer_set (pre suf : List ℕ) (u v q k : ℕ) (hk : k < q) :
    let buf := pre ++ case3ParallelCopies u v k ++ List.replicate (3 * (q - k)) 0 ++ suf
    ((buf.set (pre.length + 3 * k) u).set (pre.length + 3 * k + 1) v).set
      (pre.length + 3 * k + 2) k =
      pre ++ case3ParallelCopies u v (k + 1) ++ List.replicate (3 * (q - (k + 1))) 0 ++ suf := by
  dsimp only
  have hrep : List.replicate (3 * (q - k)) 0 =
      [0, 0, 0] ++ List.replicate (3 * (q - (k + 1))) 0 := by
    rw [show 3 * (q - k) = 3 + 3 * (q - (k + 1)) by omega, List.replicate_add]
    rfl
  rw [hrep, case3ParallelCopies_succ]
  have hlen : pre.length + 3 * k = (pre ++ case3ParallelCopies u v k).length := by
    rw [List.length_append, case3ParallelCopies_length]
  simp only [List.append_assoc]
  simpa only [List.append_assoc, List.length_append, case3ParallelCopies_length] using
    case3TripleBuffer_set (pre ++ case3ParallelCopies u v k)
      (List.replicate (3 * (q - (k + 1))) 0 ++ suf) u v k

end GraphMinor.Compute
