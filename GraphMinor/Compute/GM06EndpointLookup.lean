module

public import GraphMinor.Compute.GM06EndpointValency

/-!
# Reading consecutive edge endpoints

The successor input for VI (5.7), page 133, stores two vertex labels
per edge. The positions twice an edge index and its successor read
exactly the two supplied labels. These equations let component and
contraction scans use the same unrenumbered edge indices.
-/

public section
namespace GraphMinor.Compute

/-- The even endpoint-array position reads the first end. -/
theorem gm06EndpointWords_getElem_even (es : List (ℕ × ℕ)) {i : ℕ} (hi : i < es.length) :
    (gm06EndpointWords es)[2 * i]'(by rw [gm06EndpointWords_length]; omega) = es[i].1 := by
  induction es generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < es.length := by simpa using hi
      simpa only [gm06EndpointWords, List.flatMap_cons, List.cons_append, List.nil_append,
        Nat.mul_succ, List.getElem_cons_succ] using ih hi'

/-- The odd endpoint-array position reads the second end. -/
theorem gm06EndpointWords_getElem_odd (es : List (ℕ × ℕ)) {i : ℕ} (hi : i < es.length) :
    (gm06EndpointWords es)[2 * i + 1]'(by rw [gm06EndpointWords_length]; omega) = es[i].2 := by
  induction es generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < es.length := by simpa using hi
      simpa only [gm06EndpointWords, List.flatMap_cons, List.cons_append, List.nil_append,
        Nat.mul_succ, Nat.add_assoc, List.getElem_cons_succ] using ih hi'

end GraphMinor.Compute
