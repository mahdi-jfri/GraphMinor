module

public import Mathlib.Data.List.Count
import Mathlib.Tactic

/-!
# Endpoint lists and valency

VI, Section 1, page 116, counts incident edges with loops counted twice.
For an edge list, store both endpoint labels consecutively. Counting
occurrences of a vertex in this list counts a non-loop incident edge
once and a loop twice. These identities explain the finite incidence
quantity returned by the RAM scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Consecutive endpoint labels for an ordinary finite edge list. -/
def gm06EndpointWords (es : List (ℕ × ℕ)) : List ℕ :=
  es.flatMap fun e => [e.1, e.2]

/-- There are exactly two directed-end positions per input edge. -/
theorem gm06EndpointWords_length (es : List (ℕ × ℕ)) :
    (gm06EndpointWords es).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [gm06EndpointWords, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at *
    omega

/-- Counting endpoint occurrences adds the first-end and second-end contributions. -/
theorem gm06EndpointWords_count (es : List (ℕ × ℕ)) (v : ℕ) :
    (gm06EndpointWords es).count v =
      (es.filter fun e => decide (e.1 = v)).length +
      (es.filter fun e => decide (e.2 = v)).length := by
  induction es with
  | nil => simp [gm06EndpointWords]
  | cons e es ih =>
    change ([e.1, e.2] ++ gm06EndpointWords es).count v = _
    rw [List.count_append, ih]
    have he₁ : (v = e.1) ↔ (e.1 = v) := eq_comm
    have he₂ : (v = e.2) ↔ (e.2 = v) := eq_comm
    by_cases h₁ : e.1 = v <;> by_cases h₂ : e.2 = v <;>
      simp [h₁, h₂, he₁, he₂] <;> omega

/-- The endpoint count is precisely the non-loop incidence count plus twice the loop count. -/
theorem gm06EndpointWords_count_loops (es : List (ℕ × ℕ)) (v : ℕ) :
    (gm06EndpointWords es).count v =
      (es.filter fun e => decide ((e.1 = v ∧ e.2 ≠ v) ∨ (e.2 = v ∧ e.1 ≠ v))).length +
      2 * (es.filter fun e => decide (e.1 = v ∧ e.2 = v)).length := by
  induction es with
  | nil => simp [gm06EndpointWords]
  | cons e es ih =>
    change ([e.1, e.2] ++ gm06EndpointWords es).count v = _
    rw [List.count_append, ih]
    have he₁ : (v = e.1) ↔ (e.1 = v) := eq_comm
    have he₂ : (v = e.2) ↔ (e.2 = v) := eq_comm
    by_cases h₁ : e.1 = v <;> by_cases h₂ : e.2 = v <;>
      simp [h₁, h₂, he₁, he₂] <;> omega

end GraphMinor.Compute
