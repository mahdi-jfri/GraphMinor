module

public import GraphMinor.Compute.Case3StepsBoundaryKeys

/-!
# Boundary keys of core edges

A canonical simple edge has its smaller endpoint first. Its raw member has
those two boundary vertices (XIII (8.6), type (i), page 96). The boundary key
is therefore the size word two followed by its two endpoints and one zero.
-/

public section

namespace GraphMinor.Compute

open Classical

/-- The increasing boundary list of two ordered vertices is their pair. -/
theorem case3BoundaryVertices_pair {n : ℕ} (u v : Fin n) (huv : u < v) :
    case3BoundaryVertices ({u, v} : Finset (Fin n)) = [u, v] := by
  have hne : u ≠ v := ne_of_lt huv
  have hlen : (case3BoundaryVertices ({u, v} : Finset (Fin n))).length = 2 := by
    rw [case3BoundaryVertices_length, Finset.card_pair hne]
  obtain ⟨a, b, heq⟩ := List.length_eq_two.mp hlen
  have huL : u ∈ case3BoundaryVertices ({u, v} : Finset (Fin n)) := by
    simp [case3BoundaryVertices]
  have hvL : v ∈ case3BoundaryVertices ({u, v} : Finset (Fin n)) := by
    simp [case3BoundaryVertices]
  have hp : List.Pairwise (· < ·) (case3BoundaryVertices ({u, v} : Finset (Fin n))) :=
    (List.pairwise_lt_finRange n).filter _
  have hab : a < b := by simpa [heq] using hp
  rw [heq] at huL hvL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at huL hvL
  rcases huL with rfl | rfl <;> rcases hvL with rfl | rfl
  · exact False.elim (hne rfl)
  · exact heq
  · exact False.elim (not_lt_of_ge huv.le hab)
  · exact False.elim (hne rfl)

/-- The key of a canonical core edge has a fixed explicit four-word form. -/
theorem case3BoundaryKey_pair {n : ℕ} (u v : Fin n) (huv : u < v) :
    case3BoundaryKey ({u, v} : Finset (Fin n)) = [2, u.1, v.1, 0] := by
  rw [case3BoundaryKey, Finset.card_pair (ne_of_lt huv), case3BoundaryVertices_pair u v huv]
  rfl

end GraphMinor.Compute
