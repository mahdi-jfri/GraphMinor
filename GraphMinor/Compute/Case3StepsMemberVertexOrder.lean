module

public import GraphMinor.Compute.Case3StepsBoundaryKeys
import Mathlib.Data.List.GetD

/-!
# The vertex list agrees with compact member numbering

Filtering the ambient increasing vertex list gives the increasing list of
the member's vertex set. It is therefore the same enumeration used by the
order embedding that numbers the compact member. Reading a vertex-list word
maps a compact label back to its ambient label, including in the padded RAM
buffer.
-/

public section

namespace GraphMinor.Compute

/-- The filtered vertex scan gives the canonical increasing finset enumeration. -/
theorem case3BoundaryVertices_eq_sort {n : ℕ} (S : Finset (Fin n)) :
    case3BoundaryVertices S = S.sort (· ≤ ·) := by
  classical
  have hs : (case3BoundaryVertices S).SortedLT :=
    ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
  apply hs.eq_of_mem_iff S.sortedLT_sort
  intro u
  simp [case3BoundaryVertices]

/-- A compact vertex's ordered list entry is its ambient order-embedding label. -/
theorem case3BoundaryVertices_getD_orderEmb {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) :
    ((case3BoundaryVertices S).map Fin.val).getD i.1 0 = (S.orderEmbOfFin rfl i).1 := by
  rw [List.getD_eq_getElem _ 0 (by rw [List.length_map, case3BoundaryVertices_length]; exact i.2)]
  simp only [List.getElem_map, case3BoundaryVertices_eq_sort]
  exact congrArg Fin.val (Finset.orderEmbOfFin_apply S rfl i).symm

/-- Padding after the vertex count leaves every valid inverse-label lookup unchanged. -/
theorem case3PaddedVertices_getD_orderEmb {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) :
    ((case3BoundaryVertices S).map Fin.val ++ List.replicate (n - S.card) 0).getD i.1 0 =
      (S.orderEmbOfFin rfl i).1 := by
  rw [List.getD_append _ _ _ _ (by rw [List.length_map, case3BoundaryVertices_length]; exact i.2)]
  exact case3BoundaryVertices_getD_orderEmb S i

end GraphMinor.Compute
