module

public import GraphMinor.Compute.Case3StepsSelectedMembers

/-!
# Vertex tests for the selected merged members

A core vertex belongs to a member exactly when it is in its boundary. An
outside vertex belongs exactly when its component representative equals the
member's numeric label. These tests use the computed key and label arrays,
so writing all member vertex lists requires only one vertex scan per member.
-/

public section

namespace GraphMinor.Compute

/-- A selected boundary lies entirely in the core. -/
theorem case3GroupBoundary_subset_core (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) : case3GroupBoundary x Z i.1 ⊆ Z :=
  (case3GroupActive_isRawBoundary x Z i.1 i.2).subset_Z

/-- The vertices of a merged member are its outside components and boundary. -/
theorem case3SelectedMember_verts (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) :
    (case3SelectedMember x Z i).verts =
      outsideOfBoundary x Z (case3GroupBoundary x Z i.1) ∪ case3GroupBoundary x Z i.1 := rfl

/-- Every vertex in a selected boundary key is a member vertex. -/
theorem case3GroupBoundary_subset_member (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) :
    case3GroupBoundary x Z i.1 ⊆ (case3SelectedMember x Z i).verts := by
  rw [case3SelectedMember_verts]
  exact Finset.subset_union_right

/-- Core membership is tested just by the selected boundary. -/
theorem case3SelectedMember_mem_core_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (v : Fin x.n) (hv : v ∈ Z) :
    v ∈ (case3SelectedMember x Z i).verts ↔ v ∈ case3GroupBoundary x Z i.1 := by
  have h := congrArg (fun S : Finset (Fin x.n) => v ∈ S) (case3SelectedMember_inter_core x Z i)
  simpa only [Finset.mem_inter, hv, and_true] using Iff.of_eq h

/-- Outside membership is tested by equality of the computed representative
and the selected candidate's numeric label. -/
theorem case3SelectedMember_mem_outside_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (v : Fin x.n) (hv : v ∉ Z) :
    v ∈ (case3SelectedMember x Z i).verts ↔
      case3ComponentRepresentative x Z v = case3RawIndexLabel x i.1 := by
  rw [case3SelectedMember_verts, Finset.mem_union]
  have hvbd : v ∉ case3GroupBoundary x Z i.1 := fun h => hv (case3GroupBoundary_subset_core x Z i h)
  simp only [hvbd, or_false, outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_univ, true_and, hv, not_false_eq_true, true_and]
  rcases i with ⟨i, hi⟩
  cases i with
  | inl u =>
    have hu := (case3GroupActive_inl_iff x Z u).mp hi
    change attachOf x Z v = case3AttachmentRowSet x Z u ↔
      case3ComponentRepresentative x Z v = u.1
    rw [case3AttachmentRowSet_eq_attachOf x Z u hu.1]
    have h := case3ComponentRepresentative_eq_iff x Z v u hv hu.1
    rw [hu.2] at h
    exact h.symm
  | inr j =>
    have hj := (case3GroupActive_inr_iff x Z j).mp hi
    change attachOf x Z v = {((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2} ↔
      case3ComponentRepresentative x Z v = x.n + j.1
    constructor
    · intro h
      exact False.elim (hj.2 v ⟨hv, (case3AttachmentRowSet_eq_attachOf x Z v hv).trans h⟩)
    · intro h
      have hlt := case3ComponentRepresentative_lt x Z v hv
      omega

/-- The complete vertex predicate uses a core bit, a boundary membership
test, and a representative-label comparison. -/
theorem case3SelectedMember_mem_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (v : Fin x.n) :
    v ∈ (case3SelectedMember x Z i).verts ↔
      (v ∈ Z ∧ v ∈ case3GroupBoundary x Z i.1) ∨
        (v ∉ Z ∧ case3ComponentRepresentative x Z v = case3RawIndexLabel x i.1) := by
  by_cases hv : v ∈ Z
  · simp only [hv, true_and, not_true_eq_false, false_and, or_false]
    exact case3SelectedMember_mem_core_iff x Z i v hv
  · simp only [hv, false_and, not_false_eq_true, true_and, false_or]
    exact case3SelectedMember_mem_outside_iff x Z i v hv

end GraphMinor.Compute
