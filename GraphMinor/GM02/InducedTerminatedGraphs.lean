module

public import GraphMinor.GM02.CrossingScheme
public import Mathlib.Combinatorics.Graph.Delete
import GraphMinor.GM02.CrossingSchemeSupports

/-!
# Induced terminated graphs with original terminals protected

II, page 315, deletes only the reserved set from each side of a crossing
scheme. The star counterexample to (2.9) shows that this permits a side's
path to pass internally through an original terminal assigned to the other
side. Delete those original separator terminals as well. This leaves every
new endpoint present. The two corrected induced graphs then meet exactly
at the endpoints shared by their new terminations.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Correction to II's induced graph on the first side, page 315: also
delete original separator terminals absent from the first termination.
The printed deletion alone fails in `FeasibilityCounterexample.counterexample_2_9`. -/
def CrossingScheme.inducedLeft {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) : Graph α β :=
  H.deleteVerts (C.reservedLeft ∪ ((A₀.support ∩ (V(H) ∩ V(H'))) \ C.left.support))

/-- The corresponding correction to the second induced graph of II, page 315. -/
def CrossingScheme.inducedRight {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) : Graph α β :=
  H'.deleteVerts (C.reservedRight ∪ ((A₀.support ∩ (V(H) ∩ V(H'))) \ C.right.support))

/-- Every first-side endpoint survives the corrected deletion. -/
theorem CrossingScheme.left_support_subset_induced {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    C.left.support ⊆ V(C.inducedLeft) := by
  intro a ha
  have haH : a ∈ V(H) := by
    by_cases haX : a ∈ V(H) ∩ V(H')
    · exact haX.1
    · have h : a ∈ C.left.support \ (V(H) ∩ V(H')) := ⟨ha, haX⟩
      rw [C.left_support] at h
      exact h.2.1
  simp only [CrossingScheme.inducedLeft, Graph.vertexSet_deleteVerts]
  refine ⟨haH, ?_⟩
  rintro (hz | ht)
  · have hu : a ∈ C.reservedLeft ∪ C.reservedRight := Or.inl hz
    rw [C.reserved_union] at hu
    exact hu.2 (Or.inl (Or.inr ha))
  · exact ht.2 ha

/-- Every second-side endpoint survives the corrected deletion. -/
theorem CrossingScheme.right_support_subset_induced {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    C.right.support ⊆ V(C.inducedRight) := by
  intro a ha
  have haH : a ∈ V(H') := by
    by_cases haX : a ∈ V(H) ∩ V(H')
    · exact haX.2
    · have h : a ∈ C.right.support \ (V(H) ∩ V(H')) := ⟨ha, haX⟩
      rw [C.right_support] at h
      exact h.2.1
  simp only [CrossingScheme.inducedRight, Graph.vertexSet_deleteVerts]
  refine ⟨haH, ?_⟩
  rintro (hz | ht)
  · have hu : a ∈ C.reservedLeft ∪ C.reservedRight := Or.inr hz
    rw [C.reserved_union] at hu
    exact hu.2 (Or.inr ha)
  · exact ht.2 ha

/-- The corrected induced graphs meet exactly at their common new
endpoints. In particular, a terminal used on just one side cannot be
an internal vertex of a path on the other side. -/
theorem CrossingScheme.induced_vertex_inter {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    V(C.inducedLeft) ∩ V(C.inducedRight) = C.left.support ∩ C.right.support := by
  ext a
  constructor
  · rintro ⟨haL, haR⟩
    simp only [CrossingScheme.inducedLeft, Graph.vertexSet_deleteVerts] at haL
    simp only [CrossingScheme.inducedRight, Graph.vertexSet_deleteVerts] at haR
    have haX : a ∈ V(H) ∩ V(H') := ⟨haL.1, haR.1⟩
    by_cases ha₀ : a ∈ A₀.support
    · have hleft : a ∈ C.left.support := by
        by_contra hn
        exact haL.2 (Or.inr ⟨⟨ha₀, haX⟩, hn⟩)
      have hright : a ∈ C.right.support := by
        by_contra hn
        exact haR.2 (Or.inr ⟨⟨ha₀, haX⟩, hn⟩)
      exact ⟨hleft, hright⟩
    · have haU : a ∈ C.left.support ∪ C.right.support := by
        by_contra hn
        have haZ : a ∈ C.reservedLeft ∪ C.reservedRight := by
          rw [C.reserved_union]
          exact ⟨haX, fun h => h.elim (fun h => h.elim ha₀ (fun h => hn (Or.inl h)))
            (fun h => hn (Or.inr h))⟩
        exact haZ.elim (fun h => haL.2 (Or.inl h)) (fun h => haR.2 (Or.inl h))
      exact (C.inter_support_iff haX).2 ⟨haU, ha₀⟩
  · intro ha
    exact ⟨C.left_support_subset_induced ha.1, C.right_support_subset_induced ha.2⟩

end GraphMinor.GM02
