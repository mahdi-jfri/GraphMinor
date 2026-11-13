module

public import GraphMinor.GM06.Alg34InducedDivision

/-!
# Division conditions under finite induced restriction

Restrict each old block to the surviving vertices and discard empty
blocks. The result is still a division, and its union is exactly the
old union restricted to those vertices. Thus a division covering all
boundary vertices still covers the boundary vertices of the induced
drawing. These facts keep the algorithm's input conditions after a
reduction or component materialization.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Restricting division blocks and discarding empty restrictions gives a division. -/
theorem inducedDivision_isDivision (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (hD : IsDivision Δ) : IsDivision (h.inducedDivision vs) := by
  refine ⟨(hD.1.subset (fun _ hh => hh.1)).image _, ?_, ?_⟩
  · rintro B ⟨A, ⟨_, hA⟩, rfl⟩
    exact hA
  · rintro B ⟨A, ⟨hA, _⟩, rfl⟩ C ⟨D, ⟨hD', _⟩, rfl⟩ hne
    have hAD : A ≠ D := fun he => hne (congrArg (fun E => E ∩ h.vertexImage vs) he)
    exact (hD.2.2 hA hD' hAD).mono inter_subset_left inter_subset_left

/-- The union of restricted nonempty blocks is exactly the restricted old union. -/
theorem inducedDivision_union (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    divisionUnion (h.inducedDivision vs) = divisionUnion Δ ∩ h.vertexImage vs := by
  ext p
  constructor
  · rintro ⟨B, ⟨A, ⟨hA, _⟩, rfl⟩, hpA, hpV⟩
    exact ⟨⟨A, hA, hpA⟩, hpV⟩
  · rintro ⟨⟨A, hA, hpA⟩, hpV⟩
    exact ⟨A ∩ h.vertexImage vs, ⟨A, ⟨hA, ⟨p, hpA, hpV⟩⟩, rfl⟩, hpA, hpV⟩

/-- Covering all boundary vertices is preserved by every induced restriction. -/
theorem inducedDivision_boundary (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (hbd : divisionUnion Δ = G.V ∩ bd S) :
    divisionUnion (h.inducedDivision vs) = (induceDrawing G (h.vertexImage vs)).V ∩ bd S := by
  rw [h.inducedDivision_union vs, hbd, induceDrawing_V G (h.vertexImage_subset vs)]
  ext p
  constructor
  · exact fun hp => ⟨hp.2, hp.1.2⟩
  · exact fun hp => ⟨⟨h.vertexImage_subset vs hp.1, hp.2⟩, hp.1⟩

end GraphMinor.Compute.GM06DrawingRep
