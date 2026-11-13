module

public import GraphMinor.GM06.Alg34InducedDivision

/-!
# Cross-freeness under induced division restriction

Each new block is an old block intersected with the surviving vertices.
A crossing of distinct new blocks would therefore give the same
crossing in distinct old blocks. Thus all deletion and component
restriction steps preserve the cross-free condition used at duality.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Restricting all division blocks preserves cross-freeness. -/
theorem inducedDivision_crossFree (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) (hCF : IsCrossFree (bd S) Δ) :
    IsCrossFree (bd S) (h.inducedDivision vs) := by
  rintro ⟨A, ⟨B, ⟨hB, _⟩, rfl⟩, C, ⟨D, ⟨hD, _⟩, rfl⟩, hne,
    s, hs, t, ht, s', hs', t', ht', hcross⟩
  have hBD : B ≠ D := fun he => hne (congrArg (fun E => E ∩ h.vertexImage vs) he)
  exact hCF ⟨B, hB, D, hD, hBD, s, hs.1, t, ht.1, s', hs'.1, t', ht'.1, hcross⟩

end GraphMinor.Compute.GM06DrawingRep
