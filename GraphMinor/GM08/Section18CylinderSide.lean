module

public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18CapEmbedding
import GraphMinor.GM07.CutBounds
import GraphMinor.GM07.Section5a
import GraphMinor.GM07.CapMap
import GraphMinor.Surface.CutIArc

/-!
# An embedded cylinder attached to a cuff

Cap one cuff of a cylinder and the result is a disc. A cuff-preserving
embedding extends across the cap, so the image of the cylinder is planar
in the capped target surface. This identifies the cylinder-side obstruction
in the circle case of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- An embedded cylinder whose cuff maps onto a cuff of the target is
planar after that target cuff is capped. This is the cylinder-side
obstruction in VIII (18.2), page 286. -/
theorem isPlanarInCappedCuff_of_embedded_cylinder {Y S : Type w}
    [TopologicalSpace Y] [TopologicalSpace S] [ConnectedSpace Y]
    (hY : IsSurface Y) (hS : IsSurface S)
    (hmodel : Nonempty (Y ≃ₜ SurfaceModel 0 0 2))
    {C : Set Y} {D : Set S} (hC : C ∈ cuffs Y) (hD : D ∈ cuffs S)
    {φ : Y → S} (hφ : IsEmbedding φ) (hb : BijOn φ C D) (X : Set Y) :
    GM07.IsPlanarInCappedCuff D (φ '' X) := by
  obtain ⟨Y', tY', jY, DY, hcY, _⟩ := GM07.exists_cappedCuff hY hC
  let := tY'
  obtain ⟨S', tS', j, DS, hcS, _⟩ := GM07.exists_cappedCuff hS hD
  let := tS'
  obtain ⟨_, ⟨eY⟩⟩ := GM07.cappedCuff_homeo_model hY hmodel hC hcY
  obtain ⟨edisc⟩ := nonempty_disc_homeo
  let e : Y' ≃ₜ ClosedUnitDisc := eY.trans edisc
  obtain ⟨Ψ, hΨ, hfix⟩ := exists_cap_embedding hY hcY hcS hφ hb
  have hdisc : IsClosedDisc (range Ψ) := ⟨e.symm.trans hΨ.toHomeomorph⟩
  apply GM07.isPlanarInCappedCuff_of_cap hS hcS
  refine ⟨range Ψ, hdisc, ?_⟩
  rintro z ⟨x, ⟨y, hyX, rfl⟩, rfl⟩
  exact ⟨jY y, hfix y⟩

end GraphMinor.GM08
