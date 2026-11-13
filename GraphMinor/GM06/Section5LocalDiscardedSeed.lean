module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5RetainedRegionSeed
import GraphMinor.GM06.Section5PolarLocalDrawingDirections
import GraphMinor.GM11.Regions

/-!
# A seed disc covers the discarded drawing near the attachment

For VI (5.5), page 130, every local discarded point in a retained
region normalizes to a discarded rim direction in that region.
The seed constructed from the compact rim set therefore contains
all such points in its interior. No list of local edge directions
or separate coverage assumption is needed.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The actual seed for a nonempty discarded rim piece encloses
all discarded points of that region in the open polar neighbourhood. -/
theorem exists_seed_containing_local_discarded_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {Γ T H : Drawing S} (hT : T.IsSubdrawing Γ) (hH : H.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    (hsT : s ∈ T.U) (hTp : IsPreconnected (T.U \ {s}))
    (hscl : s ∈ closure (T.U \ {s})) (hover : H.U ∩ T.U ⊆ {s})
    {r : Set S} (hr : r ∈ T.R)
    (hne : ((polarRimMap Φ) ⁻¹' (H.U ∩ r)).Nonempty) :
    ∃ D : Set S, IsClosedDisc D ∧ s ∈ discBd D ∧ D ⊆ r ∪ {s} ∧
      H.U ∩ r ∩ interior (range Φ) ⊆ discInt D := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨D, hD, hsD, hDr, hlocal⟩ := exists_seed_for_discarded_rim_piece
    hS hsph hT hp hsT hTp hscl H.isClosed_U hover hr hne
  refine ⟨D, hD, hsD, hDr, ?_⟩
  rintro y ⟨⟨hyH, hyr⟩, hyΦ⟩
  obtain ⟨c, w, hc, hc1, he, hw⟩ :=
    exists_rim_direction_of_local_subdrawing_region_point hS hT hH hp hsT hr hyΦ hyH hyr
  exact he ▸ hlocal c hc hc1 w hw

end GraphMinor.GM06
