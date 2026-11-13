module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5PolarCornerConnected
import GraphMinor.GM06.Section5PolarBarrierRim
import GraphMinor.GM06.Section5CompactOpenCircleArc
import GraphMinor.GM06.Section5CompactRimSeed
import GraphMinor.GM06.Section5CompactRimPieces
import GraphMinor.GM11.Regions

/-!
# Seed discs for the actual compact part of a retained corner

For Reduction 2 in VI (5.5), page 130, each retained region has
one connected proper open set of polar rim directions. Its compact
discarded part therefore fits inside one closed arc of that set.
The radial seed construction gives an attached disc inside the
region, enclosing the discarded directions at every smaller positive
radius. The sole separation vertex is avoided on the rim, so the
compactness condition follows from the actual closed discarded side.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A compact part of the rim in a retained region has an attached
seed disc, without assuming any angular interval enclosing it. -/
theorem exists_seed_for_compact_rim_part_of_retained_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    (hsT : s ∈ T.U) (hTp : IsPreconnected (T.U \ {s}))
    (hscl : s ∈ closure (T.U \ {s}))
    {r : Set S} (hr : r ∈ T.R) {K : Set Circle}
    (hK : IsCompact K) (hne : K.Nonempty) (hKr : K ⊆ (polarRimMap Φ) ⁻¹' r) :
    ∃ E : Set S, IsClosedDisc E ∧ s ∈ discBd E ∧ E ⊆ r ∪ {s} ∧
      ∀ c : I, 0 < c → c < 1 → ∀ w ∈ K,
        Φ (polarDiscPoint c w) ∈ discInt E := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hW : IsOpen ((polarRimMap Φ) ⁻¹' r) := (region_isOpen hr).preimage (polarRimMap Φ).continuous
  have hWp := isPreconnected_polar_rim_region_of_punctured_barrier hS hsph hT hp hsT hTp hscl hr
  obtain ⟨z, hzT⟩ := exists_polar_rim_point_of_subdrawing_accumulation hT hp hscl
  have hz : z ∉ (polarRimMap Φ) ⁻¹' r := fun hz => region_subset hr hz hzT
  obtain ⟨a, ha, har, hKa, h0, h1⟩ :=
    exists_arc_enclosing_compact_in_open_circle_set hW hWp hz hK hne hKr
  exact exists_seed_for_compact_rim_arc hT hp hr ha
    (fun w hw => har hw.1) hK hne hKa h0 h1

/-- The closed discarded side of a vertex separation supplies the
compact rim set used by the actual retained-region seed disc. -/
theorem exists_seed_for_discarded_rim_piece
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    (hsT : s ∈ T.U) (hTp : IsPreconnected (T.U \ {s}))
    (hscl : s ∈ closure (T.U \ {s}))
    {H : Set S} (hH : IsClosed H) (hover : H ∩ T.U ⊆ {s})
    {r : Set S} (hr : r ∈ T.R)
    (hne : ((polarRimMap Φ) ⁻¹' (H ∩ r)).Nonempty) :
    ∃ E : Set S, IsClosedDisc E ∧ s ∈ discBd E ∧ E ⊆ r ∪ {s} ∧
      ∀ c : I, 0 < c → c < 1 → ∀ w : Circle,
        polarRimMap Φ w ∈ H ∩ r → Φ (polarDiscPoint c w) ∈ discInt E := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hsnot : s ∉ range (polarRimMap Φ) := by
    rintro ⟨w, hw⟩
    exact polarDiscPoint_one_ne_centre w (hp.inj (hw.trans hp.centre.symm))
  have hK := isCompact_rim_piece_in_region hH hover (polarRimMap Φ) hsnot hr
  exact exists_seed_for_compact_rim_part_of_retained_region hS hsph hT hp hsT hTp hscl hr
    hK hne (fun w hw => hw.2)

end GraphMinor.GM06
