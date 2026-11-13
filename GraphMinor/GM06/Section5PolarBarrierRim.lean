module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5PolarAngularProjection
import GraphMinor.GM11.NiceStatements

/-!
# The retained barrier meets the polar rim

For VI (5.5), page 130, the retained barrier accumulates at the
attachment. It therefore meets the punctured interior of the polar
disc. Radial normalization moves such a point to the rim while
staying in the same full-drawing atom, which the retained subdrawing
contains. In particular the rim cannot belong entirely to one region.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A subdrawing accumulating at the polar centre has a point on
the polar rim. -/
theorem exists_polar_rim_point_of_subdrawing_accumulation
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    (hscl : s ∈ closure (T.U \ {s})) :
    ∃ w : Circle, polarRimMap Φ w ∈ T.U := by
  obtain ⟨y, hyΦ, hyT, hys⟩ := mem_closure_iff.mp hscl _ isOpen_interior hp.nhd
  obtain ⟨q, _, _, hrepr⟩ := exists_polar_angular_projection hp
  obtain ⟨c, hc, he⟩ := hrepr y ⟨interior_subset hyΦ, hys⟩
  have hn : IsGammaNice Γ T.U := isGammaNice_of_frontier hT subset_rfl
    (frontier_subset_closure.trans (by rw [T.isClosed_U.closure_eq]))
  obtain ⟨a, ha, hwa, hca⟩ := hp.ray (polarDiscPoint 1 (q y))
    (polarDiscPoint_one_ne_centre (q y)) c hc
  rw [discScale_polarDiscPoint_one, he] at hca
  exact ⟨q y, nice_atom hn ha ⟨y, hca, hyT⟩ hwa⟩

end GraphMinor.GM06
