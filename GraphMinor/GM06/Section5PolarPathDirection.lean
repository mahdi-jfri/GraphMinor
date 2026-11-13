module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRay
import GraphMinor.GM06.Section5PolarAngularProjection
import GraphMinor.GM06.Section5InitialSubarcsMeet
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM11.Walks

/-!
# The unique polar direction of a path endpoint

For the barrier in VI (5.7), page 133, the linkage path contributes
one direction at its initial vertex. A nearby positive path point
normalizes to a rim direction. Radial segments stay in the path,
which is a closed union of drawing atoms. Two such directions
would be initial subarcs of the same path, so they would meet at
positive parameters and hence be equal.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A polar chart meets a path subdrawing starting at its centre in
exactly one rim direction. -/
theorem exists_unique_polar_rim_direction_of_path
    {S : Type u} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ P : Drawing S} (hP : P.IsSubdrawing Γ)
    {v t : S} (f : Curve S) (hf : ParametrizesSet f P.U v t)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ) :
    ∃! w : Circle, polarRimMap Φ w ∈ P.U := by
  have hn : IsGammaNice Γ P.U := isGammaNice_of_frontier hP subset_rfl
    (frontier_subset_closure.trans (by rw [P.isClosed_U.closure_eq]))
  let V := f ⁻¹' interior (range Φ)
  have hVo : IsOpen V := isOpen_interior.preimage f.continuous
  have h0V : (0 : I) ∈ V := by
    change f 0 ∈ interior (range Φ)
    rw [hf.2.2.1]
    exact hp.nhd
  have h0cl : (0 : I) ∈ closure (Ioo (0 : I) 1) := by
    rw [closure_Ioo (zero_ne_one : (0 : I) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨a, haV, ha⟩ := mem_closure_iff.mp h0cl V hVo h0V
  have hay : f a ≠ v := by
    intro hh
    have ha0 : a = 0 := hf.1 (hh.trans hf.2.2.1.symm)
    exact ha.1.ne' ha0
  obtain ⟨q, _, _, hrepr⟩ := exists_polar_angular_projection hp
  obtain ⟨c, hc, hcy⟩ := hrepr (f a) ⟨interior_subset haV, hay⟩
  let w := q (f a)
  have hw : polarRimMap Φ w ∈ P.U := by
    obtain ⟨b, hb, hwb, hcb⟩ := hp.ray (polarDiscPoint 1 w)
      (polarDiscPoint_one_ne_centre w) c hc
    rw [discScale_polarDiscPoint_one, hcy] at hcb
    exact nice_atom hn hb ⟨f a, hcb, hf.2.1 ▸ mem_range_self a⟩ hwb
  have hsub (z : Circle) (hz : polarRimMap Φ z ∈ P.U) :
      range (polarRayMap Φ z) ⊆ range f := by
    rintro _ ⟨r, rfl⟩
    rw [hf.2.1]
    have hh := hp.star P.isClosed_U hn hz r
    rwa [discScale_polarDiscPoint_one] at hh
  have hstart (z : Circle) : polarRayMap Φ z 0 = f 0 := by
    rw [polarRayMap_zero, hp.centre, hf.2.2.1]
  refine ⟨w, hw, ?_⟩
  intro z hz
  obtain ⟨r, s, hr, _, hrs⟩ := exists_positive_meeting_of_initial_subarcs f
    (polarRayMap Φ z) (polarRayMap Φ w) ⟨f.continuous, hf.1⟩
    (isArcMap_polarRayMap hp.inj z) (isArcMap_polarRayMap hp.inj w)
    (hsub z hz) (hsub w hw) (hstart z) (hstart w)
  exact polarDiscPoint_direction_eq hr (hp.inj hrs)

/-- A subdrawing missed by the polar centre is missed by the whole
polar chart, since each of its radial segments stays in the subdrawing. -/
theorem disjoint_polar_chart_subdrawing_of_centre_not_mem
    {S : Type u} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ)
    {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ) (hvT : v ∉ T.U) :
    Disjoint (range Φ) T.U := by
  have hn : IsGammaNice Γ T.U := isGammaNice_of_frontier hT subset_rfl
    (frontier_subset_closure.trans (by rw [T.isClosed_U.closure_eq]))
  apply disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hxT
  have hh := hp.star T.isClosed_U hn hxT 0
  rw [discScale_zero, hp.centre] at hh
  exact hvT hh

end GraphMinor.GM06
