module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Order.Hom.Set
import GraphMinor.Surface.ArcDisc
import Mathlib.Tactic

/-!
# Placing the end of the contracted edge at a chosen parameter

For Reduction 3 of VI, page 129, the neighbour of the initial vertex
is an interior point of the linkage parameter interval. A strictly
increasing reparametrization fixing both ends can put it at the
midpoint. A piecewise linear slide gives the map, and the intermediate
value theorem gives its inverse on the interval.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

private theorem exists_unitInterval_orderIso_lower
    (a b : unitInterval) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ e : unitInterval ≃o unitInterval, e b = a := by
  have haR : (0 : ℝ) < a.1 := ha
  have habR : a.1 < b.1 := hab
  have hbR : b.1 < 1 := hb
  obtain ⟨ψ, hc, hm, h0, h1, hba, _⟩ := exists_slide_fun haR habR hbR
  let g : unitInterval → unitInterval := fun t => ⟨ψ t.1, by
    constructor
    · rw [← h0]
      exact hm.monotone t.2.1
    · rw [← h1]
      exact hm.monotone t.2.2⟩
  have hg : StrictMono g := fun _ _ h => hm h
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn
      (show y.1 ∈ Icc (ψ 0) (ψ 1) by rw [h0, h1]; exact y.2)
    exact ⟨⟨t, ht⟩, Subtype.ext he⟩
  let e := StrictMono.orderIsoOfSurjective g hg hsurj
  refine ⟨e, ?_⟩
  simpa only [e, StrictMono.coe_orderIsoOfSurjective] using
    (show g b = a from Subtype.ext hba)

/-- Two interior parameters of the unit interval can be matched by
an order isomorphism. Its associated homeomorphism fixes the two ends
and preserves every prefix interval. -/
theorem exists_unitInterval_orderIso_map_point
    (a b : unitInterval) (ha : a ∈ Ioo (0 : unitInterval) 1)
    (hb : b ∈ Ioo (0 : unitInterval) 1) :
    ∃ e : unitInterval ≃o unitInterval, e a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨e, he⟩ := exists_unitInterval_orderIso_lower a b ha.1 hab hb.2
    refine ⟨e.symm, ?_⟩
    rw [← he, e.symm_apply_apply]
  · subst b
    exact ⟨OrderIso.refl _, rfl⟩
  · exact exists_unitInterval_orderIso_lower b a hb.1 hab ha.2

end GraphMinor.GM06
