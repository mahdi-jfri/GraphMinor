module

public import GraphMinor.GM06.Alg34GapBoundary

/-!
# Crossing tests are constant on boundary segments

A segment stays in one component after removing any two primal boundary
vertices. Moving a gap point within its segment therefore preserves
all crossing tests against primal pairs. This allows the finite gap
order to be interpreted using the actual dual boundary vertices.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

private theorem gap_preconnected {seg : Set S}
    (hs : seg ∈ segmentsOf (bd S) (G.V ∩ bd S)) : IsPreconnected seg := by
  obtain ⟨⟨p, _, rfl⟩, _⟩ := hs
  exact isPreconnected_connectedComponentIn

/-- Points in one boundary segment stay together after two primal boundary vertices are removed. -/
theorem gap_component_eq {seg : Set S}
    (hs : seg ∈ segmentsOf (bd S) (G.V ∩ bd S))
    {a b u v : S} (ha : a ∈ G.V ∩ bd S) (hb : b ∈ G.V ∩ bd S)
    (hu : u ∈ seg) (hv : v ∈ seg) :
    connectedComponentIn (bd S \ {a, b}) u = connectedComponentIn (bd S \ {a, b}) v := by
  have hsub : seg ⊆ bd S \ {a, b} := by
    intro p hp
    have hpd := gap_subset_boundary_diff hs hp
    refine ⟨hpd.1, ?_⟩
    rintro (rfl | rfl)
    · exact hpd.2 ha
    · exact hpd.2 hb
  have hvcc := (gap_preconnected hs).subset_connectedComponentIn hu hsub hv
  exact connectedComponentIn_eq hvcc

private theorem gap_crosses_transfer {seg₁ seg₂ : Set S}
    (hs₁ : seg₁ ∈ segmentsOf (bd S) (G.V ∩ bd S))
    (hs₂ : seg₂ ∈ segmentsOf (bd S) (G.V ∩ bd S))
    {a b u v u' v' : S} (ha : a ∈ G.V ∩ bd S) (hb : b ∈ G.V ∩ bd S)
    (hu : u ∈ seg₁) (hv : v ∈ seg₂) (hu' : u' ∈ seg₁) (hv' : v' ∈ seg₂)
    (hc : CrossesOn (bd S) a b u v) : CrossesOn (bd S) a b u' v' := by
  have hcu := gap_component_eq hs₁ ha hb hu hu'
  have hcv := gap_component_eq hs₂ ha hb hv hv'
  have hcc : connectedComponentIn (bd S \ {a, b}) u' ≠
      connectedComponentIn (bd S \ {a, b}) v' := by
    rw [← hcu, ← hcv]
    exact hc.2.2.2.2.2.2.2.2.2.2
  have huD := gap_subset_boundary_diff hs₁ hu'
  have hvD := gap_subset_boundary_diff hs₂ hv'
  have hau : a ≠ u' := fun he => huD.2 (he ▸ ha)
  have hav : a ≠ v' := fun he => hvD.2 (he ▸ ha)
  have hbu : b ≠ u' := fun he => huD.2 (he ▸ hb)
  have hbv : b ≠ v' := fun he => hvD.2 (he ▸ hb)
  have huv : u' ≠ v' := fun he => hcc (congrArg _ he)
  exact ⟨ha.2, huD.1, hb.2, hvD.1, hc.2.2.2.2.1, huv, hau, hav, hbu, hbv, hcc⟩

/-- Replacing either gap point by another point on the same segment
preserves crossing against every pair of primal boundary vertices. -/
theorem gap_crosses_iff {seg₁ seg₂ : Set S}
    (hs₁ : seg₁ ∈ segmentsOf (bd S) (G.V ∩ bd S))
    (hs₂ : seg₂ ∈ segmentsOf (bd S) (G.V ∩ bd S))
    {a b u v u' v' : S} (ha : a ∈ G.V ∩ bd S) (hb : b ∈ G.V ∩ bd S)
    (hu : u ∈ seg₁) (hv : v ∈ seg₂) (hu' : u' ∈ seg₁) (hv' : v' ∈ seg₂) :
    CrossesOn (bd S) a b u v ↔ CrossesOn (bd S) a b u' v' :=
  ⟨gap_crosses_transfer hs₁ hs₂ ha hb hu hv hu' hv',
    gap_crosses_transfer hs₁ hs₂ ha hb hu' hv' hu hv⟩

end GraphMinor.Compute.GM06DrawingRep
