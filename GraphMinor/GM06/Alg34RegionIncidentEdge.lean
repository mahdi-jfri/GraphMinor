module

public import GraphMinor.GM06.DiscRegions
import GraphMinor.GM11.Regions

/-!
# Every region meets an edge when the drawing has an edge

Removing finitely many vertices from a disc leaves a preconnected set.
If a region met no edge in its boundary, it would be both open and
closed relative to this set, and so contain the whole set. A point on
any drawing edge contradicts that conclusion. This gives the incident
edge removed by a singleton deletion in the dual.
-/

public section
namespace GraphMinor.GM06

open Set Surface GM11
universe u
variable {S : Type u} [TopologicalSpace S]

private theorem subset_of_no_frontier {A B : Set S}
    (hA : IsPreconnected A) (hB : IsOpen B) (hAB : (A ∩ B).Nonempty)
    (hfront : Disjoint A (closure B \ B)) : A ⊆ B := by
  intro x hx
  by_contra hxB
  by_cases hxcl : x ∈ closure B
  · exact disjoint_left.mp hfront hx ⟨hxcl, hxB⟩
  · obtain ⟨w, _, hwB, hwcl⟩ := hA B (closure B)ᶜ hB isClosed_closure.isOpen_compl
      (fun y hy => by
        by_cases hyB : y ∈ B
        · exact Or.inl hyB
        · exact Or.inr fun hycl => disjoint_left.mp hfront hy ⟨hycl, hyB⟩)
      hAB ⟨x, hx, hxcl⟩
    exact hwcl (subset_closure hwB)

/-- A region of a disc drawing with at least one edge is incident with an edge. -/
theorem alg34_region_incident_edge (hS : IsClosedDiscSpace S) {G : Drawing S}
    (hE : G.E.Nonempty) {r : Set S} (hr : r ∈ G.R) :
    ∃ e ∈ G.E, G.EdgeRegionIncident e r := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨φ⟩ := hS
  have : ConnectedSpace ClosedUnitDisc :=
    Subtype.connectedSpace ((convex_closedBall (0 : EuclideanPlane) 1).isConnected
      ⟨0, by simp⟩)
  have : PreconnectedSpace S := (φ.surjective.connectedSpace φ.continuous).toPreconnectedSpace
  have hS : IsClosedDiscSpace S := ⟨φ⟩
  by_contra hnone
  have hsub : univ \ G.V ⊆ r := by
    apply subset_of_no_frontier
      (disc_isPreconnected_sdiff_finite hS isOpen_univ isPreconnected_univ G.finite_V)
      (region_isOpen hr)
    · obtain ⟨p, hp⟩ := region_nonempty hr
      exact ⟨p, ⟨trivial, fun hpV => region_subset hr hp (G.V_subset_U hpV)⟩, hp⟩
    · apply disjoint_left.mpr
      rintro p hp ⟨hpcl, hpr⟩
      have hpU : p ∈ G.U := ((closure_region_subset hr) hpcl).resolve_left hpr
      obtain ⟨e, he, hpe⟩ := G.exists_edge_of_mem hpU hp.2
      exact hnone ⟨e, he, he, hr, p, hpe, hpcl⟩
  obtain ⟨e, he⟩ := hE
  obtain ⟨p, hp⟩ := he.1
  have hps : p ∈ G.U \ G.V := he.2.1 hp
  exact region_subset hr (hsub ⟨trivial, hps.2⟩) hps.1

end GraphMinor.GM06
