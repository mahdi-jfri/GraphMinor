module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5LiftedInitialRegionContact
import GraphMinor.GM06.Section5LiftedCylinderEdgeIncidence
import GraphMinor.GM06.Section5ContractionCoverFibre

/-!
# Neighbour incidence in a prescribed angular sheet

For the cover form of Reduction 3 in VI (5.5), page 130, any region
closure meeting the lifted closed contracted edge reaches its lifted
neighbour. An initial contact gives an interior contact by the small
neighbourhood argument. Interior incidence propagates along the lift,
and continuity then includes the neighbour at its other end.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A lifted complementary component meeting the specified closed
initial edge also reaches its neighbour in the same angular sheet. -/
theorem lifted_neighbour_mem_closure_of_closed_edge_contact
    {k : ℕ} {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (heF : e ∈ F.E)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hv : v ≠ cylinderM1Point k i)
    (γ : Curve ClosedCylinder) (hγ : ParametrizesSet γ (closure e) (cylinderM1Point k i) v)
    (q : C(unitInterval, CylinderCover)) (hq : ∀ t, cylinderCoverProjection (q t) = γ t)
    {r : Set CylinderCover} (hr : r ∈ componentsIn (cylinderCoverProjection ⁻¹' F.Uᶜ))
    (hcontact : (range q ∩ closure r).Nonempty) : q 1 ∈ closure r := by
  obtain ⟨x, ⟨t, ht⟩, hx⟩ := hcontact
  have htcl : q t ∈ closure r := ht ▸ hx
  by_cases ht1 : t = 1
  · exact ht1 ▸ htcl
  have hinc : (q '' Ioo 0 1 ∩ closure r).Nonempty := by
    by_cases ht0 : t = 0
    · exact lifted_initial_region_meets_edge_interior hG hFU i hval hl hv γ hγ q hq hr (ht0 ▸ htcl)
    · exact ⟨q t, ⟨t, ⟨lt_of_le_of_ne bot_le (show t ≠ 0 from ht0).symm,
        lt_of_le_of_ne le_top (show t ≠ 1 from ht1)⟩, rfl⟩, htcl⟩
  have hAe : q '' Ioo 0 1 ⊆ cylinderCoverProjection ⁻¹' e := by
    rintro _ ⟨u, hu, rfl⟩
    change cylinderCoverProjection (q u) ∈ e
    rw [hq]
    exact image_Ioo_of_parametrizesSet_closure_edge hl γ hγ ▸ mem_image_of_mem γ hu
  have hsub := lifted_cylinder_edge_subset_closure_component hG hl.1 heF
    (isPreconnected_Ioo.image q q.continuous.continuousOn) hAe hr hinc
  have hqcl : q 1 ∈ closure (q '' Ioo 0 1) := by
    apply mem_closure_image q.continuous.continuousAt
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
    exact ⟨zero_le_one, le_rfl⟩
  exact closure_minimal hsub isClosed_closure hqcl

end GraphMinor.GM06
