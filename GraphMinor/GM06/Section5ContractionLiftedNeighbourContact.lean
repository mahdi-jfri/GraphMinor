module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverFibre
import GraphMinor.GM06.Section5ContractionCoverRegions
import GraphMinor.GM06.Section5ContractionCoverMap
import GraphMinor.GM06.Section5LiftedNeighbourIncidence
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM11.Walks
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# The chosen neighbour section meets the chosen lifted region

For Reduction 3 of VI (5.5), page 130, lift a region at a specified
copy of the contracted vertex. Closedness gives a contact with the
corresponding lifted old edge. Sheet-sensitive incidence transfers
that contact to its old neighbour. Injectivity within a projection
fibre identifies this neighbour with the chosen section value.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A region incident with a specified contraction value lifts to
a component incident with the chosen old neighbour in that sheet. -/
theorem section_neighbour_mem_closure_preimage_lifted_region
    {k : ℕ} {G F F' : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ bd ClosedCylinder) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hv : v ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hinj : ∀ x y, π x ≠ cylinderM1Point k i → π y ≠ cylinderM1Point k i → π x = π y → x = y)
    (hsurj : ∀ x, x ≠ cylinderM1Point k i → ∃ y, π y = x)
    (hU : F'.U = π '' F.U) (hs : cylinderM1Point k i ∈ F'.U)
    (hfibre : π ⁻¹' {cylinderM1Point k i} = closure e)
    (ρ : CylinderCover → CylinderCover) (hρ : ∀ q, Φ (ρ q) = q)
    (hρv : ∀ q, cylinderCoverProjection q = cylinderM1Point k i → cylinderCoverProjection (ρ q) = v)
    (p : CylinderCover) (hp : cylinderCoverProjection p = cylinderM1Point k i) (hfix : Φ p = p)
    {Y : Set CylinderCover} (hY : Y ∈ componentsIn (cylinderCoverProjection ⁻¹' F'.Uᶜ))
    (hpY : p ∈ closure Y) : ρ p ∈ closure (Φ ⁻¹' Y) := by
  let : LocallyPathConnectedSpace (Icc (1 : ℝ) 2) := (convex_Icc (1 : ℝ) 2).locallyPathConnectedSpace
  let : LocallyConnectedSpace CylinderCover := inferInstance
  have hYo : IsOpen Y := by
    obtain ⟨x, _, rfl⟩ := hY
    exact (F'.isClosed_U.preimage continuous_cylinderCoverProjection).isOpen_compl.connectedComponentIn
  have hYconn : IsConnected Y := by
    obtain ⟨x, hx, rfl⟩ := hY
    exact ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩
  have hYoff : Y ⊆ cylinderCoverProjection ⁻¹' F'.Uᶜ := by
    obtain ⟨x, _, rfl⟩ := hY
    exact connectedComponentIn_subset _ _
  have hYs : ∀ q ∈ Y, cylinderCoverProjection q ≠ cylinderM1Point k i := by
    intro q hq he
    exact hYoff hq (he ▸ hs)
  have heF : e ∈ F.E := hGF.2 hl.1
  have hFibSub : π ⁻¹' {cylinderM1Point k i} ⊆ F.U := by
    rw [hfibre]
    exact F.closure_subset_U heF
  have hC := preimage_lifted_component_of_contraction π Φ (cylinderM1Point k i)
    hproj htrans hinj hsurj hU hFibSub hs hY
  obtain ⟨_, _, hclosure⟩ := preimage_connected_open_set_of_cover_contraction
    π Φ (cylinderM1Point k i) hproj htrans hinj hsurj hYo hYconn hYs
  obtain ⟨γ, q, hγ, hq0, hq, hqfibre⟩ := exists_parametrized_cover_contraction_fibre
    hl hv π Φ hproj htrans hfibre p hp hfix
  obtain ⟨x, hxC, hxp⟩ := hclosure ▸ hpY
  have hxq : x ∈ range q := by
    rw [← hqfibre]
    exact hxp
  have hq1 := lifted_neighbour_mem_closure_of_closed_edge_contact hG hFU i heF
    hval hl hv γ hγ q hq hC ⟨x, hxq, hxC⟩
  have hq1p : Φ (q 1) = p := by
    have hm : q 1 ∈ Φ ⁻¹' {p} := hqfibre.symm ▸ mem_range_self 1
    exact hm
  have hsame : ρ p = q 1 := cover_map_injective_on_projection_fibre Φ htrans
    ((hρv p hp).trans ((hq 1).trans hγ.2.2.2).symm)
    ((hρ p).trans hq1p.symm)
  exact hsame.symm ▸ hq1

end GraphMinor.GM06
