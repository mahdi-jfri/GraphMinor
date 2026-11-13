module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5SphereComplementRegions
import GraphMinor.GM11.RadialBasics
import GraphMinor.GM11.EdgeSides
import GraphMinor.Surface.OpenDisc

/-!
# Enclosing compact discarded material in a complementary region

For Reduction 2 of VI (5.5), page 130, a compact part of the
discarded drawing lying in a region of the connected retained
barrier has a disc enclosure in that region. The complementary
region is an open disc. Exhaustion by closed discs places the
whole compact set in the interior of one disc, away from the barrier.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A compact set in a complementary region of a connected barrier
in the sphere lies inside a closed disc disjoint from that barrier. -/
theorem exists_disc_enclosing_compact_in_sphere_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {Q r K : Set S} (hQc : IsClosed Q) (hQ : IsConnected Q)
    (hr : r ∈ componentsIn Qᶜ) (hK : IsCompact K) (hKr : K ⊆ r) :
    ∃ D : Set S, IsClosedDisc D ∧ D ⊆ r ∧ K ⊆ discInt D ∧ Disjoint D Q := by
  have : CompactSpace S := hS.1
  have hrD := isOpenDisc_component_complement_connected_in_sphere hS hsph hQc hQ hr
  obtain ⟨a, ha, hra⟩ := hr
  have har : a ∈ r := hra.symm ▸ mem_connectedComponentIn ha
  have hrQ : r ⊆ Qᶜ := hra.symm ▸ connectedComponentIn_subset Qᶜ a
  have hrc : IsPreconnected r := hra.symm ▸ isPreconnected_connectedComponentIn
  obtain ⟨D₀, _, hD₀, _, _, _, hD₀r, _⟩ := GraphMinor.GM11.exists_closedDisc_nbhd hS hrD.1 har
  have hbody : ∀ F : Set S, F ⊆ r → IsOArc F →
      ∃ D : Set S, D ⊆ r ∧ IsClosedDisc D ∧ discBd D = F := by
    intro F hFr hF
    exact GraphMinor.GM11.exists_disc_in_openDisc hrD hF hFr
  have hns : ¬ (IsSphere S ∧ r = univ) := by
    rintro ⟨_, hrall⟩
    obtain ⟨x, hx⟩ := hQ.nonempty
    exact hrQ (hrall ▸ mem_univ x) hx
  obtain ⟨D, hDr, hD, _, hKD⟩ := exists_disc_compact hS.2.2 hrD.1 hrc hbody hns
    hK hKr hD₀r hD₀
  exact ⟨D, hD, hDr, hKD, disjoint_left.mpr (fun _ hx hq => hrQ (hDr hx) hq)⟩

end GraphMinor.GM06
