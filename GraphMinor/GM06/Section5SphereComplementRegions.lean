module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM11.Regions
import GraphMinor.Surface.Disc
import GraphMinor.GM11.SphereRegion
import GraphMinor.GM11.PerimeterPull
import GraphMinor.Surface.OpenDisc

/-!
# Complementary components of a connected set in a sphere

In the enclosure argument for VI (5.5), page 130, the retained
linkage and cuffs form a connected barrier. After embedding in the
sphere, each complementary component is an open disc. Indeed, an
O-arc in that component bounds a disc missing the connected barrier.
That disc remains in the same component. The open-disc criterion
then applies.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Each complementary component of a nonempty closed connected
set in a sphere is an open disc. This supplies the ambient discs
for enclosing discarded components of Reduction 2. -/
theorem isOpenDisc_component_complement_connected_in_sphere
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {Q r : Set S} (hQc : IsClosed Q) (hQ : IsConnected Q)
    (hr : r ∈ componentsIn Qᶜ) : IsOpenDisc r := by
  have : LocallyConnectedSpace S := GraphMinor.GM11.IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨a, ha, rfl⟩ := hr
  have hro : IsOpen (connectedComponentIn Qᶜ a) :=
    hQc.isOpen_compl.connectedComponentIn
  have hrc : IsConnected (connectedComponentIn Qᶜ a) :=
    ⟨⟨a, mem_connectedComponentIn ha⟩, isPreconnected_connectedComponentIn⟩
  have hbody : ∀ F : Set S, F ⊆ connectedComponentIn Qᶜ a → IsOArc F →
      ∃ D : Set S, D ⊆ connectedComponentIn Qᶜ a ∧ IsClosedDisc D ∧ discBd D = F := by
    intro F hFr hF
    obtain ⟨D, hD, hbd, hDQ⟩ := GraphMinor.GM11.exists_disc_missing hS hsph hF
      hQ.isPreconnected (disjoint_left.mpr (fun x hxQ hxF =>
        connectedComponentIn_subset Qᶜ a (hFr hxF) hxQ))
    have hDc : IsConnected D := hD.isPathConnected.isConnected
    obtain ⟨eF⟩ := hF
    let v : S := (eF 1).1
    have hv : v ∈ F := (eF 1).2
    have hvD : v ∈ D := discBd_subset D (hbd.symm ▸ hv)
    have hvR : v ∈ connectedComponentIn Qᶜ a := hFr hv
    have hDsub : D ⊆ Qᶜ := fun x hx hxQ => disjoint_left.mp hDQ hx hxQ
    have hcomp : connectedComponentIn Qᶜ v = connectedComponentIn Qᶜ a :=
      (connectedComponentIn_eq hvR).symm
    refine ⟨D, ?_, hD, hbd⟩
    rw [← hcomp]
    exact hDc.isPreconnected.subset_connectedComponentIn hvD hDsub
  rcases open_disc S (connectedComponentIn Qᶜ a) hS inferInstance hrc hro hbody with h | h
  · obtain ⟨x, hx⟩ := hQ.nonempty
    exact False.elim ((connectedComponentIn_subset Qᶜ a (h.2 ▸ mem_univ x)) hx)
  · exact h

end GraphMinor.GM06
