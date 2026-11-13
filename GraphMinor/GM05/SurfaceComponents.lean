module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutComp
import Mathlib.Topology.Connected.Clopen

/-!
# Components of closed surfaces

For the disconnected-surface case of GM V, (8.10), work in the
component containing the circle and leave the other components
unchanged. A closed surface has finitely many components. The fibers
of its connected-component quotient form a disjoint clopen connected
cover, and each fiber is itself a closed surface.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u

/-- A closed surface has finitely many connected components. -/
theorem finite_surface_components {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S) :
    Finite (ConnectedComponents S) := by
  let : CompactSpace S := hS.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hs.locallyConnected
  infer_instance

/-- Each component fiber of a closed surface is open and closed. -/
theorem surface_component_isClopen {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    (c : ConnectedComponents S) : IsClopen (ConnectedComponents.mk ⁻¹' {c} : Set S) := by
  let : T2Space S := hS.2.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hs.locallyConnected
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact ⟨isClosed_connectedComponent,isOpen_connectedComponent⟩

/-- Every component fiber is nonempty and connected. -/
theorem surface_component_isConnected {S : Type u} [TopologicalSpace S]
    (c : ConnectedComponents S) : IsConnected (ConnectedComponents.mk ⁻¹' {c} : Set S) := by
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/-- Distinct component fibers are disjoint. -/
theorem surface_components_disjoint (S : Type u) [TopologicalSpace S] :
    Pairwise (fun c d : ConnectedComponents S ↦
      Disjoint (ConnectedComponents.mk ⁻¹' {c} : Set S) (ConnectedComponents.mk ⁻¹' {d})) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hc hd
  exact hcd ((show ConnectedComponents.mk x=c from hc).symm.trans hd)

/-- The component fibers cover the whole surface. -/
theorem surface_components_cover (S : Type u) [TopologicalSpace S] :
    (⋃ c : ConnectedComponents S,(ConnectedComponents.mk ⁻¹' {c} : Set S))=univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  exact mem_iUnion.mpr ⟨ConnectedComponents.mk x,rfl⟩

/-- An open-and-closed part of a closed surface is a closed surface. -/
theorem isClosedSurface_clopen {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    {U : Set S} (hU : IsClopen U) : IsClosedSurface U := by
  let : CompactSpace S := hS.1
  let : T2Space S := hS.2.1
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU.1.isCompact
  refine ⟨inferInstance,inferInstance,?_⟩
  intro x
  exact (isInteriorPoint_sub hU.2).mpr (hS.2.2 x.1)

/-- A component fiber of a closed surface is itself a closed surface. -/
theorem isClosedSurface_component {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    (c : ConnectedComponents S) : IsClosedSurface (ConnectedComponents.mk ⁻¹' {c} : Set S) := by
  exact isClosedSurface_clopen hS (surface_component_isClopen hS c)

end GraphMinor.GM05
