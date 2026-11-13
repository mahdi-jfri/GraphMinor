module

public import GraphMinor.GM06.Defs
import GraphMinor.GM07.Section11f
import GraphMinor.GM11.Regions
import GraphMinor.Surface.SurfacePull
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.CutCyl
import GraphMinor.Surface.AddCrosscap

/-!
# Removing the cuff points from a region

In the region argument for VI (5.1), page 129, adding the cuff arcs
removes the cuff points from each old region. An open set of a surface
is dense in its part off the boundary, because interior points are
dense in every surface chart. The off-boundary part of a region is
also connected. Thus this removal preserves the incidences at the
boundary vertices when the cylinder is viewed in a sphere.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

universe u

/-- The standard cylinder is a surface, by its two-hole surface model. -/
theorem isSurface_closedCylinder : IsSurface ClosedCylinder := by
  obtain ⟨e⟩ := nonempty_cyl_homeo
  exact isSurface_of_homeo e (isSurface_model 0 0 2).1

/-- Removing the surface boundary from an open set does not change
its closure. -/
theorem closure_sdiff_boundary_of_isOpen
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {Y : Set S} (hY : IsOpen Y) : closure (Y \ bd S) = closure Y := by
  apply Subset.antisymm (closure_mono sdiff_subset)
  apply closure_minimal _ isClosed_closure
  intro x hx
  rw [mem_closure_iff]
  intro N hN hxN
  obtain ⟨y, hy, hynb⟩ := mem_closure_iff.mp (mem_closure_compl_bd (hS.2.2 x))
    (N ∩ Y) (hN.inter hY) ⟨hxN, hx⟩
  exact ⟨y, hy.1, hy.2, hynb⟩

/-- The off-boundary part of a region is nonempty and connected, and
has the same closure as that region. -/
theorem region_sdiff_boundary_connected_and_closure
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {G : Drawing S} {r : Set S} (hr : r ∈ G.R) :
    IsConnected (r \ bd S) ∧ closure (r \ bd S) = closure r := by
  let : T2Space S := hS.2.1
  let : LocallyConnectedSpace S := IsSurface.locallyConnected hS
  have hro : IsOpen r := GM11.region_isOpen hr
  have hcl := closure_sdiff_boundary_of_isOpen hS hro
  have hpre := GM07.isPreconnected_diff_bd hS hro (GM11.region_isPreconnected hr)
  obtain ⟨a, ha⟩ := GM11.region_nonempty hr
  have haCl : a ∈ closure (r \ bd S) := hcl.symm ▸ subset_closure ha
  obtain ⟨x, _, hx⟩ := mem_closure_iff.mp haCl univ isOpen_univ (mem_univ a)
  exact ⟨⟨⟨x, hx⟩, hpre⟩, hcl⟩

end GraphMinor.GM06
