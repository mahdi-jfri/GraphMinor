module

public import GraphMinor.GM06.Section5DiscFrontierPaths
import GraphMinor.Surface.DiscNbhd
import GraphMinor.GM11.Regions
import GraphMinor.GM11.PerimeterPull

/-!
# Incidence extends along a cut-disc edge

Embed a disc drawing containing its boundary in a sphere. Its old
regions remain whole regions. Incidence with one point of an edge
therefore extends along the edge by the sphere edge-side lemma.
Closedness and injectivity of the embedding bring the incidence
back to the disc. This makes the added gap edge incident with the
chosen cut region in the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u

/-- In a disc drawing containing its boundary, incidence at one point
of an edge implies incidence along the whole edge. -/
theorem edge_subset_closure_of_incident_disc_region
    {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S)
    {F : Drawing S} (hbd : bd S ⊆ F.U) {r e : Set S}
    (hr : r ∈ F.R) (he : e ∈ F.E) (hinc : (e ∩ closure r).Nonempty) :
    e ⊆ closure r := by
  let : CompactSpace S := compactSpace_of_isClosedDiscSpace hDisc
  let : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  obtain ⟨p, hp, hpr⟩ := hinc
  let : Nonempty S := ⟨p⟩
  have hS : IsSurface S := ⟨inferInstance, inferInstance,
    fun q => isManifoldPoint_of_disc hDisc.isClosedDisc_univ Filter.univ_mem⟩
  obtain ⟨j, hj, hopen, _⟩ := exists_closedDisc_sphere_embedding hDisc
  have hR := image_region_of_boundary_subset hS hj hopen hbd hr
  have heH : j '' e ∈ (GM07.embedDrawing hj F).E := by
    rw [GM07.embedDrawing_E]
    exact mem_image_of_mem _ he
  have hincH : ((j '' e) ∩ closure (j '' r)).Nonempty := by
    refine ⟨j p, mem_image_of_mem j hp, ?_⟩
    rw [hj.closure_image_eq]
    exact mem_image_of_mem j hpr
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hSphere := IsSphere.isClosedSurface hsph
  have hsub := edge_subset_closure_of_incident hSphere.1 heH hR hincH
  intro x hx
  have hxc := hsub (mem_image_of_mem j hx)
  rw [hj.closure_image_eq] at hxc
  obtain ⟨y, hy, hyx⟩ := hxc
  exact hj.injective hyx ▸ hy

end GraphMinor.GM06
