module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Section4c

/-!
# Propagating region incidence along a cylinder edge

The Reduction 3 argument in VI (5.5), page 130, needs to transfer
incidence along the contracted edge. Adjoining the cuffs and capping
the cylinder reduces this to the two-side incidence lemma on a sphere.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A cylinder region incident with a point of an edge is incident
with the whole closed edge, including both ends. -/
theorem closure_edge_subset_closure_region_of_incident
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) {e R : Set ClosedCylinder}
    (he : e ∈ G.E) (hR : R ∈ G.R) (hinc : (e ∩ closure R).Nonempty) :
    closure e ⊆ closure R := by
  obtain ⟨F, hGF, hFU, _⟩ := exists_drawing_adjoining_boundary L hG
  have heF : e ∈ F.E := hGF.2 he
  have hes : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ heF
  have hRS := image_region_sdiff_boundary_mem_sphere_regions hFU hR
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GraphMinor.GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hi : (cylinderToSphere '' e ∩
      closure (cylinderToSphere '' (R \ bd ClosedCylinder))).Nonempty := by
    obtain ⟨x, hxe, hxR⟩ := hinc
    rw [closure_image_region_sdiff_boundary hR]
    exact ⟨cylinderToSphere x, mem_image_of_mem _ hxe, mem_image_of_mem _ hxR⟩
  have hedge := GraphMinor.GM11.edge_subset_closure_of_incident hS hes hRS hi
  apply closure_minimal _ isClosed_closure
  intro x hx
  have hxr := hedge (mem_image_of_mem cylinderToSphere hx)
  rw [closure_image_region_sdiff_boundary hR] at hxr
  obtain ⟨y, hy, heq⟩ := hxr
  exact injective_cylinderToSphere heq ▸ hy

/-- If a region closure meets a closed non-loop edge, it meets an end.
An interior contact in fact gives both ends. -/
theorem endpoint_mem_closure_region_of_closed_edge_contact
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) {e R : Set ClosedCylinder}
    {s v : ClosedCylinder} (hl : G.toGraph.IsLink e s v)
    (hR : R ∈ G.R) (hcontact : (closure e ∩ closure R).Nonempty) :
    s ∈ closure R ∨ v ∈ closure R := by
  obtain ⟨x, hxe, hxR⟩ := hcontact
  by_cases hxV : x ∈ G.V
  · have hxends : x ∈ ({s, v} : Set ClosedCylinder) :=
      hl.2.2.2 ▸ ⟨hxe, hxV⟩
    rcases hxends with rfl | hxv
    · exact Or.inl hxR
    · exact Or.inr (mem_singleton_iff.mp hxv ▸ hxR)
  · have hxi : x ∈ e := G.closure_diff_V hl.1 ▸ ⟨hxe, hxV⟩
    have hwhole := closure_edge_subset_closure_region_of_incident L hG hl.1 hR ⟨x, hxi, hxR⟩
    have hs : s ∈ closure e := by
      have he : s ∈ closure e ∩ G.V := hl.2.2.2 ▸ (mem_insert s {v})
      exact he.1
    exact Or.inl (hwhole hs)

end GraphMinor.GM06
