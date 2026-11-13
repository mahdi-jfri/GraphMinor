module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.RegionCount
import GraphMinor.GM11.PerimeterPull
import GraphMinor.Surface.Gluing

/-!
# Cuff edges have only one side in an old region

For VI (5.1), page 129, a cuff edge adjoined to the cylinder lies
between an old region and the cap. It cannot have two sides in an
old region. A cuff point is not interior to the sphere image of the
cylinder: an interior chart there would pull back to an interior chart
at a boundary point of the cylinder. This gives the needed bound on
its occurrences in the sphere region walk.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u v

private theorem interiorPoint_of_mem_interior_range
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) {x : X}
    (hy : IsInteriorPoint (f x)) (hx : f x ∈ interior (range f)) : IsInteriorPoint x := by
  obtain ⟨U, hU, hxU, hsub, ⟨e⟩⟩ := hy.exists_subset isOpen_interior hx
  have hr : f '' (f ⁻¹' U) = U :=
    image_preimage_eq_of_subset (hsub.trans interior_subset)
  exact ⟨f ⁻¹' U, hU.preimage hf.continuous, hxU,
    ⟨(hf.homeomorphImage _).trans ((Homeomorph.setCongr hr).trans e)⟩⟩

/-- A cuff point has no sphere neighbourhood contained in the image
of the cylinder. -/
theorem cylinderToSphere_boundary_not_mem_interior_range
    {x : ClosedCylinder} (hx : x ∈ bd ClosedCylinder) :
    cylinderToSphere x ∉ interior (range cylinderToSphere) := by
  intro hxi
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := IsSphere.isClosedSurface hsph
  exact hx (interiorPoint_of_mem_interior_range isClosedEmbedding_cylinderToSphere.isEmbedding
    (hS.1.2.2 _) hxi)

/-- An edge lying on a cuff has at most one side in any sphere region
contained in the cylinder image. -/
theorem not_isTwoSided_image_cuff_edge
    {r : Set (OnePoint EuclideanPlane)} (hr : r ⊆ range cylinderToSphere)
    {e : Set ClosedCylinder} (he : e ⊆ bd ClosedCylinder) :
    ¬ IsTwoSided r (cylinderToSphere '' e) := by
  rintro ⟨z, hzE, hzInt⟩
  obtain ⟨x, hx, rfl⟩ := hzE
  have hsub : r ∪ cylinderToSphere '' e ⊆ range cylinderToSphere :=
    union_subset hr (image_subset_range _ _)
  exact cylinderToSphere_boundary_not_mem_interior_range (he hx) (interior_mono hsub hzInt)

end GraphMinor.GM06
