module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverLocalHomeomorph
import GraphMinor.GM06.Section5LiftedEdgeIncidence
import GraphMinor.GM11.PerimeterPull

/-!
# Edge incidence in a chosen cylinder sheet

For VI (5.5), page 130, a connected lifted edge meets the closure
of a lifted face either everywhere or nowhere. The angular cover
has local sphere charts at every interior edge point. The general
lifted two-side argument therefore applies to the sphere drawing
obtained from the cylinder drawing.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Incidence propagates along a connected lift of an old cylinder
edge, for components of the complement of a drawing containing it. -/
theorem lifted_cylinder_edge_subset_closure_component
    {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) {e : Set ClosedCylinder}
    (he : e ∈ G.E) (heF : e ∈ F.E) {A r : Set CylinderCover}
    (hA : IsPreconnected A) (hAe : A ⊆ cylinderCoverProjection ⁻¹' e)
    (hr : r ∈ componentsIn (cylinderCoverProjection ⁻¹' F.Uᶜ))
    (hinc : (A ∩ closure r).Nonempty) : A ⊆ closure r := by
  let f : CylinderCover → OnePoint EuclideanPlane :=
    fun p => cylinderToSphere (cylinderCoverProjection p)
  have hpre : f ⁻¹' (cylinderSphereDrawing F).Uᶜ =
      cylinderCoverProjection ⁻¹' F.Uᶜ := by
    rw [cylinderSphereDrawing_U]
    ext p
    constructor
    · intro hp hpf
      exact hp (mem_image_of_mem cylinderToSphere hpf)
    · intro hp hpf
      obtain ⟨x, hx, heq⟩ := hpf
      have hxp : x = cylinderCoverProjection p := injective_cylinderToSphere heq
      exact hp (hxp ▸ hx)
  have hr' : r ∈ componentsIn (f ⁻¹' (cylinderSphereDrawing F).Uᶜ) := hpre.symm ▸ hr
  have heS : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ heF
  have hAeS : A ⊆ f ⁻¹' (cylinderToSphere '' e) :=
    fun p hp => mem_image_of_mem cylinderToSphere (hAe hp)
  have hlocal : IsLocalHomeomorphOn f A :=
    isLocalHomeomorphOn_cover_to_sphere_off_boundary.mono (by
      intro p hp hbd
      exact (he.2.1 (hAe hp)).2 (hG.2.1 ⟨hbd, (he.2.1 (hAe hp)).1⟩))
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GraphMinor.GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  exact lifted_edge_subset_closure_component hS (cylinderSphereDrawing F) f
    heS hA hAeS hlocal hr' hinc

end GraphMinor.GM06
