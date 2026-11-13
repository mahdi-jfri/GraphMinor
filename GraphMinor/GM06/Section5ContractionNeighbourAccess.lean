module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5ContractionNeighbourEdges
import GraphMinor.GM06.Section5ContractionNeighbourPolar
import GraphMinor.GM06.Section5LiftedPolarAccess
import GraphMinor.GM06.Section5CoverLocalHomeomorph

/-!
# Access to the old neighbour in a specified angular sheet

For Reduction 3 of VI (5.5), page 130, the old neighbour is off
the cuffs and has a polar chart from its two linkage edges. Lift
that chart at the specified neighbour point. The polar access
construction then approaches the selected complementary component
without changing sheets or meeting any other drawing point.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- At a specified lift of the old neighbour, construct a curve
whose positive part lies in the specified incident lifted component. -/
theorem exists_access_at_contraction_neighbour_in_cover
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) (hGF : G.IsSubdrawing F)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (w : CylinderCover) (hw : cylinderCoverProjection w = v)
    {r : Set CylinderCover} (hr : r ∈ componentsIn (cylinderCoverProjection ⁻¹' F.Uᶜ))
    (hwr : w ∈ closure r) :
    ∃ g : C(unitInterval, CylinderCover), g 0 = w ∧ ∀ t, 0 < t → g t ∈ r := by
  have hvbd := contraction_neighbour_not_mem_boundary L hG i hval hl hv hvC
  obtain ⟨Φ, hΦ⟩ := exists_polar_at_contraction_neighbour L i hGF hval hl hv hvC
  let f : CylinderCover → OnePoint EuclideanPlane :=
    fun p => cylinderToSphere (cylinderCoverProjection p)
  have hpV : f w ∈ (cylinderSphereDrawing F).V := by
    rw [show f w = cylinderToSphere v from congrArg cylinderToSphere hw, cylinderSphereDrawing_V]
    exact mem_image_of_mem _ (hGF.1 hl.2.2.1)
  have hpolar : GraphMinor.GM11.IsPolar (cylinderSphereDrawing F) (f w) Φ := by
    change GraphMinor.GM11.IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderCoverProjection w)) Φ
    rw [hw]
    exact hΦ
  have hlocal : IsLocalHomeomorphOn f {w} :=
    isLocalHomeomorphOn_cover_to_sphere_off_boundary.mono (by
      intro p hp
      change cylinderCoverProjection p ∉ bd ClosedCylinder
      rw [mem_singleton_iff.mp hp, hw]
      exact hvbd)
  have hpre : f ⁻¹' (cylinderSphereDrawing F).Uᶜ = cylinderCoverProjection ⁻¹' F.Uᶜ := by
    rw [cylinderSphereDrawing_U]
    ext p
    constructor
    · intro hp hpF
      exact hp (mem_image_of_mem cylinderToSphere hpF)
    · intro hp hpf
      obtain ⟨x, hx, he⟩ := hpf
      exact hp (injective_cylinderToSphere he ▸ hx)
  have hr' : r ∈ componentsIn (f ⁻¹' (cylinderSphereDrawing F).Uᶜ) := hpre.symm ▸ hr
  exact exists_access_curve_in_lifted_component_of_polar (cylinderSphereDrawing F) f w
    hpV hpolar hlocal hr' hwr

end GraphMinor.GM06
