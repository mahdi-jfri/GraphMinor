module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.LocalCone
import GraphMinor.GM06.Section5ContractionNeighbourPolar
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# Polar charts at initial cuff vertices

For VI (5.5), page 130, the augmented drawing contains the whole
initial cuff. With at least two linkage paths that cuff has two
distinct drawing vertices. Its O-arc therefore supplies the polar
chart used in the attached-side enclosure construction.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- An augmented drawing with at least two linkage paths has an
actual polar chart at each prescribed initial vertex in the capped sphere. -/
theorem exists_polar_at_initial_vertex_of_cuffs
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (i : Fin k) :
    ∃ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane),
      IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ := by
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  let j := finSuccCycle i
  have hji : j ≠ i := finSuccCycle_ne_of_one_lt hk i
  have hsw : cylinderM1Point k i ≠ cylinderM1Point k j := by
    intro he
    exact hji ((cylinderM1Point_injective (lt_trans Nat.zero_lt_one hk)) he).symm
  have hB : IsOArc (cylinderToSphere '' cylinderCuff1) := by
    obtain ⟨b⟩ := isOArc_cylinderCuff1
    exact ⟨b.trans (isClosedEmbedding_cylinderToSphere.isEmbedding.homeomorphImage cylinderCuff1)⟩
  have hBU : cylinderToSphere '' cylinderCuff1 ⊆ (cylinderSphereDrawing F).U := by
    rw [cylinderSphereDrawing_U]
    apply image_mono
    intro x hx
    apply hbdF
    rw [bd_closedCylinder]
    exact Or.inl hx
  have hv (l : Fin k) : cylinderToSphere (cylinderM1Point k l) ∈ (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem _ (hGF.1 ((L.isSubdrawing l).1.1
      (isPathDrawing_end_vertices (L.isPath l)).1))
  exact exists_polar_at_vertex_on_oArc hS.1 (cylinderSphereDrawing F) hB hBU (hv i) (hv j)
    (mem_image_of_mem _ (show cylinderM1Point k i ∈ cylinderCuff1 from rfl))
    (mem_image_of_mem _ (show cylinderM1Point k j ∈ cylinderCuff1 from rfl))
    (fun he => hsw (injective_cylinderToSphere he))

end GraphMinor.GM06
