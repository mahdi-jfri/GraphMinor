module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.LocalCone
import GraphMinor.GM06.Section5CircuitHalfEdges
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM11.OArcCircuit
import GraphMinor.GM06.Section4PathTools

/-!
# Polar charts at cuff vertices with any positive number of paths

For the rotation input of VI (5.7), page 133, a cuff is a circle
in the augmented drawing. Its circuit supplies two incident directed
ends at every vertex, even when the whole cuff is a single loop.
The finite-drawing polar-chart theorem therefore applies at each
initial vertex without a restriction to two or more linkage paths.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u

/-- A vertex on a circle contained in a finite drawing has a polar
chart, including when it is the only drawing vertex on that circle. -/
theorem exists_polar_at_vertex_on_circle
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {B : Set S} (hB : IsOArc B)
    (hBU : B ⊆ Γ.U) {v : S} (hv : v ∈ Γ.V) (hvB : v ∈ B) :
    ∃ Φ : C(ClosedUnitDisc, S), IsPolar Γ v Φ := by
  let : T2Space S := hS.2.1
  let : Nonempty S := ⟨v⟩
  obtain ⟨C, hC, hCΓ, hCU⟩ := exists_circuit_of_oArc hB hBU
  have hvC : v ∈ C.V := vertex_mem_of_mem_subdrawing_point_set hCΓ (hCU.symm ▸ hvB) hv
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  exact exists_isPolar_of_sectors hS hγ hv
    (two_le_card_halfEdges_of_circuit_vertex hγ hC hCΓ hvC)

/-- Adjoining the cuffs gives a polar chart at every initial vertex,
including the case of a single linkage path. -/
theorem exists_polar_at_initial_vertex_on_cuff
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U) (i : Fin k) :
    ∃ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane),
      IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ := by
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
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
  have hv : cylinderToSphere (cylinderM1Point k i) ∈ (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem _ (hGF.1 ((L.isSubdrawing i).1.1
      (isPathDrawing_end_vertices (L.isPath i)).1))
  exact exists_polar_at_vertex_on_circle hS.1 hB hBU hv
    (mem_image_of_mem _ (show cylinderM1Point k i ∈ cylinderCuff1 from rfl))

end GraphMinor.GM06
