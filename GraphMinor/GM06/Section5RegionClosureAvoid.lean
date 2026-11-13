module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM06.Section5CuffSides
import GraphMinor.GM06.Section5FrontierPaths
import GraphMinor.GM06.Section5PullPathsAvoid
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.PaintingFacts

/-!
# Region paths avoiding an added cuff edge

For VI (5.1), page 129, follow the boundary of Rᵢ without using the
added initial cuff edge. After capping the cylinder, that edge has at
most one side in the old region. The region walk thus yields a path
avoiding it. Pulling that path back preserves both its confinement
to the old region closure and its exclusion of the cuff edge.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Two old vertices in a region closure can be joined along that
closure while avoiding any specified added cuff edge. -/
theorem exists_subpath_in_region_closure_avoiding_cuff_edge
    {G F : Drawing ClosedCylinder} (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) (hconn : IsConnected F.U)
    {r : Set ClosedCylinder} (hr : r ∈ G.R) {a b : ClosedCylinder}
    (ha : a ∈ G.V ∩ closure r) (hb : b ∈ G.V ∩ closure r) (hab : a ≠ b)
    {e : Set ClosedCylinder} (he : e ∈ F.E) (heBd : e ⊆ bd ClosedCylinder) :
    ∃ Q : Drawing ClosedCylinder, IsSubpathOf F Q a b ∧ Q.U ⊆ closure r ∧ e ∉ Q.E := by
  let D := cylinderSphereDrawing F
  let Y := cylinderToSphere '' (r \ bd ClosedCylinder)
  have hY : Y ∈ D.R := image_region_sdiff_boundary_mem_sphere_regions hFU hr
  have hD : D.IsTwoCell := cylinderSphereDrawing_isTwoCell hconn
  have heD : cylinderToSphere '' e ∈ D.E := by
    rw [cylinderSphereDrawing_E]
    exact ⟨e, he, rfl⟩
  have hfront (x : ClosedCylinder) (hx : x ∈ G.V ∩ closure r) :
      cylinderToSphere x ∈ D.V ∩ frontier Y := by
    constructor
    · rw [cylinderSphereDrawing_V, hFV]
      exact ⟨x, hx.1, rfl⟩
    · constructor
      · rw [closure_image_region_sdiff_boundary hr]
        exact ⟨x, hx.2, rfl⟩
      · intro hxInt
        obtain ⟨y, hy, heq⟩ := interior_subset hxInt
        have hyx : y = x := injective_cylinderToSphere heq
        exact region_subset hr (hyx ▸ hy.1) (G.V_subset_U hx.1)
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GM11.IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  have hab' : cylinderToSphere a ≠ cylinderToSphere b := fun h => hab (injective_cylinderToSphere h)
  have hone : ¬ IsTwoSided Y (cylinderToSphere '' e) :=
    not_isTwoSided_image_cuff_edge (image_subset_range _ _) heBd
  obtain ⟨P, hP, hPU, heP⟩ := exists_subpath_in_region_frontier_avoiding_one_sided_edge
    hS.1 hsph hD ⟨_, heD⟩ hY (hfront a ha) (hfront b hb) hab' heD hone
  obtain ⟨Q, hQ, hQU, heQ⟩ := exists_subpath_of_sphere_subpath_avoiding_edge hab hP heP
  refine ⟨Q, hQ, ?_, heQ⟩
  intro x hx
  have hxcl : cylinderToSphere x ∈ closure Y := (hPU (hQU ⟨x, hx, rfl⟩)).1
  rw [closure_image_region_sdiff_boundary hr] at hxcl
  obtain ⟨y, hy, heq⟩ := hxcl
  exact (injective_cylinderToSphere heq) ▸ hy

end GraphMinor.GM06
