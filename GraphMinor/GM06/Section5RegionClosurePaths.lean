module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5CapDrawing
import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM06.Section5FrontierPaths
import GraphMinor.GM06.Section5PullPaths
import GraphMinor.GM06.Section5DrawingConnected
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.PaintingFacts

/-!
# Region paths in the augmented cylinder drawing

The region walk for VI (5.1), page 129, can be read in the sphere and
pulled back to the cylinder. A vertex of G in the old region closure
lies on the frontier of the sphere region. Thus any two such vertices
are joined in the augmented drawing by a path in that closure. The
later use of the reduction exclusions chooses the required side of
this boundary path.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Two distinct vertices in an old region closure are joined along
that closure after the cuff arcs have been adjoined. -/
theorem exists_subpath_in_region_closure_of_adjoining_boundary
    {G F : Drawing ClosedCylinder} (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) (hconn : IsConnected F.U)
    {r : Set ClosedCylinder} (hr : r ∈ G.R) {a b : ClosedCylinder}
    (ha : a ∈ G.V ∩ closure r) (hb : b ∈ G.V ∩ closure r) (hab : a ≠ b) :
    ∃ Q : Drawing ClosedCylinder, IsSubpathOf F Q a b ∧ Q.U ⊆ closure r := by
  let D := cylinderSphereDrawing F
  let Y := cylinderToSphere '' (r \ bd ClosedCylinder)
  have hY : Y ∈ D.R := image_region_sdiff_boundary_mem_sphere_regions hFU hr
  have hD : D.IsTwoCell := cylinderSphereDrawing_isTwoCell hconn
  have hFE : F.E.Nonempty := by
    obtain ⟨x, hxC, hxG⟩ := (infinite_of_isOArc isOArc_cylinderCuff1).exists_notMem_finite G.finite_V
    have hxF : x ∈ F.U := by
      rw [hFU, bd_closedCylinder]
      exact Or.inr (Or.inl hxC)
    have hxFV : x ∉ F.V := by rw [hFV]; exact hxG
    obtain ⟨e, he, _⟩ := F.exists_edge_of_mem hxF hxFV
    exact ⟨e, he⟩
  have hDE : D.E.Nonempty := by
    rw [cylinderSphereDrawing_E]
    exact hFE.image _
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
  obtain ⟨P, hP, hPU⟩ := exists_subpath_in_region_frontier hS.1 hsph hD hDE hY
    (hfront a ha) (hfront b hb) hab'
  obtain ⟨Q, hQ, hQU⟩ := exists_subpath_of_sphere_subpath hab hP
  refine ⟨Q, hQ, ?_⟩
  intro x hx
  have hxcl : cylinderToSphere x ∈ closure Y := (hPU (hQU ⟨x, hx, rfl⟩)).1
  rw [closure_image_region_sdiff_boundary hr] at hxcl
  obtain ⟨y, hy, heq⟩ := hxcl
  exact (injective_cylinderToSphere heq) ▸ hy

end GraphMinor.GM06
