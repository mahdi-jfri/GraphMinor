module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DeletedEdgeFaces
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Section4c

/-!
# The approach region for a helix before edge deletion

For VI (5.5), page 131, cap the cylinder cuffs and apply the old-face
choice on the sphere. An old sphere face lies inside the embedded
cylinder, since it lies in the new face there. A point of that face
identifies the corresponding cylinder region. The closure formula
for capping then transfers incidence with both the deleted edge and
the last helix point back to the cylinder.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- The old region chosen in the Reduction 1 proof of VI (5.5),
page 131, is incident with both the initial vertex and the last
point of the new region. -/
theorem exists_old_cylinder_region_at_deleted_edge_region_closure
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hU : G'.U = G.U \ e)
    {R : Set ClosedCylinder} (hR : R ∈ G'.R) (heR : e ⊆ R)
    {s w : ClosedCylinder} (hs : s ∈ closure e) (hw : w ∈ closure R) :
    ∃ r ∈ G.R, r ⊆ R ∧ s ∈ closure r ∧ w ∈ closure r := by
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  obtain ⟨F, hGF, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
  have heF : e ∈ F.E := hGF.2 he
  have heBd : Disjoint e (bd ClosedCylinder) := by
    refine disjoint_left.mpr ?_
    intro x hxe hxbd
    exact (he.2.1 hxe).2 (hG.2.1 ⟨hxbd, (he.2.1 hxe).1⟩)
  let D := F.deleteEdge e
  have hDU : D.U = G'.U ∪ bd ClosedCylinder := by
    rw [show D.U = F.U \ e from deleteEdge_U F heF, hFU, hU]
    ext x
    constructor
    · rintro ⟨hx | hx, hno⟩
      · exact Or.inl ⟨hx, hno⟩
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨Or.inl hx.1, hx.2⟩
      · exact ⟨Or.inr hx, fun h => disjoint_left.mp heBd h hx⟩
  let A := cylinderSphereDrawing F
  let es := cylinderToSphere '' e
  let RS := cylinderToSphere '' (R \ bd ClosedCylinder)
  have hes : es ∈ A.E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ heF
  have hAB : (A.deleteEdge es).U = (cylinderSphereDrawing D).U := by
    rw [deleteEdge_U A hes, cylinderSphereDrawing_U, cylinderSphereDrawing_U,
      show D.U = F.U \ e from deleteEdge_U F heF, image_sdiff injective_cylinderToSphere]
  have hRS : RS ∈ (A.deleteEdge es).R := by
    change RS ∈ componentsIn (univ \ (A.deleteEdge es).U)
    rw [hAB]
    exact image_region_sdiff_boundary_mem_sphere_regions hDU hR
  have heRS : es ⊆ RS := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, ⟨heR hx, fun h => disjoint_left.mp heBd hx h⟩, rfl⟩
  have hwRS : cylinderToSphere w ∈ closure RS := by
    rw [closure_image_region_sdiff_boundary hR]
    exact mem_image_of_mem _ hw
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  obtain ⟨a, ha, haRS, hea, hwa⟩ :=
    exists_old_region_at_deleted_edge_region_closure hS hes hRS heRS hwRS
  obtain ⟨x, hxa⟩ := region_nonempty ha
  obtain ⟨y, hyR, hyx⟩ := haRS hxa
  have hyoff : y ∉ G.U := by
    intro hyG
    apply region_subset ha hxa
    rw [cylinderSphereDrawing_U]
    exact ⟨y, hFU.symm ▸ Or.inl hyG, hyx⟩
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyoff
  have hrS := image_region_sdiff_boundary_mem_sphere_regions hFU hr
  have heqa : cylinderToSphere '' (r \ bd ClosedCylinder) = a :=
    region_eq_of_mem hrS ha ⟨y, ⟨hyr, hyR.2⟩, hyx⟩ hxa
  have hrR : r ⊆ R := by
    apply subset_region hR (region_isPreconnected hr) _ hyr hyR.1
    refine disjoint_left.mpr ?_
    intro z hzr hzG'
    rw [hU] at hzG'
    exact region_subset hr hzr hzG'.1
  have hwa' : w ∈ closure r := by
    rw [← heqa, closure_image_region_sdiff_boundary hr] at hwa
    obtain ⟨z, hz, hzw⟩ := hwa
    exact injective_cylinderToSphere hzw ▸ hz
  have hsa : cylinderToSphere s ∈ closure a := by
    have hse : cylinderToSphere s ∈ closure es :=
      mem_closure_image continuous_cylinderToSphere.continuousAt hs
    exact closure_minimal hea isClosed_closure hse
  have hsa' : s ∈ closure r := by
    rw [← heqa, closure_image_region_sdiff_boundary hr] at hsa
    obtain ⟨z, hz, hzs⟩ := hsa
    exact injective_cylinderToSphere hzs ▸ hz
  exact ⟨r, hr, hrR, hsa', hwa'⟩

end GraphMinor.GM06
