module

public import GraphMinor.GM06.Section5CapDrawing
import GraphMinor.GM06.Section5AnnulusInterior
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.Regions
import GraphMinor.Surface.CutComp

/-!
# Regions after adjoining the cuffs and capping

For VI (5.1), page 129, an old cylinder region becomes a sphere
region after its cuff points are removed. Its image is open and
connected. Every added frontier point lies either in the original
drawing or on a cuff, and hence in the augmented drawing. This makes
the image a whole region, rather than merely a subset of one.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

universe u

private theorem mem_regions_of_connected_open_frontier_subset
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {Y : Set S}
    (hY : IsConnected Y) (hYo : IsOpen Y) (hdis : Disjoint Y G.U)
    (hfr : frontier Y ⊆ G.U) : Y ∈ G.R := by
  obtain ⟨a, ha⟩ := hY.nonempty
  have haoff : a ∈ univ \ G.U := ⟨mem_univ _, fun h => disjoint_left.mp hdis ha h⟩
  let R := connectedComponentIn (univ \ G.U) a
  have haR : a ∈ R := mem_connectedComponentIn haoff
  have hYR : Y ⊆ R := hY.isPreconnected.subset_connectedComponentIn ha
    (fun x hx => ⟨mem_univ _, fun hxG => disjoint_left.mp hdis hx hxG⟩)
  have hcover : R ⊆ Y ∪ (closure Y)ᶜ := by
    intro x hx
    by_cases hxY : x ∈ Y
    · exact Or.inl hxY
    · refine Or.inr ?_
      intro hxcl
      have hxfr : x ∈ frontier Y := ⟨hxcl, by rw [hYo.interior_eq]; exact hxY⟩
      exact (connectedComponentIn_subset _ a hx).2 (hfr hxfr)
  have hsplit : Disjoint Y (closure Y)ᶜ := disjoint_left.mpr fun x hx hxcl => hxcl (subset_closure hx)
  have hRY : R ⊆ Y := by
    rcases isPreconnected_connectedComponentIn.subset_or_subset hYo
      isClosed_closure.isOpen_compl hsplit hcover with h | h
    · exact h
    · exact False.elim (h haR (subset_closure ha))
  exact ⟨a, haoff, Subset.antisymm hRY hYR⟩

/-- Removing the cuff points from a cylinder region and embedding it
in the sphere preserves its closure under the embedding. -/
theorem closure_image_region_sdiff_boundary
    {G : Drawing ClosedCylinder} {r : Set ClosedCylinder} (hr : r ∈ G.R) :
    closure (cylinderToSphere '' (r \ bd ClosedCylinder)) = cylinderToSphere '' closure r := by
  rw [isClosedEmbedding_cylinderToSphere.closure_image_eq,
    (region_sdiff_boundary_connected_and_closure isSurface_closedCylinder hr).2]

/-- A cylinder region off its cuffs is a whole region of the sphere
drawing obtained by adjoining the cuffs. -/
theorem image_region_sdiff_boundary_mem_sphere_regions
    {G F : Drawing ClosedCylinder} (hFU : F.U = G.U ∪ bd ClosedCylinder)
    {r : Set ClosedCylinder} (hr : r ∈ G.R) :
    cylinderToSphere '' (r \ bd ClosedCylinder) ∈ (cylinderSphereDrawing F).R := by
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  have hro : IsOpen r := GM11.region_isOpen hr
  have hYconn := (region_sdiff_boundary_connected_and_closure isSurface_closedCylinder hr).1
  have hYo := isOpen_image_cylinderToSphere_sdiff_boundary hro
  have hdis : Disjoint (cylinderToSphere '' (r \ bd ClosedCylinder)) (cylinderSphereDrawing F).U := by
    rw [cylinderSphereDrawing_U]
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hyx : y = x := injective_cylinderToSphere heq
    subst y
    rw [hFU] at hy
    rcases hy with hxG | hxbd
    · exact GM11.region_subset hr hx.1 hxG
    · exact hx.2 hxbd
  have hfront : frontier (cylinderToSphere '' (r \ bd ClosedCylinder)) ⊆
      (cylinderSphereDrawing F).U := by
    intro z hz
    have hzcl := hz.1
    rw [closure_image_region_sdiff_boundary hr] at hzcl
    obtain ⟨x, hx, rfl⟩ := hzcl
    rw [cylinderSphereDrawing_U]
    refine ⟨x, ?_, rfl⟩
    rw [hFU]
    rcases GM11.closure_region_subset hr hx with hxr | hxG
    · by_cases hxbd : x ∈ bd ClosedCylinder
      · exact Or.inr hxbd
      · have hzY : cylinderToSphere x ∈ cylinderToSphere '' (r \ bd ClosedCylinder) :=
          ⟨x, ⟨hxr, hxbd⟩, rfl⟩
        exact False.elim (hz.2 (hYo.interior_eq.symm ▸ hzY))
    · exact Or.inl hxG
  exact mem_regions_of_connected_open_frontier_subset
    (hYconn.image cylinderToSphere continuous_cylinderToSphere.continuousOn) hYo hdis hfront

end GraphMinor.GM06
