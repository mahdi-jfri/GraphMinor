module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM06.Section3Dual
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5DetachedComponentEnclosures
import GraphMinor.GM06.Section5AnnulusInterior
import GraphMinor.GM11.PerimeterPull
import GraphMinor.Surface.SurfacePull
import GraphMinor.Surface.Disc

/-!
# Bringing detached-component enclosures back to the cylinder

For Reduction 2 of VI (5.5), page 130, a root component containing
the cuffs blocks passage from the open annulus to either cap of
the sphere. A connected enclosure missing that root and meeting
the cylinder therefore stays inside the open annulus. The closed
embedding pulls its disc and boundary back to the cylinder.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A connected set missing both cuff images and meeting the
annulus stays in its interior. -/
theorem subset_open_annulus_of_preconnected_of_disjoint_cuffs
    {D : Set (OnePoint EuclideanPlane)} (hD : IsPreconnected D)
    (hbd : Disjoint D (cylinderToSphere '' bd ClosedCylinder))
    (hmeet : (D ∩ range cylinderToSphere).Nonempty) :
    D ⊆ cylinderToSphere '' (bd ClosedCylinder)ᶜ := by
  let A := cylinderToSphere '' (bd ClosedCylinder)ᶜ
  let B := (range cylinderToSphere)ᶜ
  have hcover : D ⊆ A ∪ B := by
    intro z hz
    by_cases hzr : z ∈ range cylinderToSphere
    · obtain ⟨x, rfl⟩ := hzr
      refine Or.inl ⟨x, ?_, rfl⟩
      exact fun hxb => disjoint_left.mp hbd hz (mem_image_of_mem _ hxb)
    · exact Or.inr hzr
  have hdis : Disjoint A B := disjoint_left.mpr (by
    rintro _ ⟨x, _, rfl⟩ hx
    exact hx (mem_range_self x))
  rcases hD.subset_or_subset isOpen_image_cylinderToSphere_compl_boundary
    isClosedEmbedding_cylinderToSphere.isClosed_range.isOpen_compl hdis hcover with h | h
  · exact h
  · obtain ⟨x, hxD, hxR⟩ := hmeet
    exact False.elim (h hxD hxR)

/-- Components detached from a sphere-image root containing both
cuffs have a finite cylinder-disc cover. Its boundaries miss the
entire cylinder drawing and its discs miss both cuffs. -/
theorem exists_cylinder_discs_enclosing_detached_components
    (G : Drawing ClosedCylinder)
    {C : Graph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane))}
    (hC : IsGraphComponent C (cylinderSphereDrawing G).toGraph)
    (hCbd : cylinderToSphere '' bd ClosedCylinder ⊆ compPointSet C) :
    ∃ F : Set (Set ClosedCylinder), F.Finite ∧
      (∀ D ∈ F, IsClosedDisc D ∧ Disjoint D (bd ClosedCylinder) ∧
        Disjoint (discBd D) G.U) ∧
      G.U \ cylinderToSphere ⁻¹' compPointSet C ⊆ ⋃ D ∈ F, discInt D := by
  let : Nonempty ClosedCylinder := ⟨cylinderPoint 1 (by simp) 0⟩
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GraphMinor.GM11.IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  obtain ⟨F, hF, hdisc, hcover⟩ := exists_discs_enclosing_detached_components
    hS.1 hsph (cylinderSphereDrawing G) hC
  have hsub (D) (hD : D ∈ F) : D ⊆ range cylinderToSphere := by
    obtain ⟨hDc, hDQ, _, x, hxD, hxG⟩ := hdisc D hD
    have hbd : Disjoint D (cylinderToSphere '' bd ClosedCylinder) := hDQ.mono_right hCbd
    have hxR : x ∈ range cylinderToSphere := by
      rw [cylinderSphereDrawing_U] at hxG
      exact image_subset_range _ _ hxG
    exact (subset_open_annulus_of_preconnected_of_disjoint_cuffs
      hDc.isPathConnected.isConnected.isPreconnected hbd ⟨x, hxD, hxR⟩).trans
      (image_subset_range _ _)
  have hpull (D) (hD : D ∈ F) := isClosedDisc_preimage
    isClosedEmbedding_cylinderToSphere (hdisc D hD).1 (hsub D hD)
  refine ⟨(fun D => cylinderToSphere ⁻¹' D) '' F, hF.image _, ?_, ?_⟩
  · rintro _ ⟨D, hD, rfl⟩
    refine ⟨(hpull D hD).1, ?_, ?_⟩
    · exact disjoint_left.mpr (fun x hx hxb => disjoint_left.mp (hdisc D hD).2.1 hx
        (hCbd (mem_image_of_mem _ hxb)))
    · rw [(hpull D hD).2]
      exact disjoint_left.mpr (fun x hx hxG => disjoint_left.mp (hdisc D hD).2.2.1 hx
        (by rw [cylinderSphereDrawing_U]; exact mem_image_of_mem _ hxG))
  · rintro x ⟨hxG, hxC⟩
    have hx : cylinderToSphere x ∈ (cylinderSphereDrawing G).U \ compPointSet C := by
      rw [cylinderSphereDrawing_U]
      exact ⟨mem_image_of_mem _ hxG, hxC⟩
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp (hcover hx)
    refine mem_iUnion₂.mpr ⟨cylinderToSphere ⁻¹' D, mem_image_of_mem _ hD, ?_⟩
    refine ⟨hxD.1, ?_⟩
    rw [(hpull D hD).2]
    exact hxD.2

end GraphMinor.GM06
