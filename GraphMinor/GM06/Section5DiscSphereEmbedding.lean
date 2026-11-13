module

public import GraphMinor.GM06.DiscRegions
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM06.EdgeChart
import GraphMinor.Surface.Gluing
import GraphMinor.Surface.Wedge
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.SurfacePull
import GraphMinor.GM11.PerimeterPull

/-!
# Embedding the cut disc in a sphere

A closed disc space has a closed embedding in the sphere. Its interior
has open image, while a boundary point has no sphere neighbourhood
contained in the image. These two facts let the cut-disc region walk
in VI (5.1) use the sphere boundary-walk lemmas without identifying
the two sides of the linkage path.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u v

private theorem interiorPoint_of_embedding_interior_range
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) {x : X}
    (hy : IsInteriorPoint (f x)) (hx : f x ∈ interior (range f)) : IsInteriorPoint x := by
  obtain ⟨U, hU, hxU, hsub, ⟨e⟩⟩ := hy.exists_subset isOpen_interior hx
  have hr : f '' (f ⁻¹' U) = U := image_preimage_eq_of_subset (hsub.trans interior_subset)
  exact ⟨f ⁻¹' U, hU.preimage hf.continuous, hxU,
    ⟨(hf.homeomorphImage _).trans ((Homeomorph.setCongr hr).trans e)⟩⟩

/-- A closed disc space embeds in the sphere with open interior image.
A boundary point cannot have a sphere neighbourhood inside that image. -/
theorem exists_closedDisc_sphere_embedding
    {S : Type u} [TopologicalSpace S] (hS : IsClosedDiscSpace S) :
    ∃ j : S → OnePoint EuclideanPlane, IsClosedEmbedding j ∧
      IsOpen (j '' (bd S)ᶜ) ∧
      ∀ x ∈ bd S, j x ∉ interior (range j) := by
  obtain ⟨e⟩ := hS
  let : CompactSpace S := compactSpace_of_isClosedDiscSpace ⟨e⟩
  let : T2Space S := t2Space_of_isClosedDiscSpace ⟨e⟩
  let : Nonempty S := ⟨e ⟨0, by simp [ClosedUnitDisc]⟩⟩
  let j : S → OnePoint EuclideanPlane := fun x => ((e.symm x).1 : OnePoint EuclideanPlane)
  have hjc : Continuous j := OnePoint.isOpenEmbedding_coe.continuous.comp
    (continuous_subtype_val.comp e.symm.continuous)
  have hji : Function.Injective j := by
    intro x y h
    exact e.symm.injective (Subtype.ext (OnePoint.coe_injective h))
  have hj : IsClosedEmbedding j := hjc.isClosedEmbedding hji
  have hU : IsClosedDisc (univ : Set S) :=
    IsClosedDiscSpace.isClosedDisc_univ ⟨e⟩
  obtain ⟨hD, hDb⟩ := isClosedDisc_image_injOn hU isCompact_univ
    hjc.continuousOn hji.injOn
  rw [image_univ] at hD hDb
  rw [discBd_univ] at hDb
  have hInt : j '' (bd S)ᶜ = discInt (range j) := by
    rw [discInt, hDb]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨mem_range_self x, ?_⟩
      rintro ⟨y, hy, hyx⟩
      exact hx (hji hyx ▸ hy)
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, fun h => hx ⟨x, h, rfl⟩, rfl⟩
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hSphere := GM11.IsSphere.isClosedSurface hsph
  refine ⟨j, hj, ?_, ?_⟩
  · rw [hInt]
    exact hD.isOpen_discInt (fun x => (hSphere.1.2.2 x).isManifoldPoint)
  · intro x hx hxi
    exact hx (interiorPoint_of_embedding_interior_range hj.isEmbedding
      (hSphere.1.2.2 _) hxi)

end GraphMinor.GM06
