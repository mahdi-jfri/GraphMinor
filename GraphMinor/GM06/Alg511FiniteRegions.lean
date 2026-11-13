module

public import GraphMinor.GM06.Alg511AdjoinCuffs
public import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.Regions
import GraphMinor.GM11.PerimeterPull
import Mathlib.Tactic

/-!
# Finite region labels for every cylinder input

The input coverage for VI (5.11), page 134, must hold before any
linkage has been found. Adjoin both cuffs without using a linkage.
Removing the cuff points sends every cylinder region to a sphere
region. This map is injective: a region has an interior point, and
two regions containing that point are equal. Finiteness on the
sphere therefore gives finite region labels for the original input.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11

/-- Every intended cylinder instance has finitely many regions,
including instances in which no linkage exists. -/
theorem alg511_cylinder_regions_finite {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) : G.R.Finite := by
  obtain ⟨F, _, _, _, hFU, _⟩ := alg511_exists_drawing_with_cuffs hG
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GraphMinor.GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  let target := (cylinderSphereDrawing F).R
  let f : G.R → target := fun r =>
    ⟨cylinderToSphere '' (r.val \ bd ClosedCylinder),
      image_region_sdiff_boundary_mem_sphere_regions hFU r.property⟩
  have hf : Function.Injective f := by
    intro r s hrs
    have heq : cylinderToSphere '' (r.val \ bd ClosedCylinder) =
        cylinderToSphere '' (s.val \ bd ClosedCylinder) := congrArg Subtype.val hrs
    have hd : r.val \ bd ClosedCylinder = s.val \ bd ClosedCylinder :=
      Set.image_injective.mpr injective_cylinderToSphere heq
    obtain ⟨p, hpr⟩ :=
      (region_sdiff_boundary_connected_and_closure isSurface_closedCylinder r.property).1.nonempty
    have hps : p ∈ s.val \ bd ClosedCylinder := hd ▸ hpr
    exact Subtype.ext (region_eq_of_mem r.property s.property hpr.1 hps.1)
  let : Finite target := (finite_R hS (cylinderSphereDrawing F)).to_subtype
  let : Finite G.R := Finite.of_injective f hf
  exact Set.toFinite G.R

/-- The regions of every intended cylinder input have a finite
label bijection, independently of target feasibility. -/
theorem alg511_exists_region_labels {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) :
    ∃ r : ℕ, Nonempty (Fin r ≃ G.R) := by
  let : Fintype G.R := (alg511_cylinder_regions_finite hG).fintype
  exact ⟨Fintype.card G.R, ⟨(Fintype.equivFin G.R).symm⟩⟩

end GraphMinor.GM06
