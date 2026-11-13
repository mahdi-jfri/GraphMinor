module

public import GraphMinor.GM06.Section5CapDrawing
import Mathlib.Topology.Maps.Basic

/-!
# The open annulus in the sphere

The image of the cylinder away from its cuffs is the open round
annulus. Thus an open part of the cylinder, with its cuff points
removed, has open image in the sphere. This identifies the old regions
with regions of the drawing with cuff arcs adjoined in the proof of
VI (5.1), page 129.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- The off-cuff cylinder is the open planar annulus under its round
embedding. -/
theorem image_cylToPlane_compl_boundary :
    cylToPlane '' (bd ClosedCylinder)ᶜ = {v : EuclideanPlane | 1 / 2 < ‖v‖ ∧ ‖v‖ < 1} := by
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hnot : p ∉ cylinderCuff1 ∪ cylinderCuff2 := by
      rw [← bd_closedCylinder]
      exact hp
    have h1 : p.1.1 ≠ 1 := fun h => hnot (Or.inl h)
    have h2 : p.1.1 ≠ 2 := fun h => hnot (Or.inr h)
    have hlo : 1 < p.1.1 := (lt_or_eq_of_le p.2.1.1).resolve_right h1.symm
    have hhi : p.1.1 < 2 := (lt_or_eq_of_le p.2.1.2).resolve_right h2
    rw [mem_ofPred_eq, norm_cylToPlane]
    constructor <;> linarith only [hlo, hhi]
  · intro hv
    have hvR : v ∈ range cylToPlane := by
      rw [range_cylToPlane]
      exact ⟨hv.1.le, hv.2.le⟩
    obtain ⟨p, rfl⟩ := hvR
    refine ⟨p, ?_, rfl⟩
    rw [bd_closedCylinder]
    have hlo : 1 / 2 < p.1.1 / 2 := by simpa only [norm_cylToPlane] using hv.1
    have hhi : p.1.1 / 2 < 1 := by simpa only [norm_cylToPlane] using hv.2
    rintro (hp | hp)
    · change p.1.1 = 1 at hp
      rw [hp] at hlo
      exact lt_irrefl _ hlo
    · change p.1.1 = 2 at hp
      rw [hp] at hhi
      norm_num at hhi

/-- The image of the cylinder away from its cuffs is open in the sphere. -/
theorem isOpen_image_cylinderToSphere_compl_boundary :
    IsOpen (cylinderToSphere '' (bd ClosedCylinder)ᶜ) := by
  have him : cylinderToSphere '' (bd ClosedCylinder)ᶜ =
      ((↑) : EuclideanPlane → OnePoint EuclideanPlane) ''
        {v : EuclideanPlane | 1 / 2 < ‖v‖ ∧ ‖v‖ < 1} := by
    rw [← image_cylToPlane_compl_boundary, image_image]
    rfl
  rw [him]
  apply OnePoint.isOpenEmbedding_coe.isOpenMap
  exact (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- An open part of the cylinder has open image in the sphere after
its cuff points are removed. -/
theorem isOpen_image_cylinderToSphere_sdiff_boundary
    {Y : Set ClosedCylinder} (hY : IsOpen Y) :
    IsOpen (cylinderToSphere '' (Y \ bd ClosedCylinder)) := by
  obtain ⟨O, hO, hOY⟩ := isClosedEmbedding_cylinderToSphere.isEmbedding.isInducing.image_eq_isOpen_inter_range hY
  have him : cylinderToSphere '' (Y \ bd ClosedCylinder) =
      O ∩ cylinderToSphere '' (bd ClosedCylinder)ᶜ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxO : cylinderToSphere x ∈ O := by
        have hxIm : cylinderToSphere x ∈ cylinderToSphere '' Y := ⟨x, hx.1, rfl⟩
        rw [hOY] at hxIm
        exact hxIm.1
      exact ⟨hxO, x, hx.2, rfl⟩
    · rintro ⟨hzO, x, hx, rfl⟩
      have hxY : cylinderToSphere x ∈ cylinderToSphere '' Y := by
        rw [hOY]
        exact ⟨hzO, mem_range_self x⟩
      obtain ⟨y, hy, heq⟩ := hxY
      have hyx : y = x := injective_cylinderToSphere heq
      exact ⟨x, ⟨hyx ▸ hy, hx⟩, rfl⟩
  rw [him]
  exact hO.inter isOpen_image_cylinderToSphere_compl_boundary

end GraphMinor.GM06
