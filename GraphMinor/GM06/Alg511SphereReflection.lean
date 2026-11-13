module

public import GraphMinor.GM06.Section5ReflectionDrawing
public import GraphMinor.GM07.Section9MoveOff
public import GraphMinor.GM06.Section5CapDrawing
import GraphMinor.GM06.Alg511AnnulusExtension
import GraphMinor.GM06.Section4
import Mathlib.Tactic

/-!
# Extending the actual cylinder reflection to the sphere

The drawing input for VI (5.11), page 134, uses the sphere drawing
obtained by capping the cylinder. Conjugate the cylinder reflection
to its planar annulus and extend across the two complementary caps.
The annular map preserves radii, so the cap extension applies.
Compactifying the resulting plane homeomorphism gives a sphere
homeomorphism that agrees with reflection at every cylinder point.
The last lemmas identify its action on edges and the whole drawing.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem exists_annular_coordinates :
    ∃ j : ClosedCylinder ≃ₜ alg511Annulus,
      ∀ p, (j p).val = complexPlane.symm (cylToPlane p) := by
  let f : ClosedCylinder → alg511Annulus := fun p =>
    ⟨complexPlane.symm (cylToPlane p), by
      change 1 / 2 ≤ ‖complexPlane.symm (cylToPlane p)‖ ∧
        ‖complexPlane.symm (cylToPlane p)‖ ≤ 1
      rw [complexPlane.symm.norm_map, norm_cylToPlane]
      constructor <;> linarith [p.property.1.1, p.property.1.2]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q heq
      apply injective_cylToPlane
      apply complexPlane.symm.injective
      exact congrArg Subtype.val heq
    · intro z
      have hz : complexPlane z.val ∈ range cylToPlane := by
        rw [range_cylToPlane]
        change 1 / 2 ≤ ‖complexPlane z.val‖ ∧ ‖complexPlane z.val‖ ≤ 1
        rw [complexPlane.norm_map]
        exact z.property
      obtain ⟨p, hp⟩ := hz
      refine ⟨p, Subtype.ext ?_⟩
      change complexPlane.symm (cylToPlane p) = z.val
      rw [hp, complexPlane.symm_apply_apply]
  let e : ClosedCylinder ≃ alg511Annulus := Equiv.ofBijective f hf
  have hc : Continuous e := Continuous.subtype_mk
    (complexPlane.symm.continuous.comp continuous_cylToPlane) _
  exact ⟨hc.homeoOfEquivCompactToT2, fun _ => rfl⟩

/-- Reflection of the cylinder extends across its planar caps,
without requiring the formula of the chosen cylinder embedding. -/
theorem alg511_exists_plane_reflection_extension (k : ℕ) :
    ∃ P : EuclideanPlane ≃ₜ EuclideanPlane,
      ∀ p, P (cylToPlane p) = cylToPlane (section5CylinderReflection k p) := by
  obtain ⟨j, hj⟩ := exists_annular_coordinates
  have hjn (p : ClosedCylinder) : ‖(j p).val‖ = p.val.1 / 2 := by
    rw [hj, complexPlane.symm.norm_map, norm_cylToPlane]
  let A : alg511Annulus ≃ₜ alg511Annulus :=
    (j.symm.trans (section5CylinderReflection k)).trans j
  have hA (z : alg511Annulus) : ‖(A z).val‖ = ‖z.val‖ := by
    change ‖(j (section5CylinderReflection k (j.symm z))).val‖ = ‖z.val‖
    rw [hjn]
    have h := hjn (j.symm z)
    rw [j.apply_symm_apply] at h
    exact h.symm
  obtain ⟨E, _, hE⟩ := alg511_exists_annulus_extension A hA
  let P : EuclideanPlane ≃ₜ EuclideanPlane :=
    (complexPlane.toHomeomorph.symm.trans E).trans complexPlane.toHomeomorph
  refine ⟨P, ?_⟩
  intro p
  have he := hE (j p)
  change E (j p).val = (j (section5CylinderReflection k (j.symm (j p)))).val at he
  rw [j.symm_apply_apply, hj, hj] at he
  change complexPlane (E (complexPlane.symm (cylToPlane p))) = _
  rw [he, complexPlane.apply_symm_apply]

/-- The concrete sphere drawing has an ambient homeomorphism
realizing the orientation change of VI (5.11) on every point of
the cylinder. -/
theorem alg511_exists_sphere_reflection_extension (k : ℕ) :
    ∃ H : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane,
      ∀ p, H (cylinderToSphere p) = cylinderToSphere (section5CylinderReflection k p) := by
  obtain ⟨P, hP⟩ := alg511_exists_plane_reflection_extension k
  refine ⟨P.onePointCongr, ?_⟩
  intro p
  change OnePoint.map P (cylToPlane p : OnePoint EuclideanPlane) =
    (cylToPlane (section5CylinderReflection k p) : OnePoint EuclideanPlane)
  rw [OnePoint.map_some, hP]

/-- The ambient sphere map acts on every supplied cylinder edge
by the same reflection as the cylinder map itself. -/
theorem alg511_sphere_reflection_image (k : ℕ)
    (H : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane)
    (hH : ∀ p, H (cylinderToSphere p) = cylinderToSphere (section5CylinderReflection k p))
    (A : Set ClosedCylinder) :
    H '' (cylinderToSphere '' A) = cylinderToSphere '' (section5CylinderReflection k '' A) := by
  rw [image_image, image_image]
  congr 1
  funext p
  exact hH p

/-- Capping a reflected drawing gives exactly the drawing carried
by the ambient sphere homeomorphism. Thus its region and polar
chart data can be transported by that same homeomorphism. -/
theorem alg511_sphere_reflectedDrawing_eq (k : ℕ)
    (H : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane)
    (hH : ∀ p, H (cylinderToSphere p) = cylinderToSphere (section5CylinderReflection k p))
    (G : Drawing ClosedCylinder) :
    cylinderSphereDrawing (section5ReflectedDrawing k G) =
      GM07.embedDrawing H.isClosedEmbedding (cylinderSphereDrawing G) := by
  let : Nonempty ClosedCylinder := ⟨cylinderPoint 1 (by simp) 0⟩
  apply Drawing.ext_of_V_E
  · rw [cylinderSphereDrawing_V, section5ReflectedDrawing_V, GM07.embedDrawing_V,
      cylinderSphereDrawing_V, alg511_sphere_reflection_image k H hH]
  · rw [cylinderSphereDrawing_E, section5ReflectedDrawing_E, GM07.embedDrawing_E,
      cylinderSphereDrawing_E]
    rw [image_image, image_image]
    congr 1
    funext A
    exact (alg511_sphere_reflection_image k H hH A).symm

end GraphMinor.GM06
