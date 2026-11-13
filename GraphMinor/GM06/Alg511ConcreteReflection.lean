module

public import GraphMinor.GM06.Alg511RotationRelabel
public import GraphMinor.GM06.Alg511SphereReflection
public import GraphMinor.GM06.Alg511ReflectedCuffGaps
import GraphMinor.GM06.Section5ReflectionBoundary
import Mathlib.Tactic

/-!
# The concrete reflection agrees with the cylinder embedding

The positive polar-chart calculation uses a rotated conjugation
of the plane. The orientation step of VI (5.11), page 134, uses
its restriction to the cylinder. The public radial formula for
that embedding identifies these maps at every cylinder point.
Their one-point extensions therefore carry the actual capped
drawing and every edge by the same map.

The cuff edge permutation fixes the original prefix and reverses
each cuff block separately. Its mask retains ordinary parameters
and reverses the prescribed cuff parameters. These equations join
the positive-row calculation to the actual cylinder drawing. No
encoded region row is used.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Rotated conjugation restricts to the actual cylinder reflection
under the radial embedding, at every cylinder point. -/
theorem alg511_concrete_plane_reflection (k : ℕ) (p : ClosedCylinder) :
    alg511PlaneReflection (4 * π / k) (cylToPlane p) = cylToPlane (section5CylinderReflection k p) := by
  apply complexPlane.symm.injective
  rw [alg511PlaneReflection_complex, cylToPlane_apply, cylToPlane_apply]
  simp only [map_smul, complexPlane.symm_apply_apply]
  change (Circle.exp (4 * π / k) : ℂ) * (starRingEnd ℂ) ((p.val.1 / 2) • (p.val.2 : ℂ)) =
    (p.val.1 / 2) • ((Circle.exp (4 * π / k) * p.val.2⁻¹ : Circle) : ℂ)
  rw [Circle.coe_mul, Circle.coe_inv_eq_conj]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

/-- The same concrete reflection acts correctly on every point of
the capped cylinder, so it may transport its positive polar charts. -/
theorem alg511_concrete_sphere_reflection (k : ℕ) (p : ClosedCylinder) :
    (alg511PlaneReflection (4 * π / k)).onePointCongr (cylinderToSphere p) =
      cylinderToSphere (section5CylinderReflection k p) := by
  change OnePoint.map _ (cylToPlane p : OnePoint EuclideanPlane) =
    (cylToPlane (section5CylinderReflection k p) : OnePoint EuclideanPlane)
  rw [OnePoint.map_some, alg511_concrete_plane_reflection]

/-- Capping the actual reflected drawing gives the image by the
concrete sphere reflection used for the positive rotation rows. -/
theorem alg511_concrete_reflectedDrawing_eq (k : ℕ) (G : Drawing ClosedCylinder) :
    cylinderSphereDrawing (section5ReflectedDrawing k G) =
      GM07.embedDrawing (alg511PlaneReflection (4 * π / k)).onePointCongr.isClosedEmbedding
        (cylinderSphereDrawing G) :=
  alg511_sphere_reflectedDrawing_eq k _ (alg511_concrete_sphere_reflection k) G

/-- The cylinder boundary is carried onto itself by reflection. -/
theorem alg511_reflection_image_bd (k : ℕ) :
    section5CylinderReflection k '' bd ClosedCylinder = bd ClosedCylinder := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (section5CylinderReflection_mem_bd k q).mpr hq
  · intro hp
    exact ⟨section5CylinderReflection k p, (section5CylinderReflection_mem_bd k p).mpr hp,
      section5CylinderReflection_involutive k p⟩

/-- Reflection retains the full cuff augmentation and its vertices,
with the reflected original drawing as its subdrawing. -/
theorem alg511_reflected_augmentation {k : ℕ} {G F : Drawing ClosedCylinder}
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V) :
    (section5ReflectedDrawing k G).IsSubdrawing (section5ReflectedDrawing k F) ∧
      (section5ReflectedDrawing k F).U = (section5ReflectedDrawing k G).U ∪ bd ClosedCylinder ∧
      (section5ReflectedDrawing k F).V = (section5ReflectedDrawing k G).V := by
  refine ⟨section5ReflectedDrawing_isSubdrawing hGF, ?_, ?_⟩
  · rw [section5ReflectedDrawing_U, section5ReflectedDrawing_U, hFU, image_union, alg511_reflection_image_bd]
  · rw [section5ReflectedDrawing_V, section5ReflectedDrawing_V, hFV]

/-- Ordinary edge indices stay fixed in the cuff permutation. -/
theorem alg511CuffEdgeReflection_old (m k : ℕ) (j : Fin m) :
    alg511CuffEdgeReflection m k (j.castAdd (k + k)) = j.castAdd (k + k) := by
  apply Fin.ext
  change alg511CuffEdgeReflectionIndex m k j.val = j.val
  simp only [alg511CuffEdgeReflectionIndex, j.isLt, ite_true]

/-- Inner gap indices reverse inside the inner block. -/
theorem alg511CuffEdgeReflection_inner (m k : ℕ) (i : Fin k) :
    alg511CuffEdgeReflection m k ((i.castAdd k).natAdd m) =
      ((Compute.gm06Alg511ReflectGapFin i).castAdd k).natAdd m := by
  apply Fin.ext
  change alg511CuffEdgeReflectionIndex m k (m + i.val) = m + (k - 1 - i.val)
  simp only [alg511CuffEdgeReflectionIndex]
  rw [ite_eq_right (by omega : ¬ m + i.val < m), ite_eq_left (by have := i.isLt; omega), Nat.add_sub_cancel_left]

/-- Outer gap indices reverse inside the outer block. -/
theorem alg511CuffEdgeReflection_outer (m k : ℕ) (i : Fin k) :
    alg511CuffEdgeReflection m k ((i.natAdd k).natAdd m) =
      ((Compute.gm06Alg511ReflectGapFin i).natAdd k).natAdd m := by
  apply Fin.ext
  change alg511CuffEdgeReflectionIndex m k (m + (k + i.val)) = m + (k + (k - 1 - i.val))
  simp only [alg511CuffEdgeReflectionIndex]
  rw [ite_eq_right (by omega : ¬ m + (k + i.val) < m), ite_eq_right (by omega : ¬ m + (k + i.val) < m + k)]
  omega

/-- Original edges retain their parameter direction. -/
theorem alg511CuffParameterMask_old {Γ : Drawing (OnePoint EuclideanPlane)} (m k : ℕ)
    (edge : Fin (m + (k + k)) ≃ Γ.E) (j : Fin m) :
    alg511CuffParameterMask m k edge (edge (j.castAdd (k + k))).val = false := by
  rw [alg511CuffParameterMask_edge]
  exact decide_eq_false (by simpa only [Fin.val_castAdd] using Nat.not_le_of_lt j.isLt)

/-- Each prescribed inner cuff curve reverses its parameter. -/
theorem alg511CuffParameterMask_inner {Γ : Drawing (OnePoint EuclideanPlane)} (m k : ℕ)
    (edge : Fin (m + (k + k)) ≃ Γ.E) (i : Fin k) :
    alg511CuffParameterMask m k edge (edge ((i.castAdd k).natAdd m)).val = true := by
  rw [alg511CuffParameterMask_edge]
  exact decide_eq_true (by simp only [Fin.val_natAdd, Fin.val_castAdd]; omega)

/-- Each prescribed outer cuff curve reverses its parameter. -/
theorem alg511CuffParameterMask_outer {Γ : Drawing (OnePoint EuclideanPlane)} (m k : ℕ)
    (edge : Fin (m + (k + k)) ≃ Γ.E) (i : Fin k) :
    alg511CuffParameterMask m k edge (edge ((i.natAdd k).natAdd m)).val = true := by
  rw [alg511CuffParameterMask_edge]
  exact decide_eq_true (by simp only [Fin.val_natAdd]; omega)

end GraphMinor.GM06
