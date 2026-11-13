module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Winding
public import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section5Red

/-!
# Reversing the orientation of the cylinder

The sufficiency proof of VI (5.10), page 134, reverses the
orientation of the plane to obtain a tight lower helix from (5.3).
Use complex conjugation followed by a fixed rotation. This is an
involution, keeps the two cuffs, and negates every curve winding.
The rotation makes reversal of the dual-point indices particularly simple.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- A plane reflection followed by a rotation, restricted to the cylinder. -/
@[expose] noncomputable def section5CylinderReflection (k : ℕ) : ClosedCylinder ≃ₜ ClosedCylinder where
  toFun p := ⟨(p.1.1, Circle.exp (4 * π / k) * p.1.2⁻¹), p.2⟩
  invFun p := ⟨(p.1.1, Circle.exp (4 * π / k) * p.1.2⁻¹), p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp (4 * π / k) * (Circle.exp (4 * π / k) * p.1.2⁻¹)⁻¹ = p.1.2
      rw [mul_inv_rev, inv_inv]
      calc Circle.exp (4 * π / k) * (p.1.2 * (Circle.exp (4 * π / k))⁻¹) =
          p.1.2 * (Circle.exp (4 * π / k) * (Circle.exp (4 * π / k))⁻¹) := by ac_rfl
           _ = p.1.2 := by rw [mul_inv_cancel, mul_one]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp (4 * π / k) * (Circle.exp (4 * π / k) * p.1.2⁻¹)⁻¹ = p.1.2
      rw [mul_inv_rev, inv_inv]
      calc Circle.exp (4 * π / k) * (p.1.2 * (Circle.exp (4 * π / k))⁻¹) =
          p.1.2 * (Circle.exp (4 * π / k) * (Circle.exp (4 * π / k))⁻¹) := by ac_rfl
           _ = p.1.2 := by rw [mul_inv_cancel, mul_one]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Applying the reflection twice fixes each cylinder point. -/
theorem section5CylinderReflection_involutive (k : ℕ) :
    Function.Involutive (section5CylinderReflection k) :=
  (section5CylinderReflection k).left_inv

/-- Reflection of a cylinder curve in the orientation-reversing plane map. -/
@[expose] noncomputable def section5ReflectedCurve (k : ℕ) (f : Curve ClosedCylinder) : Curve ClosedCylinder :=
  ⟨fun t => section5CylinderReflection k (f t), (section5CylinderReflection k).continuous.comp f.continuous⟩

/-- Reversing the plane orientation negates the winding number. -/
theorem windingNumber_section5ReflectedCurve (k : ℕ) (f : Curve ClosedCylinder) :
    windingNumber (section5ReflectedCurve k f) = - windingNumber f := by
  let a : C(unitInterval, ℝ) := ContinuousMap.const _ (4 * π / k) - cylinderAngleLift f
  have ha (t) : Circle.exp (a t) = (section5ReflectedCurve k f t).1.2 := by
    change Circle.exp (4 * π / k - cylinderAngleLift f t) =
      Circle.exp (4 * π / k) * (f t).1.2⁻¹
    rw [Circle.exp_sub, exp_cylinderAngleLift, div_eq_mul_inv]
  rw [windingNumber_eq_of_exp_lift a ha]
  change ((4 * π / k - cylinderAngleLift f 1) - (4 * π / k - cylinderAngleLift f 0)) / (2 * π) = _
  unfold windingNumber
  ring

/-- The index of a prescribed cuff vertex after reflection. -/
@[expose] noncomputable def section5ReflectionIndex {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  modIdx k hk (1 - (i.val : ℤ))

/-- Reflection permutes the prescribed inner-cuff vertices. -/
theorem section5CylinderReflection_M1 {k : ℕ} (hk : 0 < k) (i : Fin k) :
    section5CylinderReflection k (cylinderM1Point k i) =
      cylinderM1Point k (section5ReflectionIndex hk i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp (4 * π / k) * (Circle.exp (2 * ((i.val + 1 : ℕ) : ℝ) * π / k))⁻¹ = _
    rw [← Circle.exp_neg, ← Circle.exp_add]
    have he : 4 * π / k + -(2 * ((i.val + 1 : ℕ) : ℝ) * π / k) =
        2 * ((1 - (i.val : ℤ) : ℤ) : ℝ) * π / k := by push_cast; ring
    rw [he]
    exact exp_two_mul_int_div_eq_cylinderM1Point hk _

/-- Reflection permutes the prescribed outer-cuff vertices by the same index map. -/
theorem section5CylinderReflection_M2 {k : ℕ} (hk : 0 < k) (i : Fin k) :
    section5CylinderReflection k (cylinderM2Point k i) =
      cylinderM2Point k (section5ReflectionIndex hk i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (section5CylinderReflection k (cylinderM1Point k i)).1.2 =
      (cylinderM1Point k (section5ReflectionIndex hk i)).1.2
    exact congrArg (fun p : ClosedCylinder => p.1.2) (section5CylinderReflection_M1 hk i)

/-- The induced permutation of prescribed cuff vertices is an involution. -/
theorem section5ReflectionIndex_involutive {k : ℕ} (hk : 0 < k) :
    Function.Involutive (section5ReflectionIndex hk) := by
  intro i
  apply cylinderM1Point_injective hk
  have he := congrArg (section5CylinderReflection k) (section5CylinderReflection_M1 hk i)
  rw [section5CylinderReflection_involutive k, section5CylinderReflection_M1 hk] at he
  exact he.symm

end GraphMinor.GM06
