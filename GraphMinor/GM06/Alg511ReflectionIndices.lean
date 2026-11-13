module

public import GraphMinor.Compute.GM06Alg511ReflectCuff
public import GraphMinor.GM06.Section5ReflectionMap
import Mathlib.Tactic

/-!
# Geometric interpretation of the computed reflected cuff rows

The orientation reversal in VI (5.11), page 134, uses the reflection
already proved for Section 5. Its prescribed cuff permutation is the
finite permutation computed by the RAM cuff-reordering loop. Hence
those rows keep the canonical cuff indices after actual reflection.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Real

/-- The computable cuff permutation is exactly the prescribed-index
permutation of the geometric Section 5 reflection. -/
theorem alg511_reflectFin_eq_geometric {k : ℕ} (hk : 0 < k) (i : Fin k) :
    gm06Alg511ReflectFin i = section5ReflectionIndex hk i := by
  apply Fin.ext
  rw [show (section5ReflectionIndex hk i).val = ((1 - (i.val : ℤ) - 1) % (k : ℤ)).toNat from
    modIdx_val k hk _]
  rw [show 1 - (i.val : ℤ) - 1 = -(i.val : ℤ) by ring]
  by_cases hi : i.val = 0
  · simp [gm06Alg511ReflectFin, hi]
  · have hmod : (-(i.val : ℤ)) % (k : ℤ) = (k : ℤ) - (i.val : ℤ) := by
      have hshift : ((k : ℤ) - (i.val : ℤ)) % (k : ℤ) = (-(i.val : ℤ)) % (k : ℤ) := by
        simp [sub_eq_add_neg]
      rw [← hshift]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod]
    have hsub : (k : ℤ) - (i.val : ℤ) = ((k - i.val : ℕ) : ℤ) := by omega
    rw [hsub]
    simp [gm06Alg511ReflectFin, hi]

/-- Reflection maps prescribed inner points according to the
computed finite cuff permutation. -/
theorem alg511_reflection_M1 {k : ℕ} (hk : 0 < k) (i : Fin k) :
    section5CylinderReflection k (cylinderM1Point k i) =
      cylinderM1Point k (gm06Alg511ReflectFin i) := by
  rw [alg511_reflectFin_eq_geometric hk]
  exact section5CylinderReflection_M1 hk i

/-- Reflection maps prescribed outer points by that same computed
permutation. -/
theorem alg511_reflection_M2 {k : ℕ} (hk : 0 < k) (i : Fin k) :
    section5CylinderReflection k (cylinderM2Point k i) =
      cylinderM2Point k (gm06Alg511ReflectFin i) := by
  rw [alg511_reflectFin_eq_geometric hk]
  exact section5CylinderReflection_M2 hk i

/-- The canonical angle after reflection differs from the reflected
reference by one whole turn exactly at a nonzero cuff index. -/
theorem alg511_reflected_cuff_reference {k : ℕ} (hk : 0 < k) (i : Fin k) :
    2 * (((gm06Alg511ReflectFin i).val + 1 : ℕ) : ℝ) * π / k =
      4 * π / k - 2 * ((i.val + 1 : ℕ) : ℝ) * π / k +
        2 * π * (if i.val = 0 then (0 : ℝ) else 1) := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  by_cases hi : i.val = 0
  · simp only [gm06Alg511ReflectFin, hi, ite_true, Nat.cast_one,
      Nat.zero_add, mul_zero, add_zero]
    ring
  · simp only [gm06Alg511ReflectFin, hi, ite_false, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (Nat.le_of_lt i.isLt), mul_one]
    field_simp [hkne]
    ring

end GraphMinor.GM06
