module

public import GraphMinor.GM06.Section5ReflectionMap
import GraphMinor.GM06.Section4
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Reflection preserves the prescribed cuff and dual points

For the orientation reversal in VI (5.10), page 134, the reflected
drawing must still have the same prescribed cuff vertices and helix
end sets. The reflection preserves radius and permutes the cuff
vertices by an involution. Its fixed rotation makes the dual indices
reverse by `Fin.rev`, modulo a full angular period.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Reflection fixes the radius, so it preserves membership in the cylinder boundary. -/
theorem section5CylinderReflection_mem_bd (k : ℕ) (p : ClosedCylinder) :
    section5CylinderReflection k p ∈ bd ClosedCylinder ↔ p ∈ bd ClosedCylinder := by
  rw [bd_closedCylinder]
  rfl

/-- Reflection permutes the full prescribed inner-cuff vertex set. -/
theorem section5CylinderReflection_image_M1 {k : ℕ} (hk : 0 < k) :
    section5CylinderReflection k '' cylinderM1 k = cylinderM1 k := by
  apply subset_antisymm
  · rintro p ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨section5ReflectionIndex hk i, (section5CylinderReflection_M1 hk i).symm⟩
  · rintro p ⟨i, rfl⟩
    refine ⟨cylinderM1Point k (section5ReflectionIndex hk i), ⟨_, rfl⟩, ?_⟩
    rw [section5CylinderReflection_M1 hk, section5ReflectionIndex_involutive hk]

/-- Reflection permutes the full prescribed outer-cuff vertex set. -/
theorem section5CylinderReflection_image_M2 {k : ℕ} (hk : 0 < k) :
    section5CylinderReflection k '' cylinderM2 k = cylinderM2 k := by
  apply subset_antisymm
  · rintro p ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨section5ReflectionIndex hk i, (section5CylinderReflection_M2 hk i).symm⟩
  · rintro p ⟨i, rfl⟩
    refine ⟨cylinderM2Point k (section5ReflectionIndex hk i), ⟨_, rfl⟩, ?_⟩
    rw [section5CylinderReflection_M2 hk, section5ReflectionIndex_involutive hk]

private theorem reflection_dual_angle {k : ℕ} (hk : 0 < k) (i : Fin k) :
    Circle.exp (4 * π / k) * (Circle.exp ((2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k))⁻¹ =
      Circle.exp ((2 * (((Fin.rev i).val + 1 : ℕ) : ℝ) + 1) * π / k) := by
  have hn : (Fin.rev i).val + 1 + i.val = k := by
    change k - (i.val + 1) + 1 + i.val = k
    omega
  have hnR : (((Fin.rev i).val + 1 : ℕ) : ℝ) + (i.val : ℝ) = (k : ℝ) := by exact_mod_cast hn
  have hrev : (((Fin.rev i).val + 1 : ℕ) : ℝ) = (k : ℝ) - (i.val : ℝ) := by linarith
  rw [← Circle.exp_neg, ← Circle.exp_add]
  have he : 4 * π / k + -((2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k) =
      (2 * (((Fin.rev i).val + 1 : ℕ) : ℝ) + 1) * π / k - 2 * π := by
    rw [hrev]
    push_cast
    field_simp
    ring
  rw [he, Circle.exp_sub_two_pi]

/-- The inner dual points are preserved under reversal of their indices. -/
theorem section5CylinderReflection_N1 {k : ℕ} (hk : 0 < k) (i : Fin k) :
    section5CylinderReflection k (cylinderN1Point k i) = cylinderN1Point k (Fin.rev i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact reflection_dual_angle hk i

/-- The outer dual points are preserved under the same index reversal. -/
theorem section5CylinderReflection_N2 {k : ℕ} (hk : 0 < k) (i : Fin k) :
    section5CylinderReflection k (cylinderN2Point k i) = cylinderN2Point k (Fin.rev i) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact reflection_dual_angle hk i

end GraphMinor.GM06
