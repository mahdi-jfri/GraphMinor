module

public import GraphMinor.GM06.Alg511CuffParam
public import GraphMinor.GM06.Alg511ReflectionIndices
public import GraphMinor.Compute.GM06Alg511ReflectDrawing
import Mathlib.Tactic

/-!
# Geometric meaning of reflected cuff-marker labels

In the orientation step of VI (5.11), page 134, the prescribed cuff
vertices and the gaps have different index permutations. Reflection
sends gap i to gap k-1-i and reverses its parameter. This follows
by comparing their angular lifts, which differ by one full turn.
The two cuffs obey the same formula because exchanging the radii
commutes with reflection. Thus the computed marker permutation
retains the actual edge and the actual directed end, including the
one-vertex cuff loops.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute Set Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The reflected gap starts at the reflection of its former terminal
vertex. This explains why its index differs from the vertex index. -/
theorem alg511_reflectGapFin_eq_reflect_successor {k : ℕ} (i : Fin k) :
    gm06Alg511ReflectGapFin i = gm06Alg511ReflectFin (finSuccCycle i) := by
  apply Fin.ext
  by_cases hi : i.val + 1 < k
  · simp only [finSuccCycle, hi, dite_true, gm06Alg511ReflectFin]
    rw [ite_eq_right (by omega : ¬ i.val + 1 = 0)]
    dsimp only [gm06Alg511ReflectGapFin]
    omega
  · simp only [finSuccCycle, hi, dite_false, gm06Alg511ReflectFin, ite_true]
    dsimp only [gm06Alg511ReflectGapFin]
    omega

/-- The prescribed inner-gap curve reflects to the reversed curve
of gap k-1-i. The equality holds also at both parameter ends. -/
theorem alg511_reflected_initial_gap {k : ℕ} (i : Fin k) (t : I) :
    section5CylinderReflection k (initialCuffGapCurve k i t) =
      initialCuffGapCurve k (gm06Alg511ReflectGapFin i) (σ t) := by
  have hk : 0 < k := by have := i.isLt; omega
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hj : (gm06Alg511ReflectGapFin i).val + 1 = k - i.val := by
    dsimp only [gm06Alg511ReflectGapFin]
    omega
  have hangle : 2 * ((((gm06Alg511ReflectGapFin i).val + 1 : ℕ) : ℝ) +
      (σ t : ℝ)) * π / k =
      (4 * π / k + -(2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k)) + 2 * π := by
    rw [hj, unitInterval.coe_symm_eq, Nat.cast_sub (Nat.le_of_lt i.isLt)]
    push_cast
    field_simp [hkne]
    ring
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp (4 * π / k) *
        (Circle.exp (2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k))⁻¹ =
      Circle.exp (2 * ((((gm06Alg511ReflectGapFin i).val + 1 : ℕ) : ℝ) +
        (σ t : ℝ)) * π / k)
    rw [← Circle.exp_neg, ← Circle.exp_add, hangle, Circle.exp_add_two_pi]

private theorem reflection_cuffSwap (k : ℕ) (p : ClosedCylinder) :
    section5CylinderReflection k (alg511CuffSwap p) =
      alg511CuffSwap (section5CylinderReflection k p) := by
  apply Subtype.ext
  apply Prod.ext <;> rfl

/-- The same reflected-gap index and reversed parameter describe
the outer cuff. -/
theorem alg511_reflected_outer_gap {k : ℕ} (i : Fin k) (t : I) :
    section5CylinderReflection k (alg511OuterCuffGapCurve k i t) =
      alg511OuterCuffGapCurve k (gm06Alg511ReflectGapFin i) (σ t) := by
  change section5CylinderReflection k (alg511CuffSwap (initialCuffGapCurve k i t)) = _
  rw [reflection_cuffSwap, alg511_reflected_initial_gap]
  rfl

private theorem symm_image_open : σ '' Ioo (0 : I) 1 = Ioo 0 1 := by
  have hσ {t : I} (ht : t ∈ Ioo (0 : I) 1) : σ t ∈ Ioo (0 : I) 1 :=
    ⟨by simpa using unitInterval.strictAnti_symm ht.2,
      by simpa using unitInterval.strictAnti_symm ht.1⟩
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hσ hs
  · intro ht
    exact ⟨σ t, hσ ht, by simp⟩

/-- The reflected inner gap is exactly the corresponding whole
open cuff edge, rather than only a subset of that edge. -/
theorem alg511_reflected_initial_gap_image {k : ℕ} (i : Fin k) :
    section5CylinderReflection k '' (initialCuffGapCurve k i '' Ioo 0 1) =
      initialCuffGapCurve k (gm06Alg511ReflectGapFin i) '' Ioo 0 1 := by
  rw [image_image]
  have hf : (fun t => section5CylinderReflection k (initialCuffGapCurve k i t)) =
      fun t => initialCuffGapCurve k (gm06Alg511ReflectGapFin i) (σ t) :=
    funext (alg511_reflected_initial_gap i)
  rw [hf, ← image_image, symm_image_open]

/-- The reflected outer gap is exactly its corresponding whole
open cuff edge as well. -/
theorem alg511_reflected_outer_gap_image {k : ℕ} (i : Fin k) :
    section5CylinderReflection k '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) =
      alg511OuterCuffGapCurve k (gm06Alg511ReflectGapFin i) '' Ioo 0 1 := by
  rw [image_image]
  have hf : (fun t => section5CylinderReflection k (alg511OuterCuffGapCurve k i t)) =
      fun t => alg511OuterCuffGapCurve k (gm06Alg511ReflectGapFin i) (σ t) :=
    funext (alg511_reflected_outer_gap i)
  rw [hf, ← image_image, symm_image_open]

/-- The computed inner marker has exactly the reflected gap index
and opposite Boolean parameter end. -/
theorem alg511_reflected_inner_dart (m : ℕ) {k : ℕ} (i : Fin k) (b : Bool) :
    gm06Alg511ReflectAugmentedDart m k (2 * (m + i.val) + b.toNat) =
      2 * (m + (gm06Alg511ReflectGapFin i).val) + (!b).toNat := by
  have h := gm06Alg511ReflectAugmentedDart_inner m k i.val b.toNat i.isLt (by cases b <;> decide)
  cases b <;> simpa only [gm06Alg511ReflectGapFin, Bool.toNat_false, Bool.toNat_true,
    Bool.not_false, Bool.not_true] using h

/-- The computed outer marker uses the same geometric gap
permutation after its original-plus-inner edge offset. -/
theorem alg511_reflected_outer_dart (m : ℕ) {k : ℕ} (i : Fin k) (b : Bool) :
    gm06Alg511ReflectAugmentedDart m k (2 * (m + k + i.val) + b.toNat) =
      2 * (m + k + (gm06Alg511ReflectGapFin i).val) + (!b).toNat := by
  have h := gm06Alg511ReflectAugmentedDart_outer m k i.val b.toNat i.isLt (by cases b <;> decide)
  cases b <;> simpa only [gm06Alg511ReflectGapFin, Bool.toNat_false, Bool.toNat_true,
    Bool.not_false, Bool.not_true] using h

/-- Reflection exchanges the two directed ends of every fixed
inner cuff parameter, even when both ends are the same vertex. -/
theorem alg511_reflected_initial_gap_end {k : ℕ} (i : Fin k) (b : Bool) :
    section5CylinderReflection k (initialCuffGapCurve k i (endOf b)) =
      initialCuffGapCurve k (gm06Alg511ReflectGapFin i) (endOf (!b)) := by
  have h := alg511_reflected_initial_gap i (endOf b)
  cases b <;> simpa [endOf] using h

end GraphMinor.GM06
