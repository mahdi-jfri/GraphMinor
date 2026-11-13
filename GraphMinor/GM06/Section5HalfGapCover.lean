module

public import GraphMinor.GM06.Section5InitialCuffBacktrack
public import GraphMinor.GM06.Section5CoverDisc

/-!
# The half-gap prefix above a specified initial copy

The return in VI (5.5), page 131, reverses the initial half-gap
prefix. Lift that prefix so that it ends at the specified copy of
the initial vertex. Its angle decreases linearly by pi divided by k.
The reverse therefore lies in the following half gap in the cover,
with exactly the endpoint angle used by the crossing count.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- Lift the half-gap prefix to any specified initial-vertex copy,
retaining its complete angular interval for VI (5.5), page 132. -/
theorem exists_half_gap_cover_ending_at_initial_copy
    {k : ℕ} (hk : 0 < k) (i : Fin k) (p : CylinderCover)
    (hpRad : p.1.1 = 1) (hp : cylinderCoverProjection p = cylinderM1Point k i) :
    ∃ q : C(unitInterval, CylinderCover), q 1 = p ∧
      (∀ t, cylinderCoverProjection (q t) = initialCuffHalfBacktrackCurve k i t) ∧
      (q 0).2 = p.2 + π / k ∧
      ∀ t, cylinderCoverCoordinates (q t) ∈ ({1} ×ˢ Icc p.2 (p.2 + π / k)) := by
  let q : C(unitInterval, CylinderCover) :=
    ⟨fun t => (⟨1, by norm_num⟩, p.2 + (1 - (t : ℝ)) * π / k), by fun_prop⟩
  have hpAng : Circle.exp p.2 = Circle.exp (2 * ((i.1 + 1 : ℕ) : ℝ) * π / k) :=
    congrArg (fun x : ClosedCylinder => x.1.2) hp
  have hq1 : q 1 = p := by
    apply Prod.ext
    · apply Subtype.ext
      exact hpRad.symm
    · change p.2 + (1 - ((1 : unitInterval) : ℝ)) * π / k = p.2
      norm_num
  refine ⟨q, hq1, ?_, ?_, ?_⟩
  · intro t
    rw [initialCuffHalfBacktrackCurve_apply]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp (p.2 + (1 - (t : ℝ)) * π / k) =
        Circle.exp ((2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - (t : ℝ)) * π / k)
      rw [show (2 * ((i.1 + 1 : ℕ) : ℝ) + 1 - (t : ℝ)) * π / k =
        2 * ((i.1 + 1 : ℕ) : ℝ) * π / k + (1 - (t : ℝ)) * π / k by ring]
      rw [Circle.exp_add, Circle.exp_add, hpAng]
  · change p.2 + (1 - ((0 : unitInterval) : ℝ)) * π / k = p.2 + π / k
    norm_num
  · intro t
    have hscale : (0 : ℝ) ≤ π / k := (div_pos pi_pos (Nat.cast_pos.mpr hk)).le
    refine ⟨rfl, ?_, ?_⟩
    · change p.2 ≤ p.2 + (1 - (t : ℝ)) * π / k
      rw [mul_div_assoc]
      exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr t.2.2) hscale)
    · change p.2 + (1 - (t : ℝ)) * π / k ≤ p.2 + π / k
      rw [mul_div_assoc]
      have hmul := mul_le_of_le_one_left hscale (sub_le_self (1 : ℝ) t.2.1)
      linarith only [hmul]

end GraphMinor.GM06
