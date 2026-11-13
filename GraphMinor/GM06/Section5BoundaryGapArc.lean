module

public import GraphMinor.GM06.Section5BoundaryGap

/-!
# The initial cuff gap as an injective boundary arc

For the boundary-side construction in VI (5.1), page 129, the
closed initial cuff gap is an arc when there are at least two paths.
Its angular interval has length at most pi, so angular projection is
injective there. The existing endpoint formulas then give its
parametrization from sᵢ to sᵢ₊₁.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- The initial gap curve is injective when there are at least two
linkage indices. -/
theorem initialCuffGapCurve_injective {k : ℕ} (hk : 1 < k) (i : Fin k) :
    Function.Injective (initialCuffGapCurve k i) := by
  let a : ℝ := 2 * ((i.val + 1 : ℕ) : ℝ) * π / k
  let d : ℝ := 2 * π / k
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < d := div_pos (mul_pos two_pos pi_pos) hkR
  have hdpi : d ≤ π := by
    apply (div_le_iff₀ hkR).mpr
    nlinarith only [hk2, pi_pos]
  have hangle (u : unitInterval) :
      2 * (((i.val + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k = a + d * u := by
    dsimp only [a, d]
    ring
  have hbound (u : unitInterval) : a + d * u ∈ Icc a (a + π) := by
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg hd.le u.2.1)
    · have hmul : d * (u : ℝ) ≤ d := by simpa using mul_le_mul_of_nonneg_left u.2.2 hd.le
      linarith only [hmul, hdpi]
  intro s t hst
  have hh := congrArg (fun p : ClosedCylinder => p.1.2) hst
  change Circle.exp (2 * (((i.val + 1 : ℕ) : ℝ) + (s : ℝ)) * π / k) =
    Circle.exp (2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k) at hh
  rw [hangle, hangle] at hh
  have heq := Circle.exp_injOn_Icc (by linarith only [pi_pos] : (a + π) - a < 2 * π)
    (hbound s) (hbound t) hh
  exact Subtype.ext (mul_left_cancel₀ hd.ne' (add_left_cancel heq))

/-- The initial gap is parametrized injectively from sᵢ to sᵢ₊₁,
as used to select the disc side in VI (5.1). -/
theorem initialCuffGapCurve_parametrizes
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    ParametrizesSet (initialCuffGapCurve k i) (range (initialCuffGapCurve k i))
      (cylinderM1Point k i) (cylinderM1Point k (finSuccCycle i)) := by
  have hp := initialCuffGapCurve_props hG i
  exact ⟨initialCuffGapCurve_injective hk i, rfl, hp.1, hp.2.1⟩

end GraphMinor.GM06
