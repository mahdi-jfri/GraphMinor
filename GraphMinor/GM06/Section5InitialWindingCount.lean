module

public import GraphMinor.GM06.Section5InitialCrossings

/-!
# Winding and vertex counts for initial-cuff return curves

The auxiliary curve in VI (5.5), page 131, joins two dual points on
the initial cuff. Their lifted angles have odd grid coordinates.
Their difference measures winding, and the intervening linkage
lifts give the vertex-count bound used in the surgery argument.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- For a curve between two initial dual points, the lifted endpoint
gap indices differ by k times its winding, as used for f'' in VI (5.5). -/
theorem initial_cuff_angle_and_winding_int {k : ℕ} {f : Curve ClosedCylinder}
    (hk : 0 < k) (hf0 : f 0 ∈ cylinderN1 k) (hf1 : f 1 ∈ cylinderN1 k) :
    ∃ m₀ m₁ : ℤ,
      cylinderAngleLift f 0 = ((2 * m₀ + 1 : ℤ) : ℝ) * π / (k : ℝ) ∧
      cylinderAngleLift f 1 = ((2 * m₁ + 1 : ℤ) : ℝ) * π / (k : ℝ) ∧
      (k : ℝ) * windingNumber f = ((m₁ - m₀ : ℤ) : ℝ) := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
  rcases hf0 with ⟨j₀, hj₀⟩
  rcases hf1 with ⟨j₁, hj₁⟩
  have hexp0 : Circle.exp (cylinderAngleLift f 0) =
      Circle.exp ((2 * ((j₀.1 + 1 : ℕ) : ℝ) + 1) * π / k) := by
    rw [exp_cylinderAngleLift, ← hj₀]
    rfl
  have hexp1 : Circle.exp (cylinderAngleLift f 1) =
      Circle.exp ((2 * ((j₁.1 + 1 : ℕ) : ℝ) + 1) * π / k) := by
    rw [exp_cylinderAngleLift, ← hj₁]
    rfl
  obtain ⟨n₀, hn₀⟩ := Circle.exp_eq_exp.mp hexp0
  obtain ⟨n₁, hn₁⟩ := Circle.exp_eq_exp.mp hexp1
  let m₀ : ℤ := (j₀.1 + 1 : ℤ) + n₀ * (k : ℤ)
  let m₁ : ℤ := (j₁.1 + 1 : ℤ) + n₁ * (k : ℤ)
  have hm₀ : cylinderAngleLift f 0 = ((2 * m₀ + 1 : ℤ) : ℝ) * π / (k : ℝ) := by
    rw [hn₀]
    dsimp [m₀]
    push_cast
    field_simp [hk_ne]
    ring
  have hm₁ : cylinderAngleLift f 1 = ((2 * m₁ + 1 : ℤ) : ℝ) * π / (k : ℝ) := by
    rw [hn₁]
    dsimp [m₁]
    push_cast
    field_simp [hk_ne]
    ring
  refine ⟨m₀, m₁, hm₀, hm₁, ?_⟩
  unfold windingNumber
  rw [hm₀, hm₁]
  push_cast
  field_simp [hk_ne, h2pi_ne]
  ring


/-- A normal curve between two initial dual points has at least
k times its absolute winding in vertex contacts. This is the return
curve form of the direct crossing count used in VI (5.5), page 132. -/
theorem abs_winding_initial_cuff_le_curveL
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (hk : 0 < k) (L : CylinderLinkage k G) (hθ : L.HasTheta θ)
    (f : Curve ClosedCylinder) (hf : IsNormalCurve G f)
    (hf0 : f 0 ∈ cylinderN1 k) (hf1 : f 1 ∈ cylinderN1 k)
    (hfin : (curveVertexHits G f).Finite) :
    (k : ℝ) * |windingNumber f| ≤ (curveL G f : ℝ) := by
  obtain ⟨m₀, m₁, hm₀, hm₁, hw⟩ := initial_cuff_angle_and_winding_int hk hf0 hf1
  have hr0 : (f 0).1.1 = 1 := by
    obtain ⟨i, hi⟩ := hf0
    rw [← hi]
    rfl
  have hr1 : (f 1).1.1 = 1 := by
    obtain ⟨i, hi⟩ := hf1
    rw [← hi]
    rfl
  have hcount := natAbs_initial_gap_difference_le_curveL hk L hθ f hf hr0 hr1 hfin m₀ m₁ hm₀ hm₁
  have hcount' : ((m₁ - m₀).natAbs : ℝ) ≤ (curveL G f : ℝ) := Nat.cast_le.mpr hcount
  have habs : |((m₁ - m₀ : ℤ) : ℝ)| = ((m₁ - m₀).natAbs : ℝ) := by
    rw [← Int.cast_abs, Nat.cast_natAbs]
  rw [← habs, ← hw, abs_mul, abs_of_pos (Nat.cast_pos.mpr hk)] at hcount'
  exact hcount'

end GraphMinor.GM06
