module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5ReflectionLinkage
import GraphMinor.GM06.Section5ReflectionHelix
import GraphMinor.GM06.Section5TightHelix
import Mathlib.Tactic.Linarith

/-!
# A tight lower helix at a minimum feasible winding

The proof of VI (5.10), page 134, reverses the plane orientation
at the minimum feasible winding. Its negative is a maximum in the
reflected drawing, so (5.3) supplies an upper tight helix there.
Reflect that helix back. Winding changes sign and its vertex count
stays unchanged, giving the required tight lower expression.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The orientation-reversal step in the proof of VI (5.10),
page 134: a minimum feasible winding is attained by a lower helix expression. -/
theorem exists_tight_lower_helix_of_minimum
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    {lo : ℝ} (hlo : IsThetaFeasible k G lo)
    (hmin : ∀ θ : ℝ, IsThetaFeasible k G θ → lo ≤ θ) :
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧
      windingNumber f - (k : ℝ)⁻¹ * (curveL G f : ℝ) = lo := by
  have hR := isCylinderSection5Drawing_reflected hG
  have hloR := isThetaFeasible_reflected_of_feasible hG.1 hlo
  have hpos : 0 < 1 / (k : ℝ) := div_pos zero_lt_one (Nat.cast_pos.mpr hG.1)
  have hnext : ¬ IsThetaFeasible k (section5ReflectedDrawing k G) (-lo + 1 / (k : ℝ)) := by
    intro hfeas
    have hback := isThetaFeasible_reflected_of_feasible hG.1 hfeas
    rw [section5ReflectedDrawing_involutive] at hback
    have hh := hmin _ hback
    linarith
  obtain ⟨f, hf, hφ⟩ := theorem_5_3_proof k (section5ReflectedDrawing k G) (-lo) hR hloR hnext
  have hg := isHelix_section5ReflectedCurve hG.1 f hf
  rw [section5ReflectedDrawing_involutive] at hg
  have he := reflected_lower_eq_neg_curvePhi k (section5ReflectedDrawing k G) f
  rw [section5ReflectedDrawing_involutive, hφ, neg_neg] at he
  exact ⟨section5ReflectedCurve k f, hg, he⟩

end GraphMinor.GM06
