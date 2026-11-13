module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Keeping a detoured attachment in its original angular sheet

For the attachment-visit count in VI (5.5), page 130, a lifted
homotopy path that avoids the antipode cannot leave the angular
interval centred at the old attachment lift. The intermediate
value theorem excludes crossing either end of that interval.
If the projected endpoint is the attachment again, injectivity
of the exponential on one turn identifies its lift exactly.
-/

public section
namespace GraphMinor.GM06
open Set

/-- A lifted angle starting within half a turn of an attachment
and missing its antipode stays within that same angular interval. -/
theorem lifted_angle_stays_in_attachment_sheet
    (a : C(unitInterval, ℝ)) (θ : ℝ) (h0 : |a 0 - θ| < Real.pi)
    (hmiss : ∀ t, Circle.exp (a t) ≠ Circle.exp (θ + Real.pi)) :
    ∀ t, a t ∈ Ioo (θ - Real.pi) (θ + Real.pi) := by
  have hstart := abs_lt.mp h0
  intro t
  constructor
  · by_contra hlo
    have hlow : a t ≤ θ - Real.pi := le_of_not_gt hlo
    have hbetween : θ - Real.pi ∈ Icc (a t) (a 0) :=
      ⟨hlow, by linarith only [hstart.1]⟩
    obtain ⟨u, hu⟩ := intermediate_value_univ t 0 a.continuous hbetween
    apply hmiss u
    rw [hu]
    have he := Circle.exp_sub_two_pi (θ + Real.pi)
    convert he using 1; congr 1; ring
  · by_contra hhi
    have hhigh : θ + Real.pi ≤ a t := le_of_not_gt hhi
    have hbetween : θ + Real.pi ∈ Icc (a 0) (a t) :=
      ⟨by linarith only [hstart.2], hhigh⟩
    obtain ⟨u, hu⟩ := intermediate_value_univ 0 t a.continuous hbetween
    exact hmiss u (congrArg Circle.exp hu)

/-- Returning to the attachment while missing its antipode returns
to the original angular lift, rather than another deck translate. -/
theorem lifted_attachment_endpoint_eq
    (a : C(unitInterval, ℝ)) (θ : ℝ) (h0 : |a 0 - θ| < Real.pi)
    (hmiss : ∀ t, Circle.exp (a t) ≠ Circle.exp (θ + Real.pi))
    (h1 : Circle.exp (a 1) = Circle.exp θ) : a 1 = θ := by
  have hclose := lifted_angle_stays_in_attachment_sheet a θ h0 hmiss 1
  apply Circle.exp_injOn_Ico (a := θ - Real.pi) (b := θ + Real.pi) (by linarith)
    ⟨hclose.1.le, hclose.2⟩ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ h1

end GraphMinor.GM06
