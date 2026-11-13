module

public import Mathlib.Analysis.Complex.Basic
import GraphMinor.GM06.Section5StraightFibreRetraction
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Confining an attachment fibre near its boundary vertex

For the finite attachment-visit argument in VI (5.5), page 130,
a simplified curve leaves every nonempty open set partly empty.
Choose the retraction centre outside that curve and arbitrarily
near its boundary attachment. The straight-fibre property places
the entire attachment fibre inside the same small ball.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric

/-- An omitted centre can be chosen so that the fibre of a disc
retraction over a specified boundary vertex is arbitrarily small. -/
theorem exists_disc_retraction_with_small_attachment_fibre
    {K : Set ℂ} (hK : interior K = ∅) {s : ℂ} (hs : ‖s‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℂ, ‖a‖ < 1 ∧ a ∉ K ∧
      ∃ r : ℂ → ℂ, ContinuousOn r (closedBall 0 1 \ {a}) ∧
        (∀ w ∈ closedBall (0 : ℂ) 1 \ {a}, ‖r w‖ = 1) ∧
        (∀ w : ℂ, ‖w‖ = 1 → r w = w) ∧
        ∀ w ∈ closedBall (0 : ℂ) 1 \ {a}, r w = s → dist w s < ε := by
  have hscl : s ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact mem_closedBall_zero_iff.mpr hs.le
  obtain ⟨z, hzball, hzunit⟩ := mem_closure_iff.mp hscl (ball s ε) isOpen_ball (mem_ball_self hε)
  let U := ball s ε ∩ ball (0 : ℂ) 1
  have hU : IsOpen U := isOpen_ball.inter isOpen_ball
  have hnot : ¬ U ⊆ K := by
    intro hsub
    have hempty := interior_maximal hsub hU
    rw [hK] at hempty
    exact hempty ⟨hzball, hzunit⟩
  obtain ⟨a, haU, haK⟩ := not_subset.mp hnot
  have ha : ‖a‖ < 1 := mem_ball_zero_iff.mp haU.2
  obtain ⟨r, hc, hn, hfix, hfibre⟩ := exists_disc_retraction_with_straight_fibres ha
  refine ⟨a, ha, haK, r, hc, hn, hfix, ?_⟩
  intro w hw he
  have hwseg := hfibre w hw s he
  exact (convex_ball s ε).segment_subset haU.1 (mem_ball_self hε) hwseg

end GraphMinor.GM06
