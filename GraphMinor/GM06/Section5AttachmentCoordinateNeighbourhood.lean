module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.Linarith

/-!
# Coordinate neighbourhoods avoiding the attachment antipode

For the attachment-visit count in VI (5.5), page 130, shrink the
disc-coordinate neighbourhood of the attachment so its inverse
image stays in a prescribed spatial neighbourhood and avoids the
opposite angle. Continuity of the inverse chart gives this shrinkage.
The attachment itself differs from its antipode by half a turn.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric Filter GraphMinor.Surface

/-- Near an attachment, disc coordinates stay in any prescribed
open neighbourhood and avoid the antipode of its angular value. -/
theorem exists_attachment_coordinate_neighbourhood
    {D : Set ClosedCylinder} {h : ClosedCylinder → ℂ} {j : ℂ → ClosedCylinder}
    (c : IsChart D h j) {s : ClosedCylinder} (hs : s ∈ D)
    {U : Set ClosedCylinder} (hU : IsOpen U) (hsU : s ∈ U)
    (θ : ℝ) (hθ : Circle.exp θ = s.1.2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ closedBall (0 : ℂ) 1,
      dist w (h s) < δ → j w ∈ U ∧ (j w).1.2 ≠ Circle.exp (θ + Real.pi) := by
  have hne : Circle.exp θ ≠ Circle.exp (θ + Real.pi) := by
    intro he
    have hEq := Circle.exp_injOn_Icc (a := θ) (b := θ + Real.pi)
      (by linarith [Real.pi_pos])
      (show θ ∈ Icc θ (θ + Real.pi) from ⟨le_rfl, by linarith [Real.pi_pos]⟩)
      (show θ + Real.pi ∈ Icc θ (θ + Real.pi) from ⟨by linarith [Real.pi_pos], le_rfl⟩) he
    linarith [Real.pi_pos]
  let V : Set ClosedCylinder := {x | x.1.2 ≠ Circle.exp (θ + Real.pi)}
  have hV : IsOpen V := isClosed_singleton.isOpen_compl.preimage
    (continuous_snd.comp continuous_subtype_val)
  have hsV : s ∈ V := by change s.1.2 ≠ _; rw [← hθ]; exact hne
  have hnear : Tendsto j (𝓝[closedBall (0 : ℂ) 1] h s) (𝓝 s) := by
    have hcont := c.gc (h s) (c.hm hs)
    change Tendsto j (𝓝[closedBall (0 : ℂ) 1] h s) (𝓝 (j (h s))) at hcont
    rwa [c.gh hs] at hcont
  have hpre : j ⁻¹' (U ∩ V) ∈ 𝓝[closedBall (0 : ℂ) 1] h s :=
    hnear ((hU.inter hV).mem_nhds ⟨hsU, hsV⟩)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  exact ⟨δ, hδ, fun w hw hdist => hsub ⟨hdist, hw⟩⟩

end GraphMinor.GM06
