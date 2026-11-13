module

public import Mathlib.Analysis.Complex.Basic
import GraphMinor.Surface.Schoenflies
import GraphMinor.Surface.InvarianceOfDomain

/-!
# Radial coordinates for a disc retraction

The attachment-visit count in VI (5.5), page 130, uses a retraction
whose fibre over an attachment lies on a short straight segment.
The map `z + (1 - norm z) * c` sends the disc centre to `c`, fixes
its boundary, and sends every radius to the straight segment from
`c` to its boundary endpoint. Its coordinate formula is retained
alongside the continuous bijection for use in the fibre calculation.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

/-- A disc push with its radial formula retained, so that the
inverse radial retraction has straight-segment boundary fibres. -/
theorem exists_radial_disc_push {c : ℂ} (hc : ‖c‖ < 1) :
    ∃ θ : ℂ → ℂ, Continuous θ ∧ BijOn θ (closedBall 0 1) (closedBall 0 1) ∧ θ 0 = c ∧
      (∀ z ∈ sphere (0 : ℂ) 1, θ z = z) ∧
      ∀ z : ℂ, θ z = z + ((1 - ‖z‖ : ℝ) : ℂ) * c := by
  let θ : ℂ → ℂ := fun z => z + ((1 - ‖z‖ : ℝ) : ℂ) * c
  have hθc : Continuous θ := by fun_prop
  have hnorm : ∀ z, ‖z‖ ≤ 1 → ‖θ z‖ ≤ ‖z‖ + (1 - ‖z‖) * ‖c‖ := fun z hz => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hinj : InjOn θ univ := by
    intro z _ z' _ h
    by_contra hne
    have h1 : z - z' = ((‖z‖ - ‖z'‖ : ℝ) : ℂ) * c := by
      have : z + ((1 - ‖z‖ : ℝ) : ℂ) * c = z' + ((1 - ‖z'‖ : ℝ) : ℂ) * c := h
      push_cast at this ⊢
      linear_combination this
    have h2 : ‖z - z'‖ = |‖z‖ - ‖z'‖| * ‖c‖ := by
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 : |‖z‖ - ‖z'‖| ≤ ‖z - z'‖ := abs_norm_sub_norm_le z z'
    have h4 : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h5 : |‖z‖ - ‖z'‖| * ‖c‖ ≤ ‖z - z'‖ * ‖c‖ :=
      mul_le_mul_of_nonneg_right h3 (norm_nonneg c)
    nlinarith
  have hfix : ∀ z ∈ sphere (0 : ℂ) 1, θ z = z := fun z hz => by
    have : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    simp [θ, this]
  have hmaps : MapsTo θ (closedBall 0 1) (closedBall 0 1) := by
    intro z hz
    have hz' := mem_closedBall_zero_iff.mp hz
    refine mem_closedBall_zero_iff.mpr ((hnorm z hz').trans ?_)
    nlinarith [norm_nonneg c]
  have hopen : MapsTo θ (ball 0 1) (ball 0 1) := by
    intro z hz
    have hz' := mem_ball_zero_iff.mp hz
    refine mem_ball_zero_iff.mpr (lt_of_le_of_lt (hnorm z hz'.le) ?_)
    nlinarith [norm_nonneg c]
  have hzero : θ 0 = c := by simp [θ]
  refine ⟨θ, hθc, ⟨hmaps, hinj.mono (subset_univ _), ?_⟩, hzero, hfix, fun _ => rfl⟩
  have hU : IsOpen (θ '' ball 0 1) :=
    isOpen_image_of_injOn isOpen_ball hθc.continuousOn (hinj.mono (subset_univ _))
  have hclosed : IsClosed (θ '' closedBall 0 1) :=
    ((isCompact_closedBall (0 : ℂ) 1).image hθc).isClosed
  have hball : ball (0 : ℂ) 1 ⊆ θ '' ball 0 1 := by
    refine (convex_ball (0 : ℂ) 1).isPreconnected.subset_of_closure_inter_subset hU
      ⟨c, mem_ball_zero_iff.mpr hc, 0, by simp, hzero⟩ ?_
    rintro y ⟨hy1, hy2⟩
    have hy3 : y ∈ θ '' closedBall 0 1 :=
      hclosed.closure_subset_iff.mpr (image_mono ball_subset_closedBall) hy1
    obtain ⟨z, hz, rfl⟩ := hy3
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz) with h | h
    · exact ⟨z, mem_ball_zero_iff.mpr h, rfl⟩
    · have hzs : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr h
      rw [hfix z hzs] at hy2
      exact absurd h (mem_ball_zero_iff.mp hy2).ne
  intro y hy
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hy) with h | h
  · obtain ⟨z, hz, rfl⟩ := hball (mem_ball_zero_iff.mpr h)
    exact ⟨z, ball_subset_closedBall hz, rfl⟩
  · exact ⟨y, hy, hfix y (mem_sphere_zero_iff_norm.mpr h)⟩


end GraphMinor.GM06
