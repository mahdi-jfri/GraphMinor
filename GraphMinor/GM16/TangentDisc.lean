module

public import GraphMinor.Surface.DiscArcs
import GraphMinor.GM11.GlueDiscs
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Isometry

/-!
# A small disc tangent at a boundary vertex

To draw the loops of a small torso in XVI (1.3), page 51, we need a
closed disc inside the remaining face that meets its boundary at just
one prescribed vertex. In a unit-disc chart, take a smaller round disc
internally tangent to the unit circle. Its radius can be chosen small
enough to lie in any prescribed neighborhood of that vertex.
-/

public section
namespace GraphMinor.GM16
open Set Topology Metric Surface
universe w

/-- A boundary point of a closed disc has arbitrarily small closed
discs inside it that touch the original boundary only at that point. -/
theorem exists_tangent_disc
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {D U : Set S} (hD : IsClosedDisc D) (hU : IsOpen U)
    {v : S} (hvD : v ∈ discBd D) (hvU : v ∈ U) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ D ∧ E ⊆ U ∧
      v ∈ discBd E ∧ E ∩ discBd D = {v} := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  let p : ℂ := h v
  have hp : p ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hvD
  have hpB : p ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hp
  have hgp : g p = v := c.gh (discBd_subset D hvD)
  have hnormp : ‖p‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hp
  have hpre : g ⁻¹' U ∈ 𝓝[closedBall (0 : ℂ) 1] p :=
    (c.gc p hpB) (by rw [hgp]; exact hU.mem_nhds hvU)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let r : ℝ := min (δ / 4) (1 / 2)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hrδ : 2 * r < δ := by have := min_le_left (δ / 4) (1 / 2); dsimp [r]; linarith
  let f : ℂ → ℂ := fun z => ((1 - r : ℝ) : ℂ) * p + (r : ℂ) * z
  have hf : Continuous f := by fun_prop
  have hfp : f p = p := by dsimp [f]; push_cast; ring
  have hfB : ∀ z ∈ closedBall (0 : ℂ) 1, f z ∈ closedBall (0 : ℂ) 1 := by
    intro z hz
    simpa only [f, Complex.real_smul] using
      (convex_closedBall (0 : ℂ) 1 hpB hz (by linarith : 0 ≤ 1 - r)
        (le_of_lt hr) (by ring : 1 - r + r = 1))
  have hfInj : Function.Injective f := by
    intro z z' hzz'
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    exact mul_left_cancel₀ hrC (add_left_cancel hzz')
  have hfSphere : ∀ z ∈ closedBall (0 : ℂ) 1, f z ∈ sphere (0 : ℂ) 1 → z = p := by
    intro z hz hfs
    by_contra hzp
    have hlt := strictConvex_closedBall ℝ (0 : ℂ) 1 hpB hz (fun heq => hzp heq.symm)
      (by linarith : 0 < 1 - r) hr (by ring : 1 - r + r = 1)
    rw [interior_closedBall _ one_ne_zero] at hlt
    have hNormLt : ‖f z‖ < 1 := by simpa only [f, Complex.real_smul, mem_ball_zero_iff] using hlt
    have hNormEq : ‖f z‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hfs
    linarith
  have hfNear : ∀ z ∈ closedBall (0 : ℂ) 1, dist (f z) p < δ := by
    intro z hz
    have hnormz : ‖z‖ ≤ 1 := by simpa only [mem_closedBall_zero_iff] using hz
    have hsub : ‖z - p‖ ≤ 2 := (norm_sub_le z p).trans (by rw [hnormp]; linarith)
    have heq : f z - p = (r : ℂ) * (z - p) := by dsimp [f]; push_cast; ring
    rw [dist_eq_norm, heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hsub (le_of_lt hr)).trans_lt (by simpa only [mul_comm] using hrδ)
  let k : ℂ → S := g ∘ f
  have hk : ContinuousOn k (closedBall (0 : ℂ) 1) := c.gc.comp hf.continuousOn hfB
  have hkInj : InjOn k (closedBall (0 : ℂ) 1) := by
    intro z hz z' hz' hzz'
    apply hfInj
    have heq := congrArg h hzz'
    simpa only [k, Function.comp_apply, c.hg (hfB z hz), c.hg (hfB z' hz')] using heq
  obtain ⟨hE, hBdE⟩ := GM11.isClosedDisc_image isClosedDisc_closedBall.1 hk hkInj
  refine ⟨k '' closedBall (0 : ℂ) 1, hE, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact c.gm (hfB z hz)
  · rintro _ ⟨z, hz, rfl⟩
    exact hδU ⟨hfNear z hz, hfB z hz⟩
  · rw [hBdE, isClosedDisc_closedBall.2]
    exact ⟨p, hp, by simp only [k, Function.comp_apply, hfp, hgp]⟩
  · ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxbd⟩
      have hfs : f z ∈ sphere (0 : ℂ) 1 := by
        have him : h (k z) ∈ h '' discBd D := mem_image_of_mem h hxbd
        rw [c.bd] at him
        simpa only [k, Function.comp_apply, c.hg (hfB z hz)] using him
      have hzp := hfSphere z hz hfs
      simp only [hzp, k, Function.comp_apply, hfp, hgp, mem_singleton_iff]
    · rintro rfl
      exact ⟨⟨p, hpB, by simp only [k, Function.comp_apply, hfp, hgp]⟩, hvD⟩

end GraphMinor.GM16
