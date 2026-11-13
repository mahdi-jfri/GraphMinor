module

public import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.ArcTools
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Isometry

/-!
# A chord in a closed disc

For the drawing of the small society torsos in XVI (1.3), page 51,
we join two boundary points by a chord through the interior. In a disc
chart this is the straight segment between two points of the unit circle.
Strict convexity keeps every other point of the segment off the circle.
-/

public section
namespace GraphMinor.GM16
open Set Topology Metric Surface
local notation "𝕀" => unitInterval
universe w
variable {X : Type w} [TopologicalSpace X] [T2Space X]

/-- Two points of the boundary of a closed disc are joined by an arc through the interior. -/
theorem exists_disc_chord {Δ : Set X} (hΔ : IsClosedDisc Δ) {a b : X} (ha : a ∈ discBd Δ)
    (hb : b ∈ discBd Δ) (hab : a ≠ b) :
    ∃ F, IsLineWithEnds F a b ∧ F ⊆ Δ ∧ F ∩ discBd Δ = {a, b} := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hbdΔ : discBd Δ ⊆ Δ := discBd_subset Δ
  have hsph : ∀ x ∈ discBd Δ, h x ∈ sphere (0 : ℂ) 1 := fun x hx => c.bd ▸ mem_image_of_mem h hx
  set p := h a with hp
  set q := h b with hq
  have hpq : p ≠ q := fun he => hab (by rw [← c.gh (hbdΔ ha), ← c.gh (hbdΔ hb), ← hp, ← hq, he])
  let z : 𝕀 → ℂ := fun t => ((1 - t.1 : ℝ) : ℂ) * p + ((t.1 : ℝ) : ℂ) * q
  have hzc : Continuous z := by
    have h1 : Continuous fun t : 𝕀 => ((t.1 : ℝ) : ℂ) := by fun_prop
    have h2 : Continuous fun t : 𝕀 => ((1 - t.1 : ℝ) : ℂ) := by fun_prop
    exact (h2.mul continuous_const).add (h1.mul continuous_const)
  have hzb : ∀ t, z t ∈ closedBall (0 : ℂ) 1 := fun t => by
    have h1 := (convex_closedBall (0 : ℂ) 1) (sphere_subset_closedBall (hsph a ha))
      (sphere_subset_closedBall (hsph b hb)) (a := 1 - t.1) (b := t.1) (by linarith [t.2.2]) t.2.1 (by ring)
    simpa [z, Complex.real_smul] using h1
  have hzi : Function.Injective z := fun s t he => by
    have h1 : ((t.1 - s.1 : ℝ) : ℂ) * (q - p) = 0 := by
      simp only [z] at he
      push_cast at he ⊢
      linear_combination -he
    rcases mul_eq_zero.mp h1 with h2 | h2
    · have h3 : t.1 - s.1 = 0 := by exact_mod_cast h2
      exact Subtype.ext (by linarith)
    · exact absurd (sub_eq_zero.mp h2).symm hpq
  have hz0 : z 0 = p := by simp [z]
  have hz1 : z 1 = q := by simp [z]
  have harc : IsArcMap (g ∘ z) := ⟨c.gc.comp_continuous hzc hzb, fun s t he => hzi (by
    have := congrArg h he
    rwa [Function.comp_apply, Function.comp_apply, c.hg (hzb s), c.hg (hzb t)] at this)⟩
  have hl := harc.isLineWithEnds
  have hg0 : (g ∘ z) 0 = a := by rw [Function.comp_apply, hz0, hp, c.gh (hbdΔ ha)]
  have hg1 : (g ∘ z) 1 = b := by rw [Function.comp_apply, hz1, hq, c.gh (hbdΔ hb)]
  rw [hg0, hg1] at hl
  refine ⟨_, hl, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact c.gm (hzb t)
  · ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hx⟩
      have h1 := hsph _ hx
      rw [Function.comp_apply, c.hg (hzb t)] at h1
      by_cases ht0 : t = 0
      · exact .inl (by subst ht0; exact hg0)
      by_cases ht1 : t = 1
      · exact .inr (by subst ht1; exact hg1)
      exfalso
      have ht : t.1 ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne t.2.1 (fun he => ht0 (Subtype.ext he.symm)),
        lt_of_le_of_ne t.2.2 (fun he => ht1 (Subtype.ext he))⟩
      have h2 := (strictConvex_closedBall ℝ (0 : ℂ) 1) (sphere_subset_closedBall (hsph a ha))
        (sphere_subset_closedBall (hsph b hb)) hpq (a := 1 - t.1) (b := t.1) (by linarith [ht.2]) ht.1 (by ring)
      rw [interior_closedBall _ one_ne_zero, mem_ball_zero_iff] at h2
      have h3 : ‖z t‖ = 1 := by simpa using h1
      have h4 : ‖z t‖ < 1 := by simpa [z, Complex.real_smul] using h2
      linarith
    · rintro (rfl | rfl)
      · exact ⟨⟨0, hg0⟩, ha⟩
      · exact ⟨⟨1, hg1⟩, hb⟩


end GraphMinor.GM16
