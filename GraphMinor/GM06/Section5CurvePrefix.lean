module

public import GraphMinor.GM06.Defs
import Mathlib.Tactic

/-!
# Parametrizing an initial segment of an injective curve

For the boundary arc beside the region path in VI (5.1), page 129,
follow an old linkage curve from its start to the contact parameter.
Rescale the unit interval by that positive parameter. Injectivity is
preserved, and the resulting image is exactly the initial segment.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface unitInterval
universe u

/-- An initial segment ending at a positive parameter has an
injective unit-interval parametrization with the prescribed ends. -/
theorem exists_parametrizes_initial_curve_segment
    {S : Type u} [TopologicalSpace S] (f : Curve S) (hf : Function.Injective f)
    (τ : unitInterval) (hτ : 0 < τ) :
    ∃ g : Curve S, ParametrizesSet g (f '' Icc 0 τ) (f 0) (f τ) := by
  let g : Curve S := ⟨fun t => f (t * τ), f.continuous.comp (by fun_prop)⟩
  have hτR : (0 : ℝ) < τ := hτ
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    have heq : (s : ℝ) * τ = (t : ℝ) * τ := congrArg Subtype.val (hf hst)
    exact Subtype.ext (mul_right_cancel₀ hτR.ne' heq)
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t * τ, ⟨bot_le, unitInterval.mul_le_right⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      let s : unitInterval := ⟨(t : ℝ) / τ,
        div_nonneg t.2.1 hτR.le, (div_le_one₀ hτR).mpr ht.2⟩
      refine ⟨s, ?_⟩
      have hsτ : s * τ = t := by
        apply Subtype.ext
        change ((t : ℝ) / τ) * τ = t
        exact div_mul_cancel₀ _ hτR.ne'
      change f (s * τ) = f t
      rw [hsτ]
  · change f (0 * τ) = f 0
    rw [zero_mul]
  · change f (1 * τ) = f τ
    rw [one_mul]

end GraphMinor.GM06
