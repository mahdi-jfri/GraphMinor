module

public import GraphMinor.Surface.CrossCut
import GraphMinor.Surface.ArcTools

/-!
# Reparametrizing excursions on removed intervals

The gluing step of VIII (6.2), page 264, replaces each removed parameter
interval by its outside excursion. This file stretches an embedded unit
interval arc onto any nontrivial real interval, recording continuity,
injectivity and the images of both the open and closed intervals.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

local notation "𝕀" => unitInterval

/-- Stretch an embedded arc to a real interval, extending constantly beyond
its endpoints. The interval endpoints have the original endpoint values,
and the open and closed images are preserved. -/
theorem exists_interval_arc_reparametrization {X : Type u} [TopologicalSpace X]
    {ℓ : 𝕀 → X} (hℓ : IsArcMap ℓ) {a b : ℝ} (hab : a < b) :
    ∃ p : ℝ → X, Continuous p ∧ p a = ℓ 0 ∧ p b = ℓ 1 ∧ InjOn p (Icc a b) ∧
      p '' Icc a b = range ℓ ∧ p '' Ioo a b = ℓ '' Ioo (0 : 𝕀) 1 := by
  let r : ℝ → ℝ := fun t => (t - a) / (b - a)
  let p : ℝ → X := extI ℓ ∘ r
  have hd : 0 < b - a := sub_pos.mpr hab
  have hmem : ∀ t ∈ Icc a b, r t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hd.le,
      (div_le_one hd).mpr (by linarith [ht.2])⟩
  have hopen : ∀ t ∈ Ioo a b, r t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨div_pos (sub_pos.mpr ht.1) hd,
      (div_lt_one hd).mpr (by linarith [ht.2])⟩
  have hinv : ∀ u : 𝕀, r (a + u.1 * (b - a)) = u.1 := by
    intro u
    dsimp [r]
    field_simp
    ring
  have hmix : ∀ u : 𝕀, a + u.1 * (b - a) ∈ Icc a b := by
    intro u
    constructor <;> nlinarith [u.2.1, u.2.2]
  have hmix_open : ∀ u ∈ Ioo (0 : 𝕀) 1, a + u.1 * (b - a) ∈ Ioo a b := by
    intro u hu
    constructor <;> nlinarith [show (0 : ℝ) < u.1 from hu.1,
      show u.1 < (1 : ℝ) from hu.2]
  have hp : ∀ (t : ℝ) (ht : t ∈ Icc a b), p t = ℓ ⟨r t, hmem t ht⟩ := by
    intro t ht
    exact extI_of_mem ℓ (hmem t ht)
  refine ⟨p, (continuous_extI hℓ.1).comp (by dsimp [r]; fun_prop), ?_, ?_, ?_, ?_, ?_⟩
  · change extI ℓ ((a - a) / (b - a)) = ℓ 0
    simp only [sub_self, zero_div]
    exact extI_coe ℓ 0
  · change extI ℓ ((b - a) / (b - a)) = ℓ 1
    rw [div_self hd.ne']
    exact extI_coe ℓ 1
  · intro s hs t ht he
    rw [hp s hs, hp t ht] at he
    have hr := congrArg Subtype.val (hℓ.2 he)
    have hnum : s - a = t - a := (div_left_inj' hd.ne').mp hr
    linarith
  · apply subset_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨⟨r t, hmem t ht⟩, (hp t ht).symm⟩
    · rintro _ ⟨u, rfl⟩
      refine ⟨a + u.1 * (b - a), hmix u, ?_⟩
      change extI ℓ (r (a + u.1 * (b - a))) = ℓ u
      rw [hinv]
      exact extI_coe ℓ u
  · apply subset_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨⟨r t, (hopen t ht).1.le, (hopen t ht).2.le⟩, hopen t ht, ?_⟩
      exact (hp t ⟨ht.1.le, ht.2.le⟩).symm
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨a + u.1 * (b - a), hmix_open u hu, ?_⟩
      change extI ℓ (r (a + u.1 * (b - a))) = ℓ u
      rw [hinv]
      exact extI_coe ℓ u

end GraphMinor.GM08
