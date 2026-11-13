module

public import GraphMinor.Surface.CrossCut

/-!
# Simple loops from the excursion construction

The boundary constructed for VIII (6.2), page 264, is parametrized on a
closed interval. This file turns continuity and injectivity away from the
identified endpoints into an `O`-arc, by splitting the loop into two arcs.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

private theorem simple_loop_eq_cases {Y : Type u} {g : ℝ → Y}
    (hends : g 0 = g 1) (hinj : InjOn g (Ico 0 1))
    {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (he : g s = g t) :
    s = t ∨ s = 0 ∧ t = 1 ∨ s = 1 ∧ t = 0 := by
  by_cases hs1 : s = 1
  · by_cases ht1 : t = 1
    · exact Or.inl (hs1.trans ht1.symm)
    · have ht0 : t = 0 := hinj ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
        ⟨le_rfl, zero_lt_one⟩ (he.symm.trans (hs1 ▸ hends.symm))
      exact Or.inr (Or.inr ⟨hs1, ht0⟩)
  · by_cases ht1 : t = 1
    · have hs0 : s = 0 := hinj ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
        ⟨le_rfl, zero_lt_one⟩ (he.trans (ht1 ▸ hends.symm))
      exact Or.inr (Or.inl ⟨hs0, ht1⟩)
    · exact Or.inl (hinj ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
        ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ he)

/-- A continuous loop that is injective before its final parameter traces
an `O`-arc. Applied after excursion replacement, this proves that the
constructed boundary is a simple closed curve, including at accumulation
points of replaced intervals. -/
theorem isOArc_image_of_simple_loop {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    {g : ℝ → Y} (hg : Continuous g) (hends : g 0 = g 1) (hinj : InjOn g (Ico 0 1)) :
    IsOArc (g '' Icc 0 1) := by
  let a : unitInterval → Y := fun t => g (t.1 / 2)
  let b : unitInterval → Y := fun t => g (1 - t.1 / 2)
  have hpa : ∀ t : unitInterval, t.1 / 2 ∈ Icc (0 : ℝ) 1 := by
    intro t
    constructor <;> linarith [t.2.1, t.2.2]
  have hpb : ∀ t : unitInterval, 1 - t.1 / 2 ∈ Icc (0 : ℝ) 1 := by
    intro t
    constructor <;> linarith [t.2.1, t.2.2]
  have ha : IsArcMap a := by
    refine ⟨hg.comp (continuous_subtype_val.div_const 2), ?_⟩
    intro s t he
    rcases simple_loop_eq_cases hends hinj (hpa s) (hpa t) he with h | h | h
    · apply Subtype.ext
      linarith
    · linarith [h.2, t.2.2]
    · linarith [h.1, s.2.2]
  have hb : IsArcMap b := by
    refine ⟨hg.comp (continuous_const.sub (continuous_subtype_val.div_const 2)), ?_⟩
    intro s t he
    rcases simple_loop_eq_cases hends hinj (hpb s) (hpb t) he with h | h | h
    · apply Subtype.ext
      linarith
    · linarith [h.1, s.2.2]
    · linarith [h.2, t.2.2]
  have h0 : a 0 = b 0 := by simpa [a, b] using hends
  have h1 : a 1 = b 1 := by norm_num [a, b]
  have hmeet : ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    rcases simple_loop_eq_cases hends hinj (hpa s) (hpb t) he with h | h | h
    · right
      constructor <;> apply Subtype.ext <;> dsimp <;>
        linarith [s.2.1, s.2.2, t.2.1, t.2.2]
    · left
      constructor <;> apply Subtype.ext <;> dsimp <;> linarith [h.1, h.2]
    · linarith [h.1, s.2.2]
  have hr : range a ∪ range b = g '' Icc 0 1 := by
    apply subset_antisymm
    · rintro z (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨t.1 / 2, hpa t, rfl⟩
      · exact ⟨1 - t.1 / 2, hpb t, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      by_cases hhalf : t ≤ 1 / 2
      · left
        refine ⟨⟨2 * t, by constructor <;> linarith [ht.1]⟩, ?_⟩
        dsimp [a]
        congr 1
        ring
      · right
        refine ⟨⟨2 * (1 - t), by constructor <;> linarith [ht.2]⟩, ?_⟩
        dsimp [b]
        congr 1
        ring
  rw [← hr]
  exact oArc_of_two_arcs ha hb h0 h1 hmeet

end GraphMinor.GM08
