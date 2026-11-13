module

public import GraphMinor.Surface.CrossCut

/-!
# Circle coordinates for an angular seed

For the local discs used in VI (5.5), page 130, choose coordinates
that send the upper half of the circle to a given boundary arc.
Glue the two arc maps along their ends. Their injectivity and their
intersection condition give a homeomorphism, and the formula records
which half of the circle maps to the chosen arc.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

/-- Two arcs meeting only at their ends give circle coordinates in
which the first arc is exactly the image of the upper half-circle. -/
theorem exists_circle_homeomorph_respecting_two_arcs {X : Type*} [TopologicalSpace X] [T2Space X] {a b : unitInterval → X}
    (ha : IsArcMap a) (hb : IsArcMap b) (h0 : a 0 = b 0) (h1 : a 1 = b 1)
    (h01 : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ h : Circle ≃ₜ (range a ∪ range b : Set X),
      (∀ w : Circle, (h w).1 ∈ range a ↔ 0 ≤ (w : ℂ).im) ∧
      ∀ w : Circle, (w : ℂ).im = 0 → (h w).1 = a 0 ∨ (h w).1 = a 1 := by
  classical
  have hbd : ∀ w : Circle, |(w : ℂ).re| ≤ 1 := fun w => by
    have := Complex.abs_re_le_norm (w : ℂ)
    rwa [Circle.norm_coe] at this
  let τ : Circle → unitInterval := fun w => ⟨(1 - (w : ℂ).re) / 2, by
    have := abs_le.mp (hbd w)
    constructor <;> linarith [this.1, this.2]⟩
  have hτ : Continuous τ := by
    refine Continuous.subtype_mk ?_ _
    have : Continuous fun w : Circle => (w : ℂ) := continuous_subtype_val
    exact ((continuous_const.sub (Complex.continuous_re.comp this)).div_const 2)
  let g : Circle → X := fun w => if 0 ≤ (w : ℂ).im then a (τ w) else b (τ w)
  have him : Continuous fun w : Circle => (w : ℂ).im :=
    Complex.continuous_im.comp continuous_subtype_val
  have hsq : ∀ w : Circle, (w : ℂ).re * (w : ℂ).re + (w : ℂ).im * (w : ℂ).im = 1 := fun w => by
    have h := Complex.sq_norm (w : ℂ)
    rw [Circle.norm_coe, Complex.normSq_apply] at h
    linarith
  have hτ0 : ∀ w : Circle, (w : ℂ).im = 0 → τ w = 0 ∨ τ w = 1 := by
    intro w hw
    have h := hsq w
    rw [hw] at h
    have hfac : ((w : ℂ).re - 1) * ((w : ℂ).re + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left
      refine Subtype.ext ?_
      show (1 - (w : ℂ).re) / 2 = 0
      rw [sub_eq_zero.mp h1]
      norm_num
    · right
      refine Subtype.ext ?_
      show (1 - (w : ℂ).re) / 2 = 1
      rw [eq_neg_of_add_eq_zero_left h1]
      norm_num
  have hg : Continuous g := by
    refine Continuous.if_le (ha.1.comp hτ) (hb.1.comp hτ) continuous_const him ?_
    intro w hw
    rcases hτ0 w hw.symm with h | h
    · simp only [Function.comp, h, h0]
    · simp only [Function.comp, h, h1]
  have hre : ∀ {w w' : Circle}, τ w = τ w' → (w : ℂ).re = (w' : ℂ).re := fun {w w'} h => by
    have : (1 - (w : ℂ).re) / 2 = (1 - (w' : ℂ).re) / 2 := congrArg Subtype.val h
    linarith
  have hsame : ∀ {w w' : Circle}, τ w = τ w' → 0 ≤ (w : ℂ).im → 0 ≤ (w' : ℂ).im → w = w' := by
    intro w w' h h1 h2
    have h3 := hre h
    have h4 := hsq w
    have h5 := hsq w'
    rw [h3] at h4
    have h6 : (w : ℂ).im = (w' : ℂ).im := by nlinarith [mul_self_nonneg ((w : ℂ).im - (w' : ℂ).im)]
    exact Circle.ext (Complex.ext h3 h6)
  have hsameneg : ∀ {w w' : Circle}, τ w = τ w' → (w : ℂ).im < 0 → (w' : ℂ).im < 0 → w = w' := by
    intro w w' h h1 h2
    have h3 := hre h
    have h4 := hsq w
    have h5 := hsq w'
    rw [h3] at h4
    have h6 : (w : ℂ).im = (w' : ℂ).im := by nlinarith [mul_self_nonneg ((w : ℂ).im - (w' : ℂ).im)]
    exact Circle.ext (Complex.ext h3 h6)
  -- The two points with parameter `0` and `1` lie on the real axis.
  have him0 : ∀ {w : Circle}, τ w = 0 ∨ τ w = 1 → (w : ℂ).im = 0 := by
    intro w h
    have h4 := hsq w
    have hre1 : (w : ℂ).re = 1 ∨ (w : ℂ).re = -1 := by
      rcases h with h | h
      · left
        have : (1 - (w : ℂ).re) / 2 = 0 := congrArg Subtype.val h
        linarith
      · right
        have : (1 - (w : ℂ).re) / 2 = 1 := congrArg Subtype.val h
        linarith
    rcases hre1 with h1 | h1 <;> rw [h1] at h4 <;> nlinarith [mul_self_nonneg (w : ℂ).im]
  have hmixed : ∀ {w w' : Circle}, 0 ≤ (w : ℂ).im → (w' : ℂ).im < 0 → a (τ w) = b (τ w') → False := by
    intro w w' h1 h2 h
    rcases h01 _ _ h with ⟨_, h3⟩ | ⟨_, h3⟩
    · exact absurd (him0 (Or.inl h3)) h2.ne
    · exact absurd (him0 (Or.inr h3)) h2.ne
  have hgi : Function.Injective g := by
    intro w w' h
    simp only [g] at h
    by_cases h1 : 0 ≤ (w : ℂ).im <;> by_cases h2 : 0 ≤ (w' : ℂ).im
    · simp only [h1, h2, ite_true] at h
      exact hsame (ha.2 h) h1 h2
    · simp only [h1, h2, ite_true, ite_false] at h
      exact (hmixed h1 (not_le.mp h2) h).elim
    · simp only [h1, h2, ite_true, ite_false] at h
      exact (hmixed h2 (not_le.mp h1) h.symm).elim
    · simp only [h1, h2, ite_false] at h
      exact hsameneg (hb.2 h) (not_le.mp h1) (not_le.mp h2)
  have hrange : range g = range a ∪ range b := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      by_cases h1 : 0 ≤ (w : ℂ).im
      · left
        simp only [g, h1, ite_true]
        exact ⟨_, rfl⟩
      · right
        simp only [g, h1, ite_false]
        exact ⟨_, rfl⟩
    · have hpt : ∀ t : unitInterval, ∃ w : Circle, τ w = t ∧ 0 ≤ (w : ℂ).im ∧
          ∃ w' : Circle, τ w' = t ∧ (w' : ℂ).im ≤ 0 := by
        intro t
        have ht0 := t.2.1
        have ht1 := t.2.2
        set x : ℝ := 1 - 2 * t with hx
        have hx2 : 0 ≤ 1 - x * x := by rw [hx]; nlinarith
        set y := Real.sqrt (1 - x * x) with hy
        have hy2 : y * y = 1 - x * x := Real.mul_self_sqrt hx2
        have hnorm : ∀ s : ℝ, s * s = y * y → ‖(⟨x, s⟩ : ℂ)‖ = 1 := by
          intro s hs
          have h := Complex.sq_norm (⟨x, s⟩ : ℂ)
          rw [Complex.normSq_mk, hs, hy2] at h
          have h3 : ‖(⟨x, s⟩ : ℂ)‖ ^ 2 = 1 ^ 2 := by rw [h]; ring
          exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h3
        have hτt : ∀ (s : ℝ) (hs : ‖(⟨x, s⟩ : ℂ)‖ = 1),
            τ ⟨⟨x, s⟩, mem_sphere_zero_iff_norm.mpr hs⟩ = t := by
          intro s hs
          refine Subtype.ext ?_
          show (1 - x) / 2 = t
          rw [hx]
          ring
        refine ⟨⟨⟨x, y⟩, mem_sphere_zero_iff_norm.mpr (hnorm y rfl)⟩, hτt y (hnorm y rfl),
          Real.sqrt_nonneg _, ⟨⟨x, -y⟩, mem_sphere_zero_iff_norm.mpr (hnorm (-y) (by ring))⟩,
          hτt (-y) (hnorm (-y) (by ring)), ?_⟩
        show -y ≤ 0
        linarith [Real.sqrt_nonneg (1 - x * x)]
      rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · obtain ⟨w, hw, h1, -⟩ := hpt t
        exact ⟨w, by simp only [g, h1, ite_true, hw]⟩
      · obtain ⟨-, -, -, w, hw, hle⟩ := hpt t
        rcases eq_or_lt_of_le hle with h2 | h2
        · refine ⟨w, ?_⟩
          simp only [g, h2, le_refl, ite_true, hw]
          rcases hτ0 w h2 with h3 | h3
          · rw [← hw, h3, h0]
          · rw [← hw, h3, h1]
        · exact ⟨w, by simp only [g, not_le.mpr h2, ite_false, hw]⟩
  have hemb := (hg.isClosedEmbedding hgi).isEmbedding
  let h := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  refine ⟨h, ?_, ?_⟩
  · intro w
    change g w ∈ range a ↔ 0 ≤ (w : ℂ).im
    constructor
    · rintro ⟨t, ht⟩
      by_contra hw
      have he : a t = b (τ w) := by simpa [g, hw] using ht
      rcases h01 _ _ he with ⟨_, hh⟩ | ⟨_, hh⟩
      · exact (not_le.mp hw).ne (him0 (Or.inl hh))
      · exact (not_le.mp hw).ne (him0 (Or.inr hh))
    · intro hw
      exact ⟨τ w, by simp [g, hw]⟩
  
  · intro w hw
    change g w = a 0 ∨ g w = a 1
    rcases hτ0 w hw with he | he
    · left; simp [g, hw, he]
    · right; simp [g, hw, he]


end GraphMinor.GM06
