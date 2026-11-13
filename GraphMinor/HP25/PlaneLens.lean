module

public import GraphMinor.Surface.EdgeLens
import GraphMinor.Surface.ArcDisc
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.PlaneOrientation

/-!
# A thin disc around a line of the plane

The library proves, in a closed surface, that a line `L` with ends `u, v` has a thin closed disc
around it that meets a given closed set `Z` (which meets `L` only at its ends) only at `u, v`
(`Surface.exists_edge_lens_sides`, `Surface/EdgeLens.lean`). The line cuts the disc into two sides.
This file proves the same statement in the plane `ℂ`, which is not compact
(`exists_plane_edge_lens_sides`). The proof is the library's, word for word, except for its first
step: the library puts the line inside a closed disc of the surface (`Surface.exists_disc_of_arc`),
and in the plane we take a large open ball around the line, with the chart `z ↦ M z`.

We use it for the faces on the two sides of an edge of a plane embedding (Proposition 2.3 of
Humeau and Pous).
-/

public section

namespace GraphMinor.HP25

open Set Topology Metric Complex GraphMinor.Surface

local notation "𝕀" => unitInterval

/-- A thin closed disc around a line of the plane, with its two sides: the plane form of
`Surface.exists_edge_lens_sides`. -/
theorem exists_plane_edge_lens_sides {L : Set ℂ} {u v : ℂ} (hL : IsLineWithEnds L u v) (huv : u ≠ v)
    {Z : Set ℂ} (hZ : IsClosed Z) (hLZ : L ∩ Z ⊆ {u, v}) :
    ∃ D A B, IsClosedDisc D ∧ L ⊆ D ∧ D ∩ Z ⊆ {u, v} ∧ u ∈ discBd D ∧ v ∈ discBd D ∧ discBd D ∩ L ⊆ {u, v} ∧
      D = A ∪ B ∪ L ∧ IsPreconnected A ∧ IsPreconnected B ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A L ∧ Disjoint B L ∧ L ⊆ closure A ∧ L ⊆ closure B ∧
      (∃ p : Path u v, range p ⊆ D ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ A) ∧ (∃ p : Path u v, range p ⊆ D ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ B) ∧
      Disjoint A B ∧ IsPathConnected (A \ discBd D) ∧ IsPathConnected (B \ discBd D) := by
  classical
  have hman : ∀ x : ℂ, IsManifoldPoint x := isManifoldPoint_complex
  obtain ⟨a, ha, hr, ha0, ha1⟩ := hL.exists_arc
  -- a large ball around the line, as the image of the unit ball under `z ↦ M z`
  obtain ⟨M, hM0, hM⟩ := (isCompact_range ha.1).isBounded.subset_ball_lt 0 0
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  set g : ℂ → ℂ := fun z => (M : ℂ) * z with hg
  set h : ℂ → ℂ := fun z => z / (M : ℂ) with hh
  have hgball : g '' ball 0 1 = ball 0 M := by
    ext w
    simp only [mem_image, mem_ball, dist_zero_right, g]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0]
      nlinarith [norm_nonneg z]
    · intro hw
      refine ⟨w / M, ?_, by field_simp⟩
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, div_lt_one hM0]
      exact hw
  have hbc : BallChart 1 (g '' ball 0 1) h g := by
    rw [hgball]
    refine ⟨isOpen_ball, (by fun_prop : Continuous h).continuousOn,
      (by fun_prop : Continuous g).continuousOn, ?_, ?_, ?_, ?_⟩
    · intro w hw
      simp only [mem_ball, dist_zero_right, h] at hw ⊢
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, div_lt_one hM0]
      exact hw
    · intro z hz
      rw [← hgball]
      exact mem_image_of_mem g hz
    · intro w _
      simp only [g, h]
      field_simp
    · intro z _
      simp only [g, h]
      field_simp
  have hU : range a ⊆ g '' ball 0 1 := by
    rw [hgball]
    exact hM
  obtain ⟨O, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart hman hbc ha hU
  have hlt : θ 0 < θ 1 := hθm (by simp)
  set A : ℝ := (θ 1 - θ 0) / 2 with hA
  set B : ℝ := (θ 0 + θ 1) / 2 with hB
  have hApos : 0 < A := by rw [hA]; linarith
  let aff : ℂ → ℂ := fun z => (B : ℂ) + (A : ℂ) * z
  have haffc : Continuous aff := by fun_prop
  have haffi : Function.Injective aff := fun x y h' => by
    have h1 : (A : ℂ) * x = (A : ℂ) * y := add_left_cancel h'
    exact mul_left_cancel₀ (by exact_mod_cast hApos.ne') h1
  have hreal : ∀ s : ℝ, aff s = ((B + A * s : ℝ) : ℂ) := fun s => by
    simp [aff]
  have hone : aff 1 = (θ 1 : ℂ) := by
    have := hreal 1
    simp only [Complex.ofReal_one] at this
    rw [this]
    congr 1
    rw [hA, hB]
    ring
  have hmone : aff (-1) = (θ 0 : ℂ) := by
    have := hreal (-1)
    simp only [Complex.ofReal_neg, Complex.ofReal_one] at this
    rw [this]
    congr 1
    rw [hA, hB]
    ring
  let O₁ : Set ℂ := aff ⁻¹' O
  have hO₁ : IsOpen O₁ := hK.isOpen.preimage haffc
  let K₁ : ℂ → ℂ := K ∘ aff
  have hK₁c : ContinuousOn K₁ O₁ := hK.hc.comp haffc.continuousOn fun _ h' => h'
  have hK₁i : InjOn K₁ O₁ := fun x hx y hy h' => haffi (hK.hi hx hy h')
  have h1O : (1 : ℂ) ∈ O₁ := by
    show aff 1 ∈ O
    rw [hone]
    exact (hθ 1).1
  have hmO : (-1 : ℂ) ∈ O₁ := by
    show aff (-1) ∈ O
    rw [hmone]
    exact (hθ 0).1
  have hK1 : K₁ 1 = v := by
    show K (aff 1) = v
    rw [hone, (hθ 1).2, ha1]
  have hKm : K₁ (-1) = u := by
    show K (aff (-1)) = u
    rw [hmone, (hθ 0).2, ha0]
  have hsθ : ∀ s ∈ Icc (-1 : ℝ) 1, ∃ t, θ t = B + A * s := fun s hs' =>
    mem_range_of_exists_le_of_exists_ge hθc ⟨0, by rw [hA, hB]; nlinarith [hs'.1]⟩ ⟨1, by rw [hA, hB]; nlinarith [hs'.2]⟩
  have hsO : ∀ s ∈ Icc (-1 : ℝ) 1, ∃ t, (s : ℂ) ∈ O₁ ∧ K₁ s = a t ∧ θ t = B + A * s := fun s hs' => by
    obtain ⟨t, ht⟩ := hsθ s hs'
    have e : aff s = (θ t : ℂ) := by rw [hreal, ht]
    refine ⟨t, ?_, ?_, ht⟩
    · show aff s ∈ O
      rw [e]
      exact (hθ t).1
    · show K (aff s) = a t
      rw [e, (hθ t).2]
  let Z₁ : Set ℂ := (O₁ᶜ ∪ (O₁ ∩ K₁ ⁻¹' Z)) ∪ {1, -1}
  have hZ₁ : IsClosed Z₁ := by
    have h1 : (O₁ ∩ K₁ ⁻¹' Zᶜ) = (O₁ᶜ ∪ (O₁ ∩ K₁ ⁻¹' Z))ᶜ := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_union, not_or, not_and, not_not]
      exact ⟨fun h' => ⟨h'.1, fun _ => h'.2⟩, fun h' => ⟨h'.1, h'.2 h'.1⟩⟩
    have h2 : IsOpen (O₁ ∩ K₁ ⁻¹' Zᶜ) := hK₁c.isOpen_inter_preimage hO₁ hZ.isOpen_compl
    rw [h1] at h2
    exact (isOpen_compl_iff.mp h2).union ((finite_singleton _).insert _).isClosed
  have hZne : Z₁.Nonempty := ⟨1, .inr (.inl rfl)⟩
  have hsZ : ∀ s ∈ Ioo (-1 : ℝ) 1, (s : ℂ) ∉ Z₁ := fun s hs' hin => by
    obtain ⟨t, hO, hKt, hθt⟩ := hsO s ⟨hs'.1.le, hs'.2.le⟩
    have ht0 : t ≠ 0 := fun h' => by
      rw [h', hA, hB] at hθt
      nlinarith [hs'.1]
    have ht1 : t ≠ 1 := fun h' => by
      rw [h', hA, hB] at hθt
      nlinarith [hs'.2]
    rcases hin with (h1 | h1) | h1
    · exact h1 hO
    · have h2 : a t ∈ L ∩ Z := ⟨hr ▸ mem_range_self t, hKt ▸ h1.2⟩
      rcases hLZ h2 with h3 | h3
      · exact ht0 (ha.2 (h3.trans ha0.symm))
      · exact ht1 (ha.2 (h3.trans ha1.symm))
    · rcases h1 with h1 | h1
      · have : s = 1 := by exact_mod_cast h1
        linarith [hs'.2]
      · have h1' : (s : ℂ) = -1 := h1
        have : s = -1 := by
          have h2 := congrArg Complex.re h1'
          simpa using h2
        linarith [hs'.1]
  let w := lensW Z₁
  have hwc : Continuous w := by
    show Continuous fun s : ℝ => infDist (s : ℂ) Z₁ / 2
    exact ((continuous_infDist_pt Z₁).comp continuous_ofReal).div_const 2
  have hw1 : w 1 = 0 := by
    show infDist (((1 : ℝ) : ℂ)) Z₁ / 2 = 0
    rw [Complex.ofReal_one, infDist_zero_of_mem (.inr (.inl rfl)), zero_div]
  have hwm : w (-1) = 0 := by
    show infDist (((-1 : ℝ) : ℂ)) Z₁ / 2 = 0
    rw [Complex.ofReal_neg, Complex.ofReal_one, infDist_zero_of_mem (.inr (.inr rfl)), zero_div]
  have hlc := continuousOn_lensMap hwc hw1 hwm
  have hli := injOn_lensMap hZ₁ hZne hsZ
  have hl1 : lensMap w 1 = 1 := by simpa using lensMap_real (w := w) 1
  have hlm : lensMap w (-1) = -1 := by simpa using lensMap_real (w := w) (-1)
  have hlin : ∀ z ∈ closedBall (0 : ℂ) 1, z.re ∈ Ioo (-1 : ℝ) 1 → lensMap w z ∈ O₁ ∧ K₁ (lensMap w z) ∉ Z := fun z hz hre => by
    have h1 := lensMap_notMem hZ₁ hZne hsZ hz hre
    have h2 : lensMap w z ∈ O₁ := by
      by_contra hc
      exact h1 (.inl (.inl hc))
    exact ⟨h2, fun h3 => h1 (.inl (.inr ⟨h2, h3⟩))⟩
  have hlO : ∀ z ∈ closedBall (0 : ℂ) 1, lensMap w z ∈ O₁ := fun z hz => by
    by_cases hre : z.re ∈ Ioo (-1 : ℝ) 1
    · exact (hlin z hz hre).1
    · rcases eq_one_or_of_re hz hre with rfl | rfl
      · rw [hl1]
        exact h1O
      · rw [hlm]
        exact hmO
  let Φ : ℂ → ℂ := K₁ ∘ lensMap w
  have hΦc : ContinuousOn Φ (closedBall 0 1) := hK₁c.comp hlc hlO
  have hΦi : InjOn Φ (closedBall 0 1) := fun x hx y hy he => hli hx hy (hK₁i (hlO x hx) (hlO y hy) he)
  obtain ⟨hball, hballbd⟩ := isClosedDisc_of_convex (convex_closedBall (0 : ℂ) 1) (by
    rw [interior_closedBall _ one_ne_zero]
    exact ⟨0, by simp⟩) isBounded_closedBall isClosed_closedBall
  obtain ⟨hD, hDb⟩ := hball.image_injOn hΦc hΦi
  rw [hballbd, frontier_closedBall _ one_ne_zero] at hDb
  have hΦ1 : Φ 1 = v := by
    show K₁ (lensMap w 1) = v
    rw [hl1, hK1]
  have hΦm : Φ (-1) = u := by
    show K₁ (lensMap w (-1)) = u
    rw [hlm, hKm]
  have hts : ∀ t, ∃ s ∈ Icc (-1 : ℝ) 1, θ t = B + A * s := fun t => by
    refine ⟨(θ t - B) / A, ⟨?_, ?_⟩, by field_simp; ring⟩
    · rw [le_div_iff₀ hApos]
      have := hθm.monotone (unitInterval.nonneg' (t := t))
      rw [hA, hB]
      linarith
    · rw [div_le_iff₀ hApos]
      have := hθm.monotone (unitInterval.le_one' (t := t))
      rw [hA, hB]
      linarith
  have hsball : ∀ s ∈ Icc (-1 : ℝ) 1, (s : ℂ) ∈ closedBall (0 : ℂ) 1 := fun s hs' => by
    have : |s| ≤ 1 := abs_le.mpr hs'
    simpa [Complex.norm_real] using this
  have hΦs : ∀ t, ∀ s : ℝ, θ t = B + A * s → Φ s = a t := fun t s hst => by
    show K₁ (lensMap w s) = a t
    rw [lensMap_real]
    show K (aff s) = a t
    rw [hreal, ← hst, (hθ t).2]
  have hΦL : ∀ s ∈ Icc (-1 : ℝ) 1, Φ s ∈ L := fun s hs' => by
    obtain ⟨t, -, hKt, hθt⟩ := hsO s hs'
    rw [hΦs t s hθt, ← hr]
    exact mem_range_self t
  have hLs : ∀ y ∈ L, ∃ s ∈ Icc (-1 : ℝ) 1, Φ s = y := fun y hy => by
    obtain ⟨t, rfl⟩ : y ∈ range a := hr ▸ hy
    obtain ⟨s, hs', hst⟩ := hts t
    exact ⟨s, hs', hΦs t s hst⟩
  have hnotL : ∀ z ∈ closedBall (0 : ℂ) 1, z.im ≠ 0 → Φ z ∉ L := fun z hz him hzL => by
    obtain ⟨s, hs', hse⟩ := hLs _ hzL
    have := hΦi (hsball s hs') hz hse
    exact him (by rw [← this]; simp)
  have hclo : ∀ (c : ℝ), c ≠ 0 → |c| = 1 → L ⊆ closure (Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im}) := fun c _ hc y hy => by
    obtain ⟨s, hs', rfl⟩ := hLs y hy
    refine ContinuousWithinAt.mem_closure_image (hΦc _ (hsball s hs') |>.mono fun z hz => hz.1) ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    set τ := min 1 (ε / 3) with hτ
    have hτ0 : 0 < τ := lt_min one_pos (by positivity)
    have hτ1 : τ ≤ 1 := min_le_left _ _
    have hτ2 : τ ≤ ε / 3 := min_le_right _ _
    have hsn : ‖(s : ℂ)‖ ≤ 1 := by simpa using hsball s hs'
    have hin : ‖((c : ℂ) * I)‖ = 1 := by simp [hc]
    refine ⟨(1 - τ : ℝ) * (s : ℂ) + (τ : ℝ) * ((c : ℂ) * I), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]
      calc _ ≤ ‖((1 - τ : ℝ) : ℂ) * (s : ℂ)‖ + ‖((τ : ℝ) : ℂ) * ((c : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ (1 - τ) * 1 + τ * 1 := by
          have hsn' : ‖s‖ ≤ 1 := by simpa [Complex.norm_real] using hsn
          simp only [norm_mul, hin, Complex.norm_real, Real.norm_of_nonneg hτ0.le, Real.norm_of_nonneg (show 0 ≤ 1 - τ by linarith)]
          nlinarith
        _ = 1 := by ring
    · have him : ((1 - τ : ℝ) * (s : ℂ) + (τ : ℝ) * ((c : ℂ) * I)).im = τ * c := by simp
      rw [him]
      have hcc : c * c = 1 := by rw [← abs_mul_self, abs_mul, hc, one_mul]
      nlinarith
    · have he : (s : ℂ) - ((1 - τ : ℝ) * (s : ℂ) + (τ : ℝ) * ((c : ℂ) * I)) = (τ : ℝ) * ((s : ℂ) - (c : ℂ) * I) := by
        push_cast
        ring
      rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
      have h2 : ‖(s : ℂ) - (c : ℂ) * I‖ ≤ 2 := by
        calc _ ≤ ‖(s : ℂ)‖ + ‖(c : ℂ) * I‖ := norm_sub_le _ _
          _ ≤ 2 := by rw [hin]; linarith
      nlinarith
  have hconv : ∀ c : ℝ, Convex ℝ {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im} := fun c => by
    refine (convex_closedBall _ _).inter ?_
    intro x hx y hy p q hp hq hpq
    have e : c * (p • x + q • y).im = p * (c * x.im) + q * (c * y.im) := by
      simp
      ring
    show 0 < c * (p • x + q • y).im
    rw [e]
    have hx' : 0 < c * x.im := hx
    have hy' : 0 < c * y.im := hy
    rcases hp.eq_or_lt with h | h
    · have : q = 1 := by linarith
      subst h
      simpa [this] using hy'
    · have := mul_pos h hx'
      have := mul_nonneg hq hy'.le
      linarith
  have hupc := hconv 1
  have hloc := hconv (-1)
  have hpath : ∀ c : ℝ, |c| = 1 → ∃ p : Path u v, range p ⊆ Φ '' closedBall 0 1 ∧ ∀ t : 𝕀, 0 < t → t < 1 →
      p t ∈ Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im} := fun c hc' => by
    have hcc : c * c = 1 := by rw [← abs_mul_self, abs_mul, hc', one_mul]
    let z : 𝕀 → ℂ := fun t => ((2 * t.1 - 1 : ℝ) : ℂ) + ((2 * c * t.1 * (1 - t.1) : ℝ) : ℂ) * I
    have hzre : ∀ t, (z t).re = 2 * t.1 - 1 := fun t => by simp [z]
    have hzim : ∀ t, (z t).im = 2 * c * t.1 * (1 - t.1) := fun t => by simp [z]
    have hzb : ∀ t, z t ∈ closedBall (0 : ℂ) 1 := fun t => by
      have h0 := t.2.1
      have h1 := t.2.2
      have hp : 0 ≤ t.1 * (1 - t.1) := mul_nonneg h0 (by linarith)
      have hq : t.1 * (1 - t.1) ≤ 1 := by nlinarith
      have hsq : (z t).re ^ 2 + (z t).im ^ 2 ≤ 1 := by
        rw [hzre, hzim]
        have e : (2 * c * t.1 * (1 - t.1)) ^ 2 = 4 * (c * c) * (t.1 * (1 - t.1)) ^ 2 := by ring
        rw [e, hcc]
        nlinarith
      have h3 := Complex.sq_norm (z t)
      rw [Complex.normSq_apply] at h3
      rw [mem_closedBall_zero_iff]
      nlinarith [norm_nonneg (z t)]
    have hzc : Continuous z := by
      show Continuous fun t : 𝕀 => ((2 * t.1 - 1 : ℝ) : ℂ) + ((2 * c * t.1 * (1 - t.1) : ℝ) : ℂ) * I
      fun_prop
    have hz0 : z 0 = -1 := by
      apply Complex.ext
      · rw [hzre]
        norm_num
      · rw [hzim]
        simp
    have hz1 : z 1 = 1 := by
      apply Complex.ext
      · rw [hzre]
        norm_num
      · rw [hzim]
        simp
    refine ⟨⟨⟨fun t => Φ (z t), hΦc.comp_continuous hzc hzb⟩, by simp [hz0, hΦm], by simp [hz1, hΦ1]⟩, ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩
      exact ⟨z t, hzb t, rfl⟩
    · intro t h0 h1
      refine ⟨z t, ⟨hzb t, ?_⟩, rfl⟩
      have h0' : 0 < t.1 := h0
      have h1' : t.1 < 1 := h1
      rw [hzim]
      have e : c * (2 * c * t.1 * (1 - t.1)) = 2 * (c * c) * t.1 * (1 - t.1) := by ring
      rw [e, hcc]
      have := mul_pos h0' (sub_pos.mpr h1')
      nlinarith
  have hin : ∀ c : ℝ, IsPathConnected (Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im} \ Φ '' sphere 0 1) ∨ c = 0 := fun c => by
    by_cases hc : c = 0
    · exact .inr hc
    left
    have hbc : Convex ℝ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ 0 < c * z.im} := by
      have e : {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ 0 < c * z.im} = ball (0 : ℂ) 1 ∩ {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im} := by
        ext z
        exact ⟨fun h => ⟨h.1, ball_subset_closedBall h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [e]
      exact (convex_ball _ _).inter (hconv c)
    have hne : {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ 0 < c * z.im}.Nonempty := by
      refine ⟨(((1 / 2 : ℝ) * c / |c| : ℝ) : ℂ) * I, ?_, ?_⟩
      · have : ‖(((1 / 2 : ℝ) * c / |c| : ℝ) : ℂ) * I‖ = 1 / 2 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_abs, div_eq_mul_inv]
          have h2 : |c| ≠ 0 := abs_ne_zero.mpr hc
          field_simp
          simp
        rw [mem_ball_zero_iff, this]
        norm_num
      · have h2 : 0 < |c| := abs_pos.mpr hc
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
        have : c * ((1 / 2 : ℝ) * c / |c|) = (c * c) / (2 * |c|) := by ring
        rw [this]
        have := mul_self_pos.mpr hc
        positivity
    have e : Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im} \ Φ '' sphere 0 1 = Φ '' {z | z ∈ ball (0 : ℂ) 1 ∧ 0 < c * z.im} := by
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hy⟩
        refine ⟨z, ⟨?_, hz.2⟩, rfl⟩
        have h1 : ‖z‖ ≤ 1 := by simpa using hz.1
        have h2 : ‖z‖ ≠ 1 := fun h => hy ⟨z, by simpa using h, rfl⟩
        simpa using lt_of_le_of_ne h1 h2
      · rintro ⟨z, hz, rfl⟩
        refine ⟨⟨z, ⟨ball_subset_closedBall hz.1, hz.2⟩, rfl⟩, ?_⟩
        rintro ⟨z', hz', he⟩
        have := hΦi (sphere_subset_closedBall hz') (ball_subset_closedBall hz.1) he
        rw [this] at hz'
        have h1 : ‖z‖ = 1 := by simpa using hz'
        have h2 : ‖z‖ < 1 := by simpa using hz.1
        linarith
    rw [e]
    exact (hbc.isPathConnected hne).image' (hΦc.mono fun z hz => ball_subset_closedBall hz.1)
  refine ⟨Φ '' closedBall 0 1, Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < (1 : ℝ) * z.im}, Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < (-1 : ℝ) * z.im}, hD, ?_, ?_, ?_, ?_, ?_, ?_,
    (hupc.isPreconnected.image _ (hΦc.mono fun z hz => hz.1)), (hloc.isPreconnected.image _ (hΦc.mono fun z hz => hz.1)), ?_, ?_, ?_, ?_, hclo 1 one_ne_zero (by simp), hclo (-1) (by norm_num) (by simp), hpath 1 (by simp), hpath (-1) (by simp), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨s, hs', rfl⟩ := hLs y hy
    exact ⟨s, hsball s hs', rfl⟩
  · rintro y ⟨⟨z, hz, rfl⟩, hyZ⟩
    by_cases hre : z.re ∈ Ioo (-1 : ℝ) 1
    · exact absurd hyZ (hlin z hz hre).2
    · rcases eq_one_or_of_re hz hre with rfl | rfl
      · exact .inr hΦ1
      · exact .inl hΦm
  · rw [hDb]
    exact ⟨-1, by simp, hΦm⟩
  · rw [hDb]
    exact ⟨1, by simp, hΦ1⟩
  · rintro y ⟨hy, hyL⟩
    rw [hDb] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzb : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
    by_cases hre : z.re ∈ Ioo (-1 : ℝ) 1
    · exfalso
      obtain ⟨t, ht⟩ : Φ z ∈ range a := hr ▸ hyL
      obtain ⟨s, hs', hst⟩ := hts t
      obtain ⟨t', hOs, hKs, hθt'⟩ := hsO s hs'
      have ht' : t' = t := hθm.injective (hθt'.trans hst.symm)
      subst ht'
      have he := hK₁i (hlin z hzb hre).1 hOs (ht.symm.trans hKs.symm).symm.symm
      have him := congrArg Complex.im he
      rw [lensMap_im, Complex.ofReal_im] at him
      have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
        have h2 : ‖z‖ = 1 := by simpa using hz
        have h3 := Complex.sq_norm z
        rw [Complex.normSq_apply, h2] at h3
        nlinarith
      have hpos : 0 < w z.re := lensW_pos hZ₁ hZne (hsZ _ hre)
      have h4 : z.im / Real.sqrt (1 - z.re ^ 2) = 0 := (mul_eq_zero.mp him).resolve_left hpos.ne'
      have h5 : z.im = 0 := by
        rcases div_eq_zero_iff.mp h4 with h6 | h6
        · exact h6
        · exact absurd h6 (re_mem_Ioo_sqrt hre).ne'
      rw [h5] at hsq
      nlinarith [hre.1, hre.2]
    · rcases eq_one_or_of_re hzb hre with rfl | rfl
      · exact .inr hΦ1
      · exact .inl hΦm
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rcases lt_trichotomy z.im 0 with h | h | h
      · exact .inl (.inr ⟨z, ⟨hz, by linarith⟩, rfl⟩)
      · refine .inr ?_
        have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])
        rw [e]
        have hn := re_sq_add_im_sq_le hz
        rw [h] at hn
        exact hΦL _ ⟨by nlinarith, by nlinarith⟩
      · exact .inl (.inl ⟨z, ⟨hz, by linarith⟩, rfl⟩)
    · refine union_subset (union_subset (image_mono fun z hz => hz.1) (image_mono fun z hz => hz.1)) ?_
      intro y hy
      obtain ⟨s, hs', rfl⟩ := hLs y hy
      exact ⟨s, hsball s hs', rfl⟩
  · exact ⟨_, I, ⟨by simp, by simp⟩, rfl⟩
  · exact ⟨_, -I, ⟨by simp, by simp⟩, rfl⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩
    exact hnotL z hz.1 (by have := hz.2; intro h; simp [h] at this)
  · rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩
    exact hnotL z hz.1 (by have := hz.2; intro h; simp [h] at this)
  · rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', he⟩
    have := hΦi hz'.1 hz.1 he
    rw [this] at hz'
    have h1 := hz.2
    have h2 := hz'.2
    linarith
  · rw [hDb]
    exact (hin 1).resolve_right one_ne_zero
  · rw [hDb]
    exact (hin (-1)).resolve_right (by norm_num)


end GraphMinor.HP25
