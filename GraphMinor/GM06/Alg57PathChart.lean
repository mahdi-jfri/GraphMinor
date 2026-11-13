module

public import GraphMinor.GM06.Alg57EdgeCharts

/-!
# Charts along a path

For `k = 1` of (5.7) we follow the left side of the linkage path `P₁` through polar charts at
its points. `P₁` may pass through vertices, so we cannot use the edge charts of
`exists_edge_chart` alone. Here we read off how a path runs through any polar chart at one of its
points.

Let `X` be a nice set (a union of atoms) that contains an arc `f` near `f t₀`, and suppose that
near `f t₀` the set `X` is just this arc. Each ray of the chart whose rim point is in `X` lies in
`X`, and so it lies in the part of the arc before `t₀` or in the part after `t₀`
(`chartRay_subset_piece`). Two rays in the same part are equal (`eq_of_chartRay_subset_arc`). The
arc runs out along the ray in the part after `t₀` (`exists_runsOut_piece`) and in along the ray
in the part before `t₀`. So the directions of `X` are exactly two (`exists_path_dirs`), or one at an
end of the arc (`exists_path_dirs_start`, `exists_path_dirs_end`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The ray of a chart in direction `w`, without its centre. -/
noncomputable def chartRay (Ψ : C(ClosedUnitDisc, EuclideanPlane)) (w : Circle) :
    Set (OnePoint EuclideanPlane) :=
  (fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * w))) '' Ioc 0 1

section PathChart

variable {Γ : Drawing (OnePoint EuclideanPlane)} {X : Set (OnePoint EuclideanPlane)}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}
  {c : OnePoint EuclideanPlane}

theorem isPreconnected_chartRay (w : Circle) : IsPreconnected (chartRay Ψ w) :=
  isPreconnected_Ioc.image _
    ((continuous_toSph.comp (continuous_chartC.comp (by fun_prop))).continuousOn)

theorem chartRay_subset_range (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (w : Circle) :
    chartRay Ψ w ⊆ range Φ := by
  rintro _ ⟨r, -, rfl⟩
  change toSph (chartC Ψ ((r : ℂ) * (w : ℂ))) ∈ range Φ
  rw [toSph_chartC hΨ]
  exact mem_range_self _

/-- The ray misses the centre. -/
theorem chartRay_ne_centre (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {w : Circle} {y : OnePoint EuclideanPlane} (hy : y ∈ chartRay Ψ w) : y ≠ c := by
  obtain ⟨r, ⟨hr, hr1⟩, rfl⟩ := hy
  intro h
  rw [← toSph_chartC_zero hp hΨ] at h
  have := chartC_injOn hΨ hp.inj (by
    rw [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr.le]; exact hr1) (mem_closedBall_self zero_le_one)
    (toSph_injective h)
  simp [hr.ne'] at this

/-- A ray lies in a nice set when its rim point does. -/
theorem chartRay_subset_of_rim (hp : IsPolar Γ c Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hX : IsGammaNice Γ X) {w : Circle}
    (hw : polarRimMap Φ w ∈ X) : chartRay Ψ w ⊆ X := by
  rintro _ ⟨r, ⟨hr, hr1⟩, rfl⟩
  exact (chart_ray_mem_iff hp hΨ hX w hr hr1).mpr hw

/-- A ray meeting a nice set has its rim point there. -/
theorem rim_mem_of_chartRay (hp : IsPolar Γ c Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hX : IsGammaNice Γ X) {w : Circle}
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (h : toSph (chartC Ψ ((r : ℂ) * w)) ∈ X) :
    polarRimMap Φ w ∈ X :=
  (chart_ray_mem_iff hp hΨ hX w hr hr1).mp h

/-- **Two rays inside one arc from the centre are equal.** -/
theorem eq_of_chartRay_subset_arc (hp : IsPolar Γ c Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (g : C(I, OnePoint EuclideanPlane))
    (hg : IsArcMap g) (hg0 : g 0 = c) {w w' : Circle} (hw : chartRay Ψ w ⊆ range g)
    (hw' : chartRay Ψ w' ⊆ range g) : w = w' := by
  have hsub : ∀ z : Circle, chartRay Ψ z ⊆ range g → range (polarRayMap Φ z) ⊆ range g := by
    rintro z hz _ ⟨r, rfl⟩
    rcases eq_or_lt_of_le r.2.1 with hr | hr
    · have : r = 0 := Subtype.ext hr.symm
      rw [this, polarRayMap_zero, hp.centre, ← hg0]
      exact mem_range_self _
    · have := hz ⟨r, ⟨hr, r.2.2⟩, rfl⟩
      simp only at this
      rwa [toSph_chartC hΨ, discPt_mul] at this
  have hstart : ∀ z : Circle, polarRayMap Φ z 0 = g 0 := fun z => by
    rw [polarRayMap_zero, hp.centre, hg0]
  obtain ⟨r, s, hr, -, hrs⟩ := exists_positive_meeting_of_initial_subarcs g
    (polarRayMap Φ w) (polarRayMap Φ w') hg (isArcMap_polarRayMap hp.inj w)
    (isArcMap_polarRayMap hp.inj w') (hsub w hw) (hsub w' hw') (hstart w) (hstart w')
  exact polarDiscPoint_direction_eq hr (hp.inj hrs)

variable {f : ℝ → OnePoint EuclideanPlane} {t₀ : ℝ}

/-- **Each ray of the path lies on one side of `t₀`.** -/
theorem chartRay_subset_piece (hp : IsPolar Γ (f t₀) Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hX : IsGammaNice Γ X)
    (hf : Continuous f) {a b : ℝ} (ha : a ≤ t₀) (hb : t₀ ≤ b) (hinj : InjOn f (Icc a b))
    (hloc : range Φ ∩ X ⊆ f '' Icc a b) {w : Circle} (hw : polarRimMap Φ w ∈ X) :
    chartRay Ψ w ⊆ f '' Icc a t₀ ∨ chartRay Ψ w ⊆ f '' Icc t₀ b := by
  have hu : IsClosed (f '' Icc a t₀) := ((isCompact_Icc).image hf).isClosed
  have hv : IsClosed (f '' Icc t₀ b) := ((isCompact_Icc).image hf).isClosed
  have hcov : chartRay Ψ w ⊆ f '' Icc a t₀ ∪ f '' Icc t₀ b := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hloc ⟨chartRay_subset_range hΨ w hy,
      chartRay_subset_of_rim hp hΨ hX hw hy⟩
    rcases le_total s t₀ with h | h
    · exact Or.inl ⟨s, ⟨hs.1, h⟩, rfl⟩
    · exact Or.inr ⟨s, ⟨h, hs.2⟩, rfl⟩
  have hdis : chartRay Ψ w ∩ (f '' Icc a t₀ ∩ f '' Icc t₀ b) = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    rintro hy ⟨s, hs, rfl⟩ ⟨s', hs', hss'⟩
    have h := hinj ⟨hs'.1.trans' ha, hs'.2⟩ ⟨hs.1, hs.2.trans hb⟩ hss'
    have hst : s = t₀ := le_antisymm hs.2 (h ▸ hs'.1)
    rw [hst] at hy
    exact chartRay_ne_centre hp hΨ hy rfl
  exact isPreconnected_iff_subset_of_disjoint_closed.mp (isPreconnected_chartRay w) _ _ hu hv
    hcov hdis

/-- **The path runs out along the ray in the part after `t₀`.** -/
theorem exists_runsOut_piece (hp : IsPolar Γ (f t₀) Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hX : IsGammaNice Γ X)
    (hf : Continuous f) {a b : ℝ} (ha : a ≤ t₀) (hb : t₀ < b) (hinj : InjOn f (Icc a b))
    (hfX : f '' Icc a b ⊆ X) (hloc : range Φ ∩ X ⊆ f '' Icc a b) :
    ∃ W : Circle, polarRimMap Φ W ∈ X ∧ chartRay Ψ W ⊆ f '' Icc t₀ b ∧
      ∃ δ, RunsOut Ψ W f t₀ δ := by
  -- the arc after `t₀`
  let g : C(I, OnePoint EuclideanPlane) := ⟨fun s => f (t₀ + (b - t₀) * s), by fun_prop⟩
  have hbt : 0 < b - t₀ := by linarith
  have hg : IsArcMap g := ⟨g.continuous, fun s s' h => by
    have h' := hinj (x₁ := t₀ + (b - t₀) * s) ⟨by nlinarith [s.2.1], by nlinarith [s.2.2]⟩
      ⟨by nlinarith [s'.2.1], by nlinarith [s'.2.2]⟩ h
    exact Subtype.ext (by
      have := mul_left_cancel₀ hbt.ne' (by linarith : (b - t₀) * (s : ℝ) = (b - t₀) * s')
      exact this)⟩
  have hg0 : g 0 = f t₀ := by simp [g]
  have hvg : f '' Icc t₀ b ⊆ range g := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨(s - t₀) / (b - t₀), div_nonneg (by linarith [hs.1]) hbt.le,
      (div_le_one hbt).mpr (by linarith [hs.2])⟩, ?_⟩
    change f (t₀ + (b - t₀) * ((s - t₀) / (b - t₀))) = f s
    rw [mul_div_cancel₀ _ hbt.ne']; ring_nf
  -- times just after `t₀` stay in the chart
  obtain ⟨δ₀, hδ₀, hδ₀b, hδ₀G⟩ : ∃ δ₀, 0 < δ₀ ∧ δ₀ ≤ b - t₀ ∧
      ∀ t ∈ Icc t₀ (t₀ + δ₀), f t ∈ range Φ := by
    have hpre := (isOpen_interior.preimage hf).mem_nhds (show t₀ ∈ f ⁻¹' interior (range Φ)
      from hp.nhd)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨min (ε / 2) (b - t₀), lt_min (half_pos hε) hbt, min_le_right _ _, fun t ht => ?_⟩
    apply interior_subset
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_left (ε / 2) (b - t₀)]
  -- each point after `t₀` lies on a ray in the part after `t₀`
  have hdir : ∀ t ∈ Ioc t₀ (t₀ + δ₀), ∃ r : ℝ, ∃ w : Circle, 0 < r ∧ r ≤ 1 ∧
      f t = toSph (chartC Ψ ((r : ℂ) * w)) ∧ polarRimMap Φ w ∈ X ∧
      chartRay Ψ w ⊆ f '' Icc t₀ b := by
    intro t ht
    have htI : t ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hne : f t ≠ f t₀ := fun h =>
      ht.1.ne' (hinj htI ⟨ha, hb.le⟩ h)
    obtain ⟨r, w, hr, hr1, hft⟩ := chart_point_polar hp hΨ (hδ₀G t ⟨ht.1.le, ht.2⟩) hne
    have hwX : polarRimMap Φ w ∈ X :=
      rim_mem_of_chartRay hp hΨ hX hr hr1 (hft ▸ hfX ⟨t, htI, rfl⟩)
    refine ⟨r, w, hr, hr1, hft, hwX, ?_⟩
    rcases chartRay_subset_piece hp hΨ hX hf ha hb.le hinj hloc hwX with h | h
    · exfalso
      obtain ⟨s, hs, hst⟩ := h ⟨r, ⟨hr, hr1⟩, hft.symm⟩
      have := hinj ⟨hs.1, hs.2.trans hb.le⟩ htI hst
      linarith [hs.2, ht.1]
    · exact h
  obtain ⟨r₀, W, hr₀, hr₀1, hfW, hWX, hWv⟩ := hdir (t₀ + δ₀) ⟨by linarith, le_rfl⟩
  refine ⟨W, hWX, hWv, δ₀ / 2, ?_⟩
  apply runsOut_of_on_ray hΨ hf hδ₀ hp (hinj.mono (Icc_subset_Icc ha (by linarith)))
  intro t ht
  obtain ⟨r, w, hr, hr1, hft, -, hwv⟩ := hdir t ht
  have := eq_of_chartRay_subset_arc hp hΨ g hg hg0 (hwv.trans hvg) (hWv.trans hvg)
  exact ⟨r, hr, hr1, this ▸ hft⟩

/-- **The path runs in along the ray in the part before `t₀`.** -/
theorem exists_runsIn_piece (hp : IsPolar Γ (f t₀) Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hX : IsGammaNice Γ X)
    (hf : Continuous f) {a b : ℝ} (ha : a < t₀) (hb : t₀ ≤ b) (hinj : InjOn f (Icc a b))
    (hfX : f '' Icc a b ⊆ X) (hloc : range Φ ∩ X ⊆ f '' Icc a b) :
    ∃ W : Circle, polarRimMap Φ W ∈ X ∧ chartRay Ψ W ⊆ f '' Icc a t₀ ∧
      ∃ δ, RunsIn Ψ W f t₀ δ := by
  have himg : ∀ p q : ℝ, (fun t => f (-t)) '' Icc (-q) (-p) = f '' Icc p q := by
    intro p q
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp⟩
  have hp' : IsPolar Γ ((fun t => f (-t)) (-t₀)) Φ := by simpa using hp
  have hinj' : InjOn (fun t => f (-t)) (Icc (-b) (-a)) := by
    intro s hs s' hs' h
    have := hinj (x₁ := -s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      ⟨by linarith [hs'.2], by linarith [hs'.1]⟩ h
    linarith
  obtain ⟨W, hWX, hWu, δ, hrun⟩ := exists_runsOut_piece (f := fun t => f (-t)) (t₀ := -t₀) hp' hΨ hX
    (hf.comp continuous_neg)
    (by linarith : -b ≤ -t₀) (by linarith : -t₀ < -a) hinj' (by rw [himg]; exact hfX)
    (by rw [himg]; exact hloc)
  refine ⟨W, hWX, ?_, δ, hrun.runsIn⟩
  rw [← himg]
  exact hWu

/-- **The two directions of a path through a chart.** -/
theorem exists_path_dirs (hp : IsPolar Γ (f t₀) Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hX : IsGammaNice Γ X)
    (hf : Continuous f) {a b : ℝ} (ha : a < t₀) (hb : t₀ < b) (hinj : InjOn f (Icc a b))
    (hfX : f '' Icc a b ⊆ X) (hloc : range Φ ∩ X ⊆ f '' Icc a b) :
    ∃ F B : Circle, F ≠ B ∧ polarRimMap Φ F ∈ X ∧ polarRimMap Φ B ∈ X ∧
      (∃ δ, RunsOut Ψ F f t₀ δ) ∧ (∃ δ, RunsIn Ψ B f t₀ δ) ∧
      ∀ w, polarRimMap Φ w ∈ X → w = F ∨ w = B := by
  obtain ⟨F, hFX, hFv, hout⟩ := exists_runsOut_piece hp hΨ hX hf ha.le hb hinj hfX hloc
  obtain ⟨B, hBX, hBu, hin⟩ := exists_runsIn_piece hp hΨ hX hf ha hb.le hinj hfX hloc
  -- the arc before `t₀`, read from `t₀`
  have hbt : 0 < t₀ - a := by linarith
  let g : C(I, OnePoint EuclideanPlane) := ⟨fun s => f (t₀ - (t₀ - a) * s), by fun_prop⟩
  have hg : IsArcMap g := ⟨g.continuous, fun s s' h => by
    have h' := hinj (x₁ := t₀ - (t₀ - a) * s) ⟨by nlinarith [s.2.2], by nlinarith [s.2.1]⟩
      ⟨by nlinarith [s'.2.2], by nlinarith [s'.2.1]⟩ h
    exact Subtype.ext (by
      have := mul_left_cancel₀ hbt.ne' (by linarith : (t₀ - a) * (s : ℝ) = (t₀ - a) * s')
      exact this)⟩
  have hg0 : g 0 = f t₀ := by simp [g]
  have hug : f '' Icc a t₀ ⊆ range g := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨(t₀ - s) / (t₀ - a), div_nonneg (by linarith [hs.2]) hbt.le,
      (div_le_one hbt).mpr (by linarith [hs.1])⟩, ?_⟩
    change f (t₀ - (t₀ - a) * ((t₀ - s) / (t₀ - a))) = f s
    rw [mul_div_cancel₀ _ hbt.ne']; ring_nf
  -- the arc after `t₀`
  have hbt' : 0 < b - t₀ := by linarith
  let g' : C(I, OnePoint EuclideanPlane) := ⟨fun s => f (t₀ + (b - t₀) * s), by fun_prop⟩
  have hg' : IsArcMap g' := ⟨g'.continuous, fun s s' h => by
    have h' := hinj (x₁ := t₀ + (b - t₀) * s) ⟨by nlinarith [s.2.1], by nlinarith [s.2.2]⟩
      ⟨by nlinarith [s'.2.1], by nlinarith [s'.2.2]⟩ h
    exact Subtype.ext (by
      have := mul_left_cancel₀ hbt'.ne' (by linarith : (b - t₀) * (s : ℝ) = (b - t₀) * s')
      exact this)⟩
  have hg0' : g' 0 = f t₀ := by simp [g']
  have hvg : f '' Icc t₀ b ⊆ range g' := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨(s - t₀) / (b - t₀), div_nonneg (by linarith [hs.1]) hbt'.le,
      (div_le_one hbt').mpr (by linarith [hs.2])⟩, ?_⟩
    change f (t₀ + (b - t₀) * ((s - t₀) / (b - t₀))) = f s
    rw [mul_div_cancel₀ _ hbt'.ne']; ring_nf
  refine ⟨F, B, ?_, hFX, hBX, hout, hin, fun w hw => ?_⟩
  · rintro rfl
    have hy : toSph (chartC Ψ (((1 : ℝ) : ℂ) * F)) ∈ chartRay Ψ F :=
      ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩
    obtain ⟨s, hs, hsy⟩ := hFv hy
    obtain ⟨s', hs', hsy'⟩ := hBu hy
    have := hinj ⟨hs'.1, hs'.2.trans hb.le⟩ ⟨ha.le.trans hs.1, hs.2⟩ (hsy'.trans hsy.symm)
    have hst : s = t₀ := le_antisymm (this ▸ hs'.2) hs.1
    rw [hst] at hsy
    exact chartRay_ne_centre hp hΨ hy hsy.symm
  · rcases chartRay_subset_piece hp hΨ hX hf ha.le hb.le hinj hloc hw with h | h
    · exact Or.inr (eq_of_chartRay_subset_arc hp hΨ g hg hg0 (h.trans hug) (hBu.trans hug))
    · exact Or.inl (eq_of_chartRay_subset_arc hp hΨ g' hg' hg0' (h.trans hvg) (hFv.trans hvg))

/-- **The direction of a path from its start.** -/
theorem exists_path_dirs_start (hp : IsPolar Γ (f t₀) Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hX : IsGammaNice Γ X)
    (hf : Continuous f) {b : ℝ} (hb : t₀ < b) (hinj : InjOn f (Icc t₀ b))
    (hfX : f '' Icc t₀ b ⊆ X) (hloc : range Φ ∩ X ⊆ f '' Icc t₀ b) :
    ∃ F : Circle, polarRimMap Φ F ∈ X ∧ (∃ δ, RunsOut Ψ F f t₀ δ) ∧
      ∀ w, polarRimMap Φ w ∈ X → w = F := by
  obtain ⟨F, hFX, hFv, hout⟩ := exists_runsOut_piece hp hΨ hX hf le_rfl hb hinj hfX hloc
  have hbt' : 0 < b - t₀ := by linarith
  let g' : C(I, OnePoint EuclideanPlane) := ⟨fun s => f (t₀ + (b - t₀) * s), by fun_prop⟩
  have hg' : IsArcMap g' := ⟨g'.continuous, fun s s' h => by
    have h' := hinj (x₁ := t₀ + (b - t₀) * s) ⟨by nlinarith [s.2.1], by nlinarith [s.2.2]⟩
      ⟨by nlinarith [s'.2.1], by nlinarith [s'.2.2]⟩ h
    exact Subtype.ext (by
      have := mul_left_cancel₀ hbt'.ne' (by linarith : (b - t₀) * (s : ℝ) = (b - t₀) * s')
      exact this)⟩
  have hg0' : g' 0 = f t₀ := by simp [g']
  have hvg : f '' Icc t₀ b ⊆ range g' := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨(s - t₀) / (b - t₀), div_nonneg (by linarith [hs.1]) hbt'.le,
      (div_le_one hbt').mpr (by linarith [hs.2])⟩, ?_⟩
    change f (t₀ + (b - t₀) * ((s - t₀) / (b - t₀))) = f s
    rw [mul_div_cancel₀ _ hbt'.ne']; ring_nf
  refine ⟨F, hFX, hout, fun w hw => ?_⟩
  rcases chartRay_subset_piece hp hΨ hX hf le_rfl hb.le hinj hloc hw with h | h
  · exfalso
    have hy : toSph (chartC Ψ (((1 : ℝ) : ℂ) * w)) ∈ chartRay Ψ w := ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩
    obtain ⟨s, hs, hsy⟩ := h hy
    have hst : s = t₀ := le_antisymm hs.2 hs.1
    rw [hst] at hsy
    exact chartRay_ne_centre hp hΨ hy hsy.symm
  · exact eq_of_chartRay_subset_arc hp hΨ g' hg' hg0' (h.trans hvg) (hFv.trans hvg)

/-- **The direction of a path into its end.** -/
theorem exists_path_dirs_end (hp : IsPolar Γ (f t₀) Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hX : IsGammaNice Γ X)
    (hf : Continuous f) {a : ℝ} (ha : a < t₀) (hinj : InjOn f (Icc a t₀))
    (hfX : f '' Icc a t₀ ⊆ X) (hloc : range Φ ∩ X ⊆ f '' Icc a t₀) :
    ∃ B : Circle, polarRimMap Φ B ∈ X ∧ (∃ δ, RunsIn Ψ B f t₀ δ) ∧
      ∀ w, polarRimMap Φ w ∈ X → w = B := by
  obtain ⟨B, hBX, hBu, hin⟩ := exists_runsIn_piece hp hΨ hX hf ha le_rfl hinj hfX hloc
  have hbt : 0 < t₀ - a := by linarith
  let g : C(I, OnePoint EuclideanPlane) := ⟨fun s => f (t₀ - (t₀ - a) * s), by fun_prop⟩
  have hg : IsArcMap g := ⟨g.continuous, fun s s' h => by
    have h' := hinj (x₁ := t₀ - (t₀ - a) * s) ⟨by nlinarith [s.2.2], by nlinarith [s.2.1]⟩
      ⟨by nlinarith [s'.2.2], by nlinarith [s'.2.1]⟩ h
    exact Subtype.ext (by
      have := mul_left_cancel₀ hbt.ne' (by linarith : (t₀ - a) * (s : ℝ) = (t₀ - a) * s')
      exact this)⟩
  have hg0 : g 0 = f t₀ := by simp [g]
  have hug : f '' Icc a t₀ ⊆ range g := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨(t₀ - s) / (t₀ - a), div_nonneg (by linarith [hs.2]) hbt.le,
      (div_le_one hbt).mpr (by linarith [hs.1])⟩, ?_⟩
    change f (t₀ - (t₀ - a) * ((t₀ - s) / (t₀ - a))) = f s
    rw [mul_div_cancel₀ _ hbt.ne']; ring_nf
  refine ⟨B, hBX, hin, fun w hw => ?_⟩
  rcases chartRay_subset_piece hp hΨ hX hf ha.le le_rfl hinj hloc hw with h | h
  · exact eq_of_chartRay_subset_arc hp hΨ g hg hg0 (h.trans hug) (hBu.trans hug)
  · exfalso
    have hy : toSph (chartC Ψ (((1 : ℝ) : ℂ) * w)) ∈ chartRay Ψ w := ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩
    obtain ⟨s, hs, hsy⟩ := h hy
    have hst : s = t₀ := le_antisymm hs.2 hs.1
    rw [hst] at hsy
    exact chartRay_ne_centre hp hΨ hy hsy.symm

end PathChart

end GraphMinor.GM06
